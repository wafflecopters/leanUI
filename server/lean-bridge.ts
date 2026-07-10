/**
 * Lean bridge — runs the user's source through real Lean 4 and returns
 * structured diagnostics.
 *
 * Milestone 1 ("proof of life"): we shell out to `lean --json` on a temp file.
 * Lean emits one JSON object per message on stdout, e.g.:
 *
 *   {"severity":"error","pos":{"line":3,"column":17},
 *    "endPos":{"line":3,"column":28},"data":"Type mismatch ..."}
 *
 * Lines are 1-based, columns 0-based (we keep them as Lean reports them; the
 * frontend maps to Monaco's 1-based columns).
 *
 * Mathlib mode (opt-in) runs `lake env lean --json <file>` with the bundled
 * Lean package (`/lean`) as cwd so Mathlib is on the import path. That path
 * requires the package to have been built with `-K mathlib=on` first.
 */
import { execFile } from 'node:child_process';
import { existsSync } from 'node:fs';
import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir, homedir } from 'node:os';
import { join, resolve } from 'node:path';

export type LeanSeverity = 'error' | 'warning' | 'information' | 'hint';

export interface LeanMessage {
  severity: LeanSeverity;
  /** 1-based line (as Lean reports). */
  startLine: number;
  /** 0-based column (as Lean reports). */
  startCol: number;
  endLine: number;
  endCol: number;
  text: string;
}

export interface CheckOptions {
  mathlib?: boolean;
  /** Hard timeout in ms (default 30s). */
  timeoutMs?: number;
  /** Jump the analyze queue (goal/display refreshes) ahead of background work
   *  (suggestion trials), so the visible goal state never starves. */
  priority?: boolean;
}

export interface CheckResult {
  success: boolean;
  messages: LeanMessage[];
  /** Lean/Lake version string, for the UI to display. */
  toolchain?: string;
  /** Set when the bridge itself failed (e.g. `lean` not found), distinct from a Lean error. */
  bridgeError?: string;
  /** Wall-clock duration of the Lean invocation, ms. */
  durationMs: number;
}

const ELAN_BIN = join(homedir(), '.elan', 'bin');
const LEAN_PKG_DIR = resolve(process.cwd(), 'lean');
const EXTRACT_LEAN = join(LEAN_PKG_DIR, 'Extract.lean');
// Precompiled extractor (built via `cd lean && lake build extract`, which the
// dev script runs). With `supportInterpreter := true` it elaborates user files
// correctly AND skips recompiling Extract.lean each call — ~1.7s vs ~32s. The
// bridge prefers it when present (core mode), else falls back to `lean --run`.
const EXTRACT_BIN = join(LEAN_PKG_DIR, '.lake', 'build', 'bin', 'extract');
let extractBinExists: boolean | undefined;
function hasExtractBin(): boolean {
  // Memoize only the POSITIVE result: if the binary doesn't exist yet (built
  // after the server started), keep re-checking so a long-lived server picks
  // it up instead of being stuck on the ~20x slower `lean --run` path forever.
  if (extractBinExists !== true) {
    try {
      extractBinExists = existsSync(EXTRACT_BIN);
    } catch {
      extractBinExists = false;
    }
  }
  return extractBinExists === true;
}

/** PATH with elan's shim dir prepended so `lean`/`lake` resolve. */
function leanEnv(): NodeJS.ProcessEnv {
  const path = `${ELAN_BIN}:${process.env.PATH ?? ''}`;
  return { ...process.env, PATH: path };
}

interface ExecOut {
  stdout: string;
  stderr: string;
  error?: NodeJS.ErrnoException;
}

function run(cmd: string, args: string[], opts: { cwd?: string; timeoutMs: number }): Promise<ExecOut> {
  return new Promise((resolveExec) => {
    execFile(
      cmd,
      args,
      { cwd: opts.cwd, env: leanEnv(), timeout: opts.timeoutMs, maxBuffer: 32 * 1024 * 1024 },
      (error, stdout, stderr) => {
        // Non-zero exit (Lean found errors) is expected — we still want stdout.
        resolveExec({ stdout: stdout ?? '', stderr: stderr ?? '', error: error ?? undefined });
      },
    );
  });
}

const SEVERITIES: ReadonlySet<string> = new Set(['error', 'warning', 'information', 'hint']);

/** Parse Lean's newline-delimited JSON message stream into LeanMessage[]. */
export function parseLeanJson(stdout: string): LeanMessage[] {
  const messages: LeanMessage[] = [];
  for (const line of stdout.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    let obj: any;
    try {
      obj = JSON.parse(trimmed);
    } catch {
      continue; // non-JSON noise — skip
    }
    if (!obj || typeof obj !== 'object' || !obj.pos) continue;
    const severity: LeanSeverity = SEVERITIES.has(obj.severity) ? obj.severity : 'information';
    const startLine = obj.pos.line ?? 1;
    const startCol = obj.pos.column ?? 0;
    const endLine = obj.endPos?.line ?? startLine;
    const endCol = obj.endPos?.column ?? startCol;
    messages.push({
      severity,
      startLine,
      startCol,
      endLine,
      endCol,
      text: typeof obj.data === 'string' ? obj.data : String(obj.data ?? ''),
    });
  }
  return messages;
}

export async function checkLeanSource(source: string, opts: CheckOptions = {}): Promise<CheckResult> {
  const timeoutMs = opts.timeoutMs ?? 30_000;
  const started = Date.now();
  let dir: string | undefined;
  try {
    dir = await mkdtemp(join(tmpdir(), 'leanui-check-'));
    const file = join(dir, 'Main.lean');
    await writeFile(file, source, 'utf8');

    const out = opts.mathlib
      ? await run('lake', ['env', 'lean', '--json', file], { cwd: LEAN_PKG_DIR, timeoutMs })
      : await run('lean', ['--json', file], { timeoutMs });

    // Spawn-level failures (binary missing, timeout) — surface as bridgeError.
    if (out.error && (out.error.code === 'ENOENT' || (out.error as any).killed)) {
      const reason =
        out.error.code === 'ENOENT'
          ? `Could not find \`${opts.mathlib ? 'lake' : 'lean'}\`. Is elan installed and on PATH (${ELAN_BIN})?`
          : `Lean timed out after ${timeoutMs}ms.`;
      return { success: false, messages: [], bridgeError: reason, durationMs: Date.now() - started };
    }

    const messages = parseLeanJson(out.stdout);
    const success = !messages.some((m) => m.severity === 'error');
    return { success, messages, durationMs: Date.now() - started };
  } catch (e) {
    return {
      success: false,
      messages: [],
      bridgeError: e instanceof Error ? e.message : String(e),
      durationMs: Date.now() - started,
    };
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// Analyze: messages + tactic goal states (via lean/Extract.lean InfoTree walk)
// ---------------------------------------------------------------------------

/**
 * Tagged pretty-printed expression (Lean `CodeWithInfos`), as serialized by
 * lean/Extract.lean. Mirrors `TaggedText SubexprInfo`: text leaves, append
 * nodes, and `tag` nodes carrying a subexpression position. Passed through
 * verbatim; the client's codeWithInfosToMathRow turns it into a MathRow.
 */
export type TaggedText =
  | { t: 'text'; s: string }
  | { t: 'append'; kids: TaggedText[] }
  | { t: 'tag'; pos: string; child: TaggedText };

/** One hypothesis in a goal state (names share a type, e.g. `a b : Nat`). */
export interface LeanHyp {
  names: string[];
  /** Tagged pretty-print of the hypothesis type, for WYSIWYG rendering. */
  type: TaggedText;
}

/** A single open goal: optional case name, hypotheses, and a target. */
export interface LeanGoalState {
  /** `case foo` name, if any. */
  case?: string;
  hyps: LeanHyp[];
  /** Tagged pretty-print of the target type (the thing after ⊢). */
  targetTagged: TaggedText;
  /** Plain-text rendering (fallback / copy), e.g. "n : Nat\n⊢ n + 0 = n". */
  plain: string;
}

export interface LeanGoal {
  /** 1-based line, 0-based col — source range of the tactic this goal precedes. */
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  /** The open goal states at this tactic position. */
  goals: LeanGoalState[];
}

/** A top-level declaration the user wrote (def/theorem/inductive/...). */
export interface LeanDeclaration {
  name: string;
  kind: 'def' | 'theorem' | 'inductive' | 'axiom' | 'opaque';
  prettyType: string;
  /** Tagged pretty-print of the type, for the WYSIWYG math editor. */
  typeTagged?: TaggedText;
  /** Present for plain `def`s only. */
  prettyValue?: string;
  /** Tagged pretty-print of the value (defs only). */
  valueTagged?: TaggedText;
  /** 1-based line, 0-based column of the declaration's start. */
  line: number;
  col: number;
}

/** Shallow structural validation of a tagged-text tree (defensive; bounded depth). */
function sanitizeTagged(x: any, depth = 0): TaggedText | undefined {
  if (!x || typeof x !== 'object' || depth > 200) return undefined;
  if (x.t === 'text') return { t: 'text', s: String(x.s ?? '') };
  if (x.t === 'append' && Array.isArray(x.kids)) {
    return { t: 'append', kids: x.kids.map((k: any) => sanitizeTagged(k, depth + 1)).filter(Boolean) };
  }
  if (x.t === 'tag') {
    const child = sanitizeTagged(x.child, depth + 1);
    if (!child) return undefined;
    return { t: 'tag', pos: String(x.pos ?? ''), child };
  }
  return undefined;
}

export interface AnalyzeResult {
  success: boolean;
  messages: LeanMessage[];
  goals: LeanGoal[];
  declarations: LeanDeclaration[];
  bridgeError?: string;
  durationMs: number;
}

function clampInt(n: unknown, fallback = 0): number {
  return typeof n === 'number' && Number.isFinite(n) ? n : fallback;
}

const DECL_KINDS: ReadonlySet<string> = new Set(['def', 'theorem', 'inductive', 'axiom', 'opaque']);

/** Parse the extractor's single-object JSON output. */
export function parseAnalyzeJson(
  stdout: string,
): { messages: LeanMessage[]; goals: LeanGoal[]; declarations: LeanDeclaration[] } | null {
  const trimmed = stdout.trim();
  if (!trimmed) return null;
  // The extractor prints exactly one JSON object (take the last non-empty line).
  const lastLine = trimmed.split('\n').filter((l) => l.trim()).pop() ?? trimmed;
  let obj: any;
  try {
    obj = JSON.parse(lastLine);
  } catch {
    return null;
  }
  if (!obj || typeof obj !== 'object' || !Array.isArray(obj.messages) || !Array.isArray(obj.goals)) {
    return null;
  }
  const messages: LeanMessage[] = obj.messages.map((m: any) => ({
    severity: SEVERITIES.has(m.severity) ? m.severity : 'information',
    startLine: clampInt(m.startLine, 1),
    startCol: clampInt(m.startCol),
    endLine: clampInt(m.endLine, clampInt(m.startLine, 1)),
    endCol: clampInt(m.endCol, clampInt(m.startCol)),
    text: typeof m.text === 'string' ? m.text : String(m.text ?? ''),
  }));
  const parseGoalState = (gs: any): LeanGoalState => {
    const target = sanitizeTagged(gs?.targetTagged) ?? { t: 'text', s: String(gs?.plain ?? '') };
    const hyps: LeanHyp[] = Array.isArray(gs?.hyps)
      ? gs.hyps
          .map((h: any) => {
            const type = sanitizeTagged(h?.type);
            if (!type) return undefined;
            return { names: Array.isArray(h?.names) ? h.names.map((n: any) => String(n)) : [], type };
          })
          .filter(Boolean)
      : [];
    return {
      ...(typeof gs?.case === 'string' ? { case: gs.case } : {}),
      hyps,
      targetTagged: target,
      plain: String(gs?.plain ?? ''),
    };
  };
  const goals: LeanGoal[] = obj.goals.map((g: any) => ({
    startLine: clampInt(g.startLine, 1),
    startCol: clampInt(g.startCol),
    endLine: clampInt(g.endLine, clampInt(g.startLine, 1)),
    endCol: clampInt(g.endCol, clampInt(g.startCol)),
    goals: Array.isArray(g.goals) ? g.goals.map(parseGoalState) : [],
  }));
  const declarations: LeanDeclaration[] = Array.isArray(obj.declarations)
    ? obj.declarations.map((d: any) => {
        const typeTagged = sanitizeTagged(d.typeTagged);
        const valueTagged = sanitizeTagged(d.valueTagged);
        return {
          name: String(d.name ?? ''),
          kind: DECL_KINDS.has(d.kind) ? d.kind : 'def',
          prettyType: String(d.prettyType ?? ''),
          ...(typeTagged ? { typeTagged } : {}),
          ...(typeof d.prettyValue === 'string' ? { prettyValue: d.prettyValue } : {}),
          ...(valueTagged ? { valueTagged } : {}),
          line: clampInt(d.line, 1),
          col: clampInt(d.col),
        };
      })
    : [];
  return { messages, goals, declarations };
}

// Same-source cache. The editor's debounce re-sends identical source often (and
// suggestion discovery re-analyzes near-identical sources), so memoizing by
// source+mathlib turns repeat analyses into instant hits. Bounded FIFO.
const ANALYZE_CACHE = new Map<string, AnalyzeResult>();
const ANALYZE_CACHE_MAX = 200;

function cacheKey(source: string, mathlib: boolean): string {
  return `${mathlib ? 'M' : 'C'}:${source}`;
}

/**
 * Priority-aware concurrency limiter for analyze runs. Unbounded parallel Lean
 * processes thrash the CPU (every run slows down, queues build, and the visible
 * goal state lags minutes behind); a small cap keeps each run near its solo
 * speed. Priority acquirers (goal/display refreshes) jump ahead of queued
 * background work (suggestion trials) so the UI never starves.
 */
export interface AnalyzeLimiter {
  acquire(priority: boolean): Promise<void>;
  release(): void;
}

export function createAnalyzeLimiter(maxConcurrent: number): AnalyzeLimiter {
  let running = 0;
  const waiting: Array<{ priority: boolean; start: () => void }> = [];
  return {
    acquire(priority: boolean): Promise<void> {
      if (running < maxConcurrent) {
        running++;
        return Promise.resolve();
      }
      return new Promise((start) => {
        const entry = { priority, start };
        if (priority) {
          // Ahead of all non-priority waiters, behind earlier priority ones.
          const i = waiting.findIndex((w) => !w.priority);
          if (i === -1) waiting.push(entry);
          else waiting.splice(i, 0, entry);
        } else {
          waiting.push(entry);
        }
      });
    },
    release(): void {
      const next = waiting.shift();
      if (next) next.start(); // the running slot transfers to the next waiter
      else running = Math.max(0, running - 1);
    },
  };
}

const analyzeLimiter = createAnalyzeLimiter(2);

export async function analyzeLeanSource(source: string, opts: CheckOptions = {}): Promise<AnalyzeResult> {
  const key = cacheKey(source, opts.mathlib === true);
  const hit = ANALYZE_CACHE.get(key);
  if (hit && !hit.bridgeError) {
    return { ...hit, durationMs: 0 };
  }
  await analyzeLimiter.acquire(opts.priority === true);
  let result: AnalyzeResult;
  try {
    // Re-check the cache: an identical request may have completed while queued.
    const hit2 = ANALYZE_CACHE.get(key);
    if (hit2 && !hit2.bridgeError) return { ...hit2, durationMs: 0 };
    result = await runAnalyze(source, opts);
  } finally {
    analyzeLimiter.release();
  }
  if (!result.bridgeError) {
    ANALYZE_CACHE.set(key, result);
    if (ANALYZE_CACHE.size > ANALYZE_CACHE_MAX) {
      const oldest = ANALYZE_CACHE.keys().next().value;
      if (oldest !== undefined) ANALYZE_CACHE.delete(oldest);
    }
  }
  return result;
}

async function runAnalyze(source: string, opts: CheckOptions = {}): Promise<AnalyzeResult> {
  const timeoutMs = opts.timeoutMs ?? 60_000;
  const started = Date.now();
  let dir: string | undefined;
  try {
    dir = await mkdtemp(join(tmpdir(), 'leanui-analyze-'));
    const file = join(dir, 'Main.lean');
    await writeFile(file, source, 'utf8');

    // Mathlib mode runs under `lake env` (interpreted) for the import path.
    // Core mode prefers the precompiled binary (supportInterpreter=true, so it
    // elaborates correctly), falling back to `lean --run` if not yet built.
    let out: ExecOut;
    let cmdName: string;
    if (opts.mathlib) {
      cmdName = 'lake';
      out = await run('lake', ['env', 'lean', '--run', EXTRACT_LEAN, file, 'mathlib'], { cwd: LEAN_PKG_DIR, timeoutMs });
    } else if (hasExtractBin()) {
      cmdName = 'extract';
      out = await run(EXTRACT_BIN, [file], { timeoutMs });
    } else {
      cmdName = 'lean';
      out = await run('lean', ['--run', EXTRACT_LEAN, file], { timeoutMs });
    }

    if (out.error && (out.error.code === 'ENOENT' || (out.error as any).killed)) {
      const reason =
        out.error.code === 'ENOENT'
          ? `Could not find \`${cmdName}\`. Is elan installed and on PATH (${ELAN_BIN})?`
          : `Lean timed out after ${timeoutMs}ms.`;
      return {
        success: false,
        messages: [],
        goals: [],
        declarations: [],
        bridgeError: reason,
        durationMs: Date.now() - started,
      };
    }

    const parsed = parseAnalyzeJson(out.stdout);
    if (!parsed) {
      const detail = (out.stderr || out.stdout || '').trim().slice(0, 2000);
      return {
        success: false,
        messages: [],
        goals: [],
        declarations: [],
        bridgeError: `Lean extractor produced no output.${detail ? `\n${detail}` : ''}`,
        durationMs: Date.now() - started,
      };
    }

    const success = !parsed.messages.some((m) => m.severity === 'error');
    return {
      success,
      messages: parsed.messages,
      goals: parsed.goals,
      declarations: parsed.declarations,
      durationMs: Date.now() - started,
    };
  } catch (e) {
    return {
      success: false,
      messages: [],
      goals: [],
      declarations: [],
      bridgeError: e instanceof Error ? e.message : String(e),
      durationMs: Date.now() - started,
    };
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}
