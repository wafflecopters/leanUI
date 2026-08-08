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
 * Mathlib mode (opt-in, `-K mathlib=on`) is NOT a separate execution path: it
 * asks `lake env` once for the environment Mathlib needs and then runs through
 * the same precompiled extractor, resident workers and prefix-olean cache as
 * core mode. Only when Mathlib isn't built does anything fall back to
 * interpreting under `lake env`, and then mainly to produce a real error.
 */
import {
  execFile,
  spawn,
  type ChildProcessWithoutNullStreams,
  type ExecFileException,
} from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync } from 'node:fs';
import { mkdtemp, writeFile, rm, mkdir, copyFile } from 'node:fs/promises';
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

// ── Mathlib environment ──────────────────────────────────────────────────────
// Mathlib mode used to mean "shell out to `lake env lean`", which re-elaborated
// the whole file per request and locked Mathlib out of every fast path. It
// doesn't have to: `lake env` is just a set of environment variables. Ask for
// them ONCE, then hand them to the same precompiled extractor and the same
// resident workers core mode uses — so Mathlib gets the olean cache and the
// ~20ms warm requests too, instead of paying tens of seconds per round-trip.
//
// LEAN_PATH is the important one, but NOT the only one: a dependency built with
// `precompileModules` (ProofWidgets, in Mathlib's tree) is loaded as a native
// shared library at elaboration time, found via the platform's library path.
// Capturing LEAN_PATH alone would work until it suddenly didn't, with an error
// about a missing symbol rather than a missing import — so take the whole set
// `lake env` actually sets.
// Deliberately NOT PATH: elan's shim dir has to win so `lean` resolves to the
// toolchain the extract binary was built with (see `extractEnv`).
const LAKE_ENV_KEYS = [
  'LEAN_PATH',
  'LEAN_SRC_PATH',
  'DYLD_LIBRARY_PATH', // macOS
  'LD_LIBRARY_PATH', // Linux
] as const;

let MATHLIB_ENV_PROMISE: Promise<Record<string, string> | null> | undefined;
/** The resolved overlay, once known. Read synchronously by `extractEnv`. */
let MATHLIB_ENV: Record<string, string> | null = null;

/**
 * The environment `lake env` would set for a Mathlib build, or null when
 * Mathlib isn't fetched/built.
 *
 * Memoized on the PROMISE so concurrent first-requests share one `lake` call.
 * A null result is remembered too: with Mathlib absent, re-asking on every
 * request would add a doomed subprocess to each one.
 */
function mathlibEnv(): Promise<Record<string, string> | null> {
  if (!MATHLIB_ENV_PROMISE) {
    MATHLIB_ENV_PROMISE = (async () => {
      try {
        // `-R` forces re-elaboration of the lakefile: the `require mathlib` sits
        // behind `meta if get_config? mathlib`, and Lake otherwise reuses a
        // cached lakefile olean elaborated WITHOUT the option — silently
        // resolving to a Mathlib-less workspace and reporting success.
        const out = await run('lake', ['-R', '-K', 'mathlib=on', 'env', 'printenv'], {
          cwd: LEAN_PKG_DIR,
          timeoutMs: 300_000,
        });
        if (out.error) return null;
        const env: Record<string, string> = {};
        for (const line of out.stdout.split('\n')) {
          const eq = line.indexOf('=');
          if (eq <= 0) continue;
          const key = line.slice(0, eq);
          if ((LAKE_ENV_KEYS as readonly string[]).includes(key)) env[key] = line.slice(eq + 1);
        }
        // Mathlib absent → LEAN_PATH won't mention it, and treating that as
        // "ready" would send requests down a fast path that can't resolve
        // `import Mathlib` and report it as a user error in their file.
        MATHLIB_ENV = /mathlib/i.test(env.LEAN_PATH ?? '') ? env : null;
        return MATHLIB_ENV;
      } catch {
        return null;
      }
    })();
  }
  return MATHLIB_ENV_PROMISE;
}

/**
 * The LEAN_PATH an extract run should use: the prefix-olean cache, plus Mathlib.
 *
 * MONOTONIC by design. Once Mathlib is known it goes on EVERY run, core ones
 * included — because the resident workers fix their environment at spawn, so a
 * path that varied per request would make a core warm-up and a Mathlib warm-up
 * respawn the pool out from under each other, indefinitely. A wider search path
 * costs a core request nothing: it imports no Mathlib module, so nothing is ever
 * found there.
 *
 * Only a request that actually asks for Mathlib pays to RESOLVE it, so a
 * core-only session never shells out to `lake` at all.
 */
async function searchPath(mathlib: boolean | undefined, prefixDir = PREFIX_CACHE_ROOT): Promise<string> {
  if (mathlib) await mathlibEnv();
  return MATHLIB_ENV ? `${prefixDir}:${MATHLIB_ENV.LEAN_PATH}` : prefixDir;
}

/** The full environment for an extract run — `searchPath` plus whatever else
 *  `lake env` sets (library paths for precompiled deps). Keyed for worker reuse
 *  by its LEAN_PATH, which is monotonic, so the rest follows deterministically. */
async function extractEnv(
  mathlib: boolean | undefined,
  prefixDir = PREFIX_CACHE_ROOT,
): Promise<NodeJS.ProcessEnv> {
  const LEAN_PATH = await searchPath(mathlib, prefixDir);
  // leanEnv() last for PATH: elan's shims must win so `lean` resolves to the
  // toolchain the extract binary was built with.
  return { ...process.env, ...(MATHLIB_ENV ?? {}), ...leanEnv(), LEAN_PATH };
}

interface ExecOut {
  stdout: string;
  stderr: string;
  /** `execFile`'s failure. Its `code` is `string | number | null` (a signal-kill
   *  reports a number), which is why this isn't `NodeJS.ErrnoException`. */
  error?: ExecFileException;
}

function run(
  cmd: string,
  args: string[],
  opts: { cwd?: string; timeoutMs: number; env?: NodeJS.ProcessEnv },
): Promise<ExecOut> {
  return new Promise((resolveExec) => {
    execFile(
      cmd,
      args,
      { cwd: opts.cwd, env: opts.env ?? leanEnv(), timeout: opts.timeoutMs, maxBuffer: 32 * 1024 * 1024 },
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

    // A Mathlib check is a fresh `lean` importing Mathlib (multi-GB while it
    // runs) — hold a Mathlib slot so concurrent checks queue instead of
    // stacking processes. Core checks are ~100MB and stay unthrottled.
    const out = opts.mathlib
      ? await withMathlibSlot(opts.priority === true, () =>
          run('lake', ['env', 'lean', '--json', file], { cwd: LEAN_PKG_DIR, timeoutMs }),
        )
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

/** What a hypothesis IS, from the elaborator rather than from its rendering. */
export interface LeanHypFact {
  name: string;
  typeHead: string | null;
  isFun: boolean;
  /** Constructors of the hypothesis's (unfolded) type — how many branches a
   *  `cases` on it opens. 0 when the type isn't an inductive. */
  ctors?: number;
  /** Every leaf name a one-line `obtain ⟨…⟩ := h` binds — one-constructor
   *  structures flattened all the way down. Empty when there is nothing to
   *  destructure. Names may repeat (two nested pairs both have a `fst`); the
   *  caller uniquifies. */
  flatFields?: string[];
  fields: string[];
}

/** A single open goal: optional case name, hypotheses, and a target. */
export interface LeanGoalState {
  /** `case foo` name, if any. */
  case?: string;
  hyps: LeanHyp[];
  /** Tagged pretty-print of the target type (the thing after ⊢). */
  targetTagged: TaggedText;
  /** Whether the target is a Prop (a claim to prove) as opposed to data (a
   *  value to choose). Absent from pre-`isProp` extractor builds. */
  isProp?: boolean;
  /** Head constant of the target, AS WRITTEN — `rlt` for `0 < x`. */
  targetHead?: string | null;
  /** Structural facts per hypothesis, from the elaborator. */
  hypFacts?: LeanHypFact[];
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
  /** Case tags of goals whose metavariable occurs in a sibling goal's type —
   *  values to CHOOSE (e.g. the `b` midpoint of `apply ltLeTrans`). Recorded
   *  by the extractor at the split itself, so it survives later assignment. */
  valueCaseTags?: string[];
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
  /** Head constant of the conclusion, AS WRITTEN — `rlt` for `a < b`. */
  conclHead?: string | null;
  /** Is that head an inductive type? */
  conclIsInductive?: boolean;
  /** Constructors of that inductive — branches a `cases` on this lemma's
   *  result opens (`leTotal a b` concludes an `Either`, so two). */
  conclCtors?: number;
  /** Head constant of each EXPLICIT argument's type, in order. */
  argHeads?: (string | null)[];
  /** Goals a backwards step leaves (explicit args the conclusion doesn't fix). */
  premises?: number;
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
    const hypFacts: LeanHypFact[] = Array.isArray(gs?.hypFacts)
      ? gs.hypFacts.map((h: any) => ({
          name: String(h?.name ?? ''),
          typeHead: typeof h?.typeHead === 'string' ? h.typeHead : null,
          isFun: h?.isFun === true,
          ...(typeof h?.ctors === 'number' ? { ctors: h.ctors } : {}),
          ...(Array.isArray(h?.flatFields) ? { flatFields: h.flatFields.map((x: any) => String(x)) } : {}),
          fields: Array.isArray(h?.fields) ? h.fields.map((x: any) => String(x)) : [],
        }))
      : [];
    return {
      ...(typeof gs?.case === 'string' ? { case: gs.case } : {}),
      hyps,
      ...(typeof gs?.targetHead === 'string' ? { targetHead: gs.targetHead } : {}),
      ...(hypFacts.length ? { hypFacts } : {}),
      targetTagged: target,
      ...(typeof gs?.isProp === 'boolean' ? { isProp: gs.isProp } : {}),
      plain: String(gs?.plain ?? ''),
    };
  };
  const goals: LeanGoal[] = obj.goals.map((g: any) => ({
    startLine: clampInt(g.startLine, 1),
    startCol: clampInt(g.startCol),
    endLine: clampInt(g.endLine, clampInt(g.startLine, 1)),
    endCol: clampInt(g.endCol, clampInt(g.startCol)),
    goals: Array.isArray(g.goals) ? g.goals.map(parseGoalState) : [],
    ...(Array.isArray(g.valueCaseTags) && g.valueCaseTags.length > 0
      ? { valueCaseTags: g.valueCaseTags.map((t: any) => String(t)) }
      : {}),
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
          ...(typeof d.conclHead === 'string' ? { conclHead: d.conclHead } : {}),
          ...(typeof d.conclIsInductive === 'boolean' ? { conclIsInductive: d.conclIsInductive } : {}),
          ...(typeof d.conclCtors === 'number' ? { conclCtors: d.conclCtors } : {}),
          ...(Array.isArray(d.argHeads)
            ? { argHeads: d.argHeads.map((h: any) => (typeof h === 'string' ? h : null)) }
            : {}),
          ...(typeof d.premises === 'number' ? { premises: d.premises } : {}),
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

// ── worker-pool sizing ──────────────────────────────────────────────────────
// Core and Mathlib requests run through SEPARATE pools, because a worker that
// has imported Mathlib holds 4–7GB resident and one shared pool meant every
// worker (and every busy-spill one-shot) eventually went Mathlib-sized —
// stacked across the dev server plus parallel test forks, that is the ~100GB
// blowup of 2026-07-28.
//
// CORE WORKERS ARE NOT CHEAP EITHER. This comment used to claim ~100–200MB;
// measured against the real-analysis preset with no Mathlib in the picture, the
// three core workers of an idle dev server sat at 4.4GB, 3.3GB and 2.7GB — over
// 10GB, doing nothing. The preset's own environment is what costs that, so the
// number scales with the FILE, and the default of 3 is a real memory decision
// rather than a free one. Tests override it to 1 (see vitest.config.ts).
//
// Each mode's limiter cap equals its pool size, so an acquired slot always
// finds a free worker — which is also what keeps the one-shot busy-fallback
// (another 4–7GB process per spill, in Mathlib mode) unreachable in normal
// operation: excess requests queue on the limiter instead of spawning.
/** Parse a pool-size env override; anything not an integer in [1, max] → fallback. */
export function clampPoolSize(raw: string | undefined, fallback: number, max: number): number {
  const n = Number(raw);
  return Number.isInteger(n) && n >= 1 && n <= max ? n : fallback;
}
const CORE_WORKER_COUNT = clampPoolSize(process.env.LEANUI_EXTRACT_WORKERS, 3, 8);
const MATHLIB_WORKER_COUNT = clampPoolSize(process.env.LEANUI_MATHLIB_WORKERS, 1, 4);

const analyzeLimiter = createAnalyzeLimiter(CORE_WORKER_COUNT);
const mathlibLimiter = createAnalyzeLimiter(MATHLIB_WORKER_COUNT);

/** Run `fn` holding a Mathlib concurrency slot — every code path that can make
 *  a process import Mathlib must go through here (or hold a slot already), so
 *  the number of Mathlib-resident processes stays bounded by the pool size. */
async function withMathlibSlot<T>(priority: boolean, fn: () => Promise<T>): Promise<T> {
  await mathlibLimiter.acquire(priority);
  try {
    return await fn();
  } finally {
    mathlibLimiter.release();
  }
}

// ── persistent extract workers (`extract --serve`) ──────────────────────────
// One-shot extract runs pay process boot + `importModules` on EVERY request —
// the reason goal updates felt slow next to the text editor, whose
// `lean --server` keeps the environment resident. `--serve` mode is our
// version of the same: a long-lived extract process with an env cache, one
// file path in per stdin line, one JSON out per stdout line. Warm requests
// run in ~20ms.

/**
 * How big a resident worker may get before it is recycled, in MB.
 *
 * A worker's environment cache is a CACHE WITH NO EVICTION: every distinct
 * prefix module it imports stays in memory for the life of the process, and a
 * real preset's environment is hundreds of MB to GBs each. An editing session
 * that touches many prefixes therefore grows its workers without bound — which
 * is how an ordinary afternoon of proving reached ~100GB across a pool of
 * three. Recycling on a REQUEST COUNT (the 400 below) does not bound that: the
 * cost per request depends on what was imported, not on how many requests.
 */
// 3GB each: with the default pool of 3 that is a ~9GB ceiling for the pool,
// versus the unbounded growth it replaces. Deliberately not lower — a worker
// recycled too eagerly re-imports the prefix on its next request, and the
// resident environment is the entire reason warm round-trips are ~20ms rather
// than seconds. Tune with LEANUI_WORKER_MAX_MB if that trade sits differently
// on your machine.
const MAX_WORKER_RSS_MB = clampPoolSize(process.env.LEANUI_WORKER_MAX_MB, 3072, 64_000);
/** How often to look (in requests) — `ps` is cheap next to an elaboration, but
 *  not free, and memory cannot grow much in ten requests. */
const RSS_CHECK_EVERY = 10;

/** Resident size of a live pid in KB, or null when it can't be read. */
function pidRssKb(pid: number): Promise<number | null> {
  return new Promise((resolve) => {
    execFile('ps', ['-o', 'rss=', '-p', String(pid)], { timeout: 5_000 }, (err, stdout) => {
      if (err) return resolve(null);
      const n = Number(stdout.trim());
      resolve(Number.isFinite(n) ? n : null);
    });
  });
}

class ExtractWorker {
  private child: ChildProcessWithoutNullStreams | null = null;
  private waiters: Array<(line: string | null) => void> = [];
  private buf = '';
  private served = 0;
  busy = false;

  /** The LEAN_PATH this worker's process was spawned with. A worker's search
   *  path is fixed for the life of the process, so a request needing a wider
   *  one (the first Mathlib request on a pool started for core) must respawn. */
  private spawnedPath: string | null = null;

  private ensure(leanPath: string): boolean {
    if (this.child && this.spawnedPath === leanPath) return true;
    if (this.child) {
      // Widening (or narrowing) the search path: recycle. Happens at most once
      // per pool in practice, since the resolved paths are stable.
      const old = this.child;
      this.child = null;
      for (const w of this.waiters.splice(0)) w(null);
      old.kill();
    }
    if (!hasExtractBin()) return false;
    try {
      this.spawnedPath = leanPath;
      this.child = spawn(EXTRACT_BIN, ['--serve'], {
        // Same overlay as `extractEnv`, built synchronously: the caller already
        // resolved Mathlib (via `searchPath`) to produce `leanPath`, so
        // MATHLIB_ENV is settled by the time we get here.
        env: { ...process.env, ...(MATHLIB_ENV ?? {}), ...leanEnv(), LEAN_PATH: leanPath },
        cwd: LEAN_PKG_DIR, // lean-toolchain pin for findSysroot
        stdio: ['pipe', 'pipe', 'pipe'],
      });
    } catch {
      this.child = null;
      return false;
    }
    this.buf = '';
    this.served = 0;
    this.child.stdout.on('data', (d: Buffer) => {
      this.buf += d.toString('utf8');
      let i;
      while ((i = this.buf.indexOf('\n')) >= 0) {
        const line = this.buf.slice(0, i);
        this.buf = this.buf.slice(i + 1);
        this.waiters.shift()?.(line);
      }
    });
    this.child.stderr.on('data', () => {}); // linter notes etc. — not part of the protocol
    const dead = () => {
      this.child = null;
      // Flush anyone waiting: their request died with the process.
      for (const w of this.waiters.splice(0)) w(null);
    };
    this.child.on('exit', dead);
    this.child.on('error', dead);
    return true;
  }

  /** Stop the worker process, if one is running. */
  stop(): void {
    const child = this.child;
    this.child = null;
    for (const w of this.waiters.splice(0)) w(null);
    child?.kill();
  }

  /** One request (serial per worker). Null → caller should fall back. */
  async request(path: string, timeoutMs: number, leanPath: string = PREFIX_CACHE_ROOT): Promise<string | null> {
    if (this.busy || !this.ensure(leanPath)) return null;
    this.busy = true;
    try {
      const reply = new Promise<string | null>((res) => this.waiters.push(res));
      this.child!.stdin.write(`${path}\n`);
      const timer = setTimeout(() => this.child?.kill(), timeoutMs); // kill → exit → waiters flushed null
      const line = await reply;
      clearTimeout(timer);
      // Recycle on SIZE first, then on count. The environment cache never
      // evicts, so the honest bound is "how much memory is this holding", not
      // "how many questions has it answered".
      this.served++;
      const pid = this.child?.pid;
      if (pid !== undefined && this.served % RSS_CHECK_EVERY === 0) {
        const rss = await pidRssKb(pid);
        if (rss !== null && rss > MAX_WORKER_RSS_MB * 1024) {
          console.warn(
            `[lean-bridge] recycling worker ${pid}: ${Math.round(rss / 1024)}MB > ${MAX_WORKER_RSS_MB}MB`,
          );
          this.child?.kill();
          this.child = null;
          return line;
        }
      }
      // Count backstop, for growth the size check somehow misses. 400 was far
      // too generous: a single goal refresh with a subterm selected fires on
      // the order of a HUNDRED trials (unfold alone is capped at 60), so 400
      // requests is a few refreshes — and by then a worker on a real preset is
      // many GB.
      if (this.served >= 150) {
        this.child?.kill();
        this.child = null;
      }
      return line;
    } finally {
      this.busy = false;
    }
  }
}

const CORE_WORKERS = Array.from({ length: CORE_WORKER_COUNT }, () => new ExtractWorker());
// Mathlib requests NEVER route to the core pool (and vice versa): the pools
// share a LEAN_PATH, but only processes that actually elaborate a Mathlib
// import pay its 4–7GB — so the split keeps that cost confined to this pool.
const MATHLIB_WORKERS = Array.from({ length: MATHLIB_WORKER_COUNT }, () => new ExtractWorker());

/**
 * Shut the persistent workers down.
 *
 * The long-lived `extract --serve` children are what make warm requests ~20ms,
 * but they also hold the Node event loop open forever. A server never cares; a
 * script or a test run does — without this, any headless caller hangs after its
 * last request instead of exiting.
 */
export function shutdownLeanBridge(): void {
  for (const w of CORE_WORKERS) w.stop();
  for (const w of MATHLIB_WORKERS) w.stop();
}

/** Run one analyze through a persistent worker of the mode's pool. Null →
 *  caller should fall back to one-shot (worker busy/unavailable, old binary
 *  without --serve, crash, timeout). */
async function requestViaWorker(
  file: string,
  timeoutMs: number,
  leanPath: string = PREFIX_CACHE_ROOT,
  mathlib = false,
): Promise<ReturnType<typeof parseAnalyzeJson> | null> {
  const pool = mathlib ? MATHLIB_WORKERS : CORE_WORKERS;
  const worker = pool.find((w) => !w.busy);
  if (!worker) return null;
  const line = await worker.request(file, timeoutMs, leanPath);
  if (line === null) return null;
  let obj: any;
  try {
    obj = JSON.parse(line);
  } catch {
    return null;
  }
  if (obj && typeof obj === 'object' && typeof obj.serveError === 'string') return null;
  return parseAnalyzeJson(line);
}

// ── prefix-olean cache ───────────────────────────────────────────────────────
// Proof-editor round-trips (goal refreshes, suggestion trials) all share the
// same file PREFIX — everything before the declaration being edited — and only
// vary in the decl's proof. Re-elaborating that unchanged prefix dominated
// every request (~2.5s for the Real-analysis preset). Instead we compile the
// prefix ONCE to a .olean module (hash-keyed) and analyze
// `import LeanuiP<hash>\n<body>` with LEAN_PATH pointing at the cache —
// ~0.2s per request. The cache dir carries the project's lean-toolchain pin so
// elan resolves the SAME toolchain the extract binary was built with
// (mismatched toolchains fail with "incompatible olean header").
//
// This works for Mathlib too, and matters far MORE there: `import Mathlib` is
// tens of seconds to elaborate, so paying it once per prefix — instead of once
// per goal refresh and once per suggestion trial — is the difference between a
// usable editor and an unusable one. All it takes is compiling the prefix with
// Mathlib on LEAN_PATH and importing it back the same way (see `searchPath`).
interface PrefixModule {
  ok: boolean;
  dir: string;
  modName: string;
  /** Number of lines in the prefix (for coordinate remapping). */
  lineCount: number;
}

const PREFIX_CACHE = new Map<string, Promise<PrefixModule>>();
const PREFIX_CACHE_MAX = 20;
const PREFIX_CACHE_ROOT = join(tmpdir(), 'leanui-prefix-cache');

function prefixHash(prefix: string): string {
  return createHash('sha256').update(prefix).digest('hex').slice(0, 16);
}

async function compilePrefixModule(prefix: string, mathlib?: boolean): Promise<PrefixModule> {
  const hash = prefixHash(prefix);
  const modName = `LeanuiP${hash}`;
  // FLAT layout: every prefix module lives directly in the cache root (names
  // are hash-unique), so ONE `LEAN_PATH=<root>` serves all of them — required
  // by the persistent --serve workers, whose search path is fixed at spawn.
  const dir = PREFIX_CACHE_ROOT;
  const lineCount = prefix.split('\n').length;
  const fail: PrefixModule = { ok: false, dir, modName, lineCount };
  try {
    await mkdir(dir, { recursive: true });
    const olean = join(dir, `${modName}.olean`);
    if (existsSync(olean)) return { ok: true, dir, modName, lineCount };
    await writeFile(join(dir, `${modName}.lean`), prefix, 'utf8');
    // Pin the toolchain: elan resolves `lean` per-cwd via lean-toolchain.
    await copyFile(join(LEAN_PKG_DIR, 'lean-toolchain'), join(dir, 'lean-toolchain'));
    // A Mathlib prefix (`import Mathlib…`) only compiles with Mathlib on the
    // search path — without this the module silently fails to build and every
    // Mathlib request falls back to the slow whole-file path.
    const env = await extractEnv(mathlib, dir);
    const out = await run('lean', ['-o', olean, `${modName}.lean`], {
      cwd: dir,
      // Compiling a prefix that imports Mathlib is minutes on a cold cache, not
      // seconds — and it happens once per distinct prefix.
      timeoutMs: mathlib ? 900_000 : 120_000,
      env,
    });
    // Errors in the prefix (user mid-edit above the decl) → no usable module.
    if (out.error || !existsSync(olean)) return fail;
    return { ok: true, dir, modName, lineCount };
  } catch {
    return fail;
  }
}

function getPrefixModule(prefix: string, mathlib?: boolean): Promise<PrefixModule> {
  // Keyed by mode as well as text: the same prefix compiles under Mathlib and
  // fails without it, and a cached `ok` from the other mode would send requests
  // down the fast path with a search path that can't resolve its imports.
  const hash = `${mathlib ? 'M' : 'C'}${prefixHash(prefix)}`;
  let entry = PREFIX_CACHE.get(hash);
  if (!entry) {
    entry = compilePrefixModule(prefix, mathlib).then((mod) => {
      // Pre-warm the persistent workers' env caches with the new module, so
      // the FIRST interactive request doesn't pay the ~0.7s import either.
      // (Mathlib makes this warm-up matter far more: importing it is tens of
      // seconds, and the whole point is that only the warm-up pays that.)
      if (mod.ok) void warmWorkersForPrefix(mod, mathlib);
      return mod;
    });
    PREFIX_CACHE.set(hash, entry);
    if (PREFIX_CACHE.size > PREFIX_CACHE_MAX) {
      const oldest = PREFIX_CACHE.keys().next().value;
      if (oldest !== undefined) PREFIX_CACHE.delete(oldest); // olean stays on disk; harmless
    }
  }
  return entry;
}

/** Fire-and-forget: run a trivial `import <prefix>` file through every worker
 *  of the mode's pool, so their env caches hold the module before real
 *  requests arrive. Each warm-up holds a NON-priority slot of the SAME
 *  limiter that guards the pool — never competing with real requests for a
 *  worker (the limiter cap equals the pool size, so a real slot-holder must
 *  always find a free worker). Warming only the matching pool is what keeps a
 *  Mathlib prefix from inflating every core worker to Mathlib size. */
async function warmWorkersForPrefix(mod: PrefixModule, mathlib?: boolean): Promise<void> {
  let dir: string | undefined;
  try {
    dir = await mkdtemp(join(tmpdir(), 'leanui-warm-'));
    const file = join(dir, 'Warm.lean');
    await writeFile(file, `import ${mod.modName}\n`, 'utf8');
    const leanPath = await searchPath(mathlib);
    const pool = mathlib ? MATHLIB_WORKERS : CORE_WORKERS;
    const limiter = mathlib ? mathlibLimiter : analyzeLimiter;
    await Promise.all(
      pool.map(async (w) => {
        await limiter.acquire(false);
        try {
          // Generous: a first Mathlib import is tens of seconds, and paying it
          // here is exactly the point.
          await w.request(file, mathlib ? 600_000 : 120_000, leanPath); // null if busy → warms on first real use
        } finally {
          limiter.release();
        }
      }),
    );
  } catch {
    // Warmup is best-effort; real requests just pay the import themselves.
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

/** Shift all line numbers in an analyze result by `delta` (coordinate remap
 *  from the `import`-header trial file back to the caller's full-source space). */
export function shiftAnalyzeLines(
  parsed: { messages: LeanMessage[]; goals: LeanGoal[]; declarations: LeanDeclaration[] },
  delta: number,
): { messages: LeanMessage[]; goals: LeanGoal[]; declarations: LeanDeclaration[] } {
  const line = (n: number) => Math.max(1, n + delta);
  return {
    messages: parsed.messages.map((m) => ({ ...m, startLine: line(m.startLine), endLine: line(m.endLine) })),
    goals: parsed.goals.map((g) => ({ ...g, startLine: line(g.startLine), endLine: line(g.endLine) })),
    declarations: parsed.declarations.map((d) => ({ ...d, line: line(d.line) })),
  };
}

/**
 * Turn an extractor crash into something the user can act on.
 *
 * A half-populated Mathlib build fails as `object file '…/Foo.olean' … does not
 * exist` — which reads like a corrupt install, not like "your download was
 * interrupted". It's an easy state to reach: `lake update` runs Mathlib's cache
 * fetch, and one file missing out of ~8500 is enough. (Hit exactly that while
 * building this.) The fix is a command, so say the command.
 */
function hintFor(detail: string): string {
  if (/object file .*\.olean.* does not exist/.test(detail)) {
    return '\nMathlib looks partially built. Run: cd lean && lake -R -K mathlib=on exe cache get && lake -R -K mathlib=on build';
  }
  return '';
}

export interface AnalyzeOptions extends CheckOptions {
  /** Unchanged file prefix (everything before the decl being edited). When
   *  given with `body`, the server compiles it once to a .olean and analyzes
   *  `import <prefix-module>\n<body>` instead — much faster. Coordinates in
   *  the result are in prefix+body (full-source) space. */
  prefix?: string;
  body?: string;
}

export async function analyzeLeanSource(source: string, opts: AnalyzeOptions = {}): Promise<AnalyzeResult> {
  const key = cacheKey(source, opts.mathlib === true);
  const hit = ANALYZE_CACHE.get(key);
  if (hit && !hit.bridgeError) {
    return { ...hit, durationMs: 0 };
  }
  // Mathlib analyzes hold a slot of the (much smaller) Mathlib limiter: only
  // that many processes can be elaborating a Mathlib import at any moment.
  const limiter = opts.mathlib ? mathlibLimiter : analyzeLimiter;
  await limiter.acquire(opts.priority === true);
  let result: AnalyzeResult;
  try {
    // Re-check the cache: an identical request may have completed while queued.
    const hit2 = ANALYZE_CACHE.get(key);
    if (hit2 && !hit2.bridgeError) return { ...hit2, durationMs: 0 };

    result = await runViaPrefix(opts) ?? await runAnalyze(source, opts);
  } finally {
    limiter.release();
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

/** Try the prefix-olean fast path; null → caller falls back to a full analyze. */
async function runViaPrefix(opts: AnalyzeOptions): Promise<AnalyzeResult | null> {
  const { prefix, body, mathlib } = opts;
  if (!prefix || body === undefined || !hasExtractBin()) return null;
  // Mathlib mode used to bail here, so every Mathlib round-trip re-elaborated
  // the whole file under `lake env`. It doesn't have to: `lake env`'s only
  // contribution is LEAN_PATH, and the prefix module can be compiled and
  // imported against that path like any other.
  if (mathlib && (await mathlibEnv()) === null) return null; // not built → slow path reports it
  const mod = await getPrefixModule(prefix, mathlib);
  if (!mod.ok) return null; // prefix doesn't compile → full analyze reports why
  const started = Date.now();
  let dir: string | undefined;
  try {
    dir = await mkdtemp(join(tmpdir(), 'leanui-analyze-'));
    const file = join(dir, 'Main.lean');
    await writeFile(file, `import ${mod.modName}\n${body}`, 'utf8');
    const timeoutMs = opts.timeoutMs ?? 60_000;

    // Persistent worker first (~20ms warm); one-shot process as fallback.
    // (The caller holds the mode's limiter slot, so a Mathlib one-shot here —
    // worker crash/timeout, not busy — is bounded by the Mathlib pool size.)
    const leanPath = await searchPath(mathlib, mod.dir);
    let parsed = await requestViaWorker(file, timeoutMs, leanPath, mathlib === true);
    if (!parsed) {
      const env = await extractEnv(mathlib, mod.dir);
      const out = await new Promise<ExecOut>((resolveExec) => {
        execFile(
          EXTRACT_BIN,
          [file],
          { env, timeout: timeoutMs, maxBuffer: 32 * 1024 * 1024 },
          (error, stdout, stderr) => resolveExec({ stdout: stdout ?? '', stderr: stderr ?? '', error: error ?? undefined }),
        );
      });
      if (out.error) return null;
      parsed = parseAnalyzeJson(out.stdout);
    }
    if (!parsed) return null;
    // Trial line 1 is the import; body line i sits at trial line i+1 but at
    // full-source line prefixLines+i → shift by prefixLines-1.
    const shifted = shiftAnalyzeLines(parsed, mod.lineCount - 1);
    const success = !shifted.messages.some((m) => m.severity === 'error');
    return { success, ...shifted, durationMs: Date.now() - started };
  } catch {
    return null;
  } finally {
    if (dir) await rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

async function runAnalyze(source: string, opts: CheckOptions = {}): Promise<AnalyzeResult> {
  const timeoutMs = opts.timeoutMs ?? 60_000;
  const started = Date.now();
  let dir: string | undefined;
  try {
    dir = await mkdtemp(join(tmpdir(), 'leanui-analyze-'));
    const file = join(dir, 'Main.lean');
    await writeFile(file, source, 'utf8');

    // Prefer a persistent --serve worker (env stays resident, ~20ms warm), then
    // the one-shot precompiled binary (supportInterpreter=true, so it
    // elaborates correctly), then `lean --run` if not yet built.
    //
    // Mathlib mode goes through the SAME worker, just with Mathlib on its
    // LEAN_PATH — the binary resolves imports at runtime, so it needs the path,
    // not a rebuild. Only when Mathlib isn't fetched/built does this fall
    // through to interpreting Extract.lean under `lake env`, which is ~30s a
    // call and exists now mainly to produce a real error message.
    const mathlibPath = opts.mathlib ? await mathlibEnv() : null;
    if ((!opts.mathlib || mathlibPath) && hasExtractBin()) {
      const parsed = await requestViaWorker(file, timeoutMs, await searchPath(opts.mathlib), opts.mathlib === true);
      if (parsed) {
        const success = !parsed.messages.some((m) => m.severity === 'error');
        return { success, ...parsed, durationMs: Date.now() - started };
      }
    }
    let out: ExecOut;
    let cmdName: string;
    if (opts.mathlib && mathlibPath && hasExtractBin()) {
      cmdName = 'extract';
      out = await run(EXTRACT_BIN, [file], {
        timeoutMs,
        env: await extractEnv(true),
      });
    } else if (opts.mathlib) {
      cmdName = 'lake';
      out = await run('lake', ['-R', '-K', 'mathlib=on', 'env', 'lean', '--run', EXTRACT_LEAN, file, 'mathlib'], {
        cwd: LEAN_PKG_DIR,
        timeoutMs,
      });
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
        bridgeError: `Lean extractor produced no output.${hintFor(detail)}${detail ? `\n${detail}` : ''}`,
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
