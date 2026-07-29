#!/usr/bin/env npx tsx
/**
 * A headless proof editor.
 *
 * Drives a real `ProofSession` against real Lean from the terminal: the same
 * controller the WYSIWYG panel uses, with a text interface instead of a React
 * one. Use it to reproduce a proof flow, inspect what the engine believes is
 * possible at a given goal, or check a change without opening a browser.
 *
 *   npx tsx scripts/proof-repl.ts --preset "Real Analysis (chain rule)" --decl limitAdd
 *   npx tsx scripts/proof-repl.ts --file path/to/File.lean --decl myTheorem
 *
 * Non-interactive (for scripts and CI):
 *   npx tsx scripts/proof-repl.ts --decl limitAdd --run "constructor; intros ε epsPos; goal"
 *
 * Type `help` at the prompt for the command list.
 */
import { createInterface } from 'node:readline/promises';
import { readFile } from 'node:fs/promises';
import { stdin, stdout } from 'node:process';
import { LEAN_PRESETS } from '../src/lean/presets';
import { ProofSession } from '../src/controller/session';
import { nodeAnalyzer, shutdownLeanBridge } from '../src/controller/nodeAnalyzer';
import { formatOutline } from '../src/controller/outline';
import { ACTION } from '../src/controller/actions';
import type { ActionDescriptor, SessionState } from '../src/controller/types';
import type { LeanDeclaration } from '../src/lean/types';
import { analyzeLeanSource } from '../server/lean-bridge';

// ─── argv ────────────────────────────────────────────────────────────────────

function arg(name: string): string | undefined {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? process.argv[i + 1] : undefined;
}

const PRESET = arg('preset') ?? 'Real Analysis (chain rule)';
const FILE = arg('file');
const DECL = arg('decl');
const RUN = arg('run');
const MATHLIB = process.argv.includes('--mathlib');

// ─── output ──────────────────────────────────────────────────────────────────

const C = {
  dim: (s: string) => `\x1b[2m${s}\x1b[0m`,
  bold: (s: string) => `\x1b[1m${s}\x1b[0m`,
  green: (s: string) => `\x1b[32m${s}\x1b[0m`,
  red: (s: string) => `\x1b[31m${s}\x1b[0m`,
  yellow: (s: string) => `\x1b[33m${s}\x1b[0m`,
  cyan: (s: string) => `\x1b[36m${s}\x1b[0m`,
};

const say = (s = '') => stdout.write(`${s}\n`);

function showGoal(state: SessionState): void {
  if (!state.goal) {
    say(C.dim(state.cursor.isHole ? '(no goal here — run `refresh`)' : '(the cursor is on a tactic, not an open goal)'));
    return;
  }
  for (const h of state.goal.hypotheses) {
    say(`  ${C.cyan(h.name)} : ${h.text}${h.isEquation ? C.dim('   (rewritable)') : ''}`);
  }
  say(`  ${C.bold('⊢')} ${C.bold(state.goal.targetText)}`);
}

function showSuggestions(state: SessionState): void {
  const pills = state.actions.filter((a) => a.group === 'suggestion');
  if (pills.length === 0) {
    say(C.dim(state.busy.suggestions ? '(still trialling…)' : '(nothing validated at this goal)'));
    return;
  }
  for (const a of pills) {
    const head = a.detail?.closes ? C.green('✓ closes') : C.dim(a.description ?? '');
    say(`  ${C.bold(a.label.padEnd(28))} ${head}`);
    for (const p of a.detail?.previews ?? []) say(`      ${C.dim('→')} ${latexToPlain(p)}`);
  }
}

/** Read a `{…}` group starting at `open`, respecting nesting. Returns the inner
 *  text and the index just past the closing brace. */
function braceGroup(s: string, open: number): { inner: string; end: number } | null {
  if (s[open] !== '{') return null;
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    if (s[i] === '{') depth++;
    else if (s[i] === '}' && --depth === 0) return { inner: s.slice(open + 1, i), end: i + 1 };
  }
  return null;
}

/** Unwrap every `\htmlId{id}{content}` to its content (they nest, one per
 *  subexpression, so this has to be brace-aware rather than a regex). */
function stripHtmlIds(s: string): string {
  const marker = '\\htmlId';
  const at = s.indexOf(marker);
  if (at === -1) return s;
  const id = braceGroup(s, at + marker.length);
  const body = id ? braceGroup(s, id.end) : null;
  if (!id || !body) return s.slice(0, at) + stripHtmlIds(s.slice(at + marker.length));
  return s.slice(0, at) + stripHtmlIds(body.inner) + stripHtmlIds(s.slice(body.end));
}

/** Previews are LaTeX (they're built for a renderer); strip them back to
 *  something a terminal can show. */
function latexToPlain(latex: string): string {
  let s = stripHtmlIds(latex);
  // Fractions nest, so keep rewriting until none are left.
  for (let i = 0; i < 8 && s.includes('\\frac'); i++) {
    s = s.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '$1/$2');
  }
  return s
    .replace(/\\varepsilon\s?/g, 'ε')
    .replace(/\\delta\s?/g, 'δ')
    .replace(/\\mathbb\{R\}\s?/g, 'ℝ')
    .replace(/\\operatorname\{([^}]*)\}/g, '$1')
    .replace(/\\text\{([^}]*)\}/g, '$1')
    .replace(/\\le(?![a-zA-Z])\s?/g, ' ≤ ')
    .replace(/\\to(?![a-zA-Z])\s?/g, ' → ')
    .replace(/\\cdot\s?/g, '·')
    .replace(/\\;|\\,/g, ' ')
    .replace(/[{}]/g, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function showActions(state: SessionState): void {
  const groups: Array<[string, ActionDescriptor[]]> = [];
  for (const a of state.actions) {
    const g = groups.find(([name]) => name === a.group);
    if (g) g[1].push(a);
    else groups.push([a.group, [a]]);
  }
  for (const [group, actions] of groups) {
    say(C.bold(group.toUpperCase()));
    for (const a of actions) {
      const params = a.params.map((p) => `<${p.name}>`).join(' ');
      say(`  ${a.id}${params ? ' ' + params : ''}`);
      if (a.description) say(`      ${C.dim(a.description)}`);
      const choices = a.params.flatMap((p) => p.choices ?? []);
      if (choices.length) say(`      ${C.dim(`choices: ${choices.slice(0, 12).join(', ')}${choices.length > 12 ? ' …' : ''}`)}`);
    }
  }
}

function showStatus(state: SessionState): void {
  const bits = [
    `${state.status.openGoals} open`,
    state.status.complete ? C.green('complete') : '',
    state.busy.goals ? C.yellow('goals…') : '',
    state.busy.suggestions ? C.yellow('suggestions…') : '',
    state.error ? C.red(state.error) : '',
  ].filter(Boolean);
  say(C.dim(bits.join('  ')));
  for (const d of state.status.diagnostics) {
    say(`  ${d.severity === 'error' ? C.red('✗') : C.yellow('!')} ${d.text.split('\n')[0]}`);
  }
}

// ─── commands ────────────────────────────────────────────────────────────────

const HELP = `
  goal                 the goal at the cursor
  proof                the whole proof, with the cursor marked
  suggest              validated suggestions here (what one click would do)
  actions              EVERY move available right now, with its arguments
  status               open goals, diagnostics, busy flags
  source               the proof as it would be written to the file

  do <action> [args]   dispatch an action by id (see \`actions\`)
  <tactic> <args>      shorthand for a manual tactic: intros ε h / apply divPos /
                       rewrite halfEqDiv / exact h / unfold Carrier / simp / have h := e
  take <n|label>       take the nth suggestion (or the first whose label matches)
  select <pos>         focus a goal subterm by its Lean SubExpr.Pos
  hyp <name>           select a hypothesis (shows its action tray)
  clear                clear the selection

  next / prev          move to the next / previous open goal
  goto <id>            move the cursor to a proof step
  undo / redo
  refresh              re-run Lean (goals + suggestions)
  help / quit
`;

async function main(): Promise<void> {
  const { source, declarations } = await loadFile();
  if (!DECL) {
    say(C.bold('Provable declarations in this file:'));
    for (const d of declarations) say(`  ${d.kind.padEnd(9)} ${d.name}`);
    say(`\nRe-run with --decl <name>.`);
    return;
  }

  let analyzeCount = 0;
  const session = ProofSession.open({
    analyze: nodeAnalyzer({ onTiming: () => analyzeCount++ }),
    source,
    declarations,
    declName: DECL,
    mathlib: MATHLIB,
    // The REPL drives Lean explicitly, so a command's output never races a
    // background timer.
    autoRefresh: false,
  });

  say(C.bold(`\n${session.declaration.name} : ${session.declaration.prettyType}\n`));
  say(C.dim('running Lean…'));
  await session.refresh();
  showGoal(session.getState());
  say();

  const runCommand = async (line: string): Promise<boolean> => {
    const [cmd, ...rest] = line.trim().split(/\s+/);
    const args = rest.join(' ');
    const state = session.getState();
    switch (cmd) {
      case '': return true;
      case 'quit': case 'exit': case 'q': return false;
      case 'help': case '?': say(HELP); return true;
      case 'goal': showGoal(state); return true;
      case 'proof': say(formatOutline(state.outline)); return true;
      case 'suggest': showSuggestions(state); return true;
      case 'actions': showActions(state); return true;
      case 'status': showStatus(state); return true;
      case 'source': say(state.proofSource); return true;

      case 'do': {
        const [id, ...vals] = args.split(/\s+/);
        const action = state.actions.find((a) => a.id === id);
        const argMap: Record<string, string> = {};
        action?.params.forEach((p, i) => {
          argMap[p.name] = i === action.params.length - 1 ? vals.slice(i).join(' ') : vals[i] ?? '';
        });
        return report(session.dispatch({ id, args: argMap }));
      }

      case 'take': {
        const pills = state.actions.filter((a) => a.group === 'suggestion');
        const n = Number(args);
        const pick = Number.isFinite(n) ? pills[n - 1] : pills.find((p) => p.label.includes(args));
        if (!pick) { say(C.red(`no suggestion "${args}"`)); return true; }
        say(C.dim(`→ ${pick.detail?.tactic}`));
        return report(session.dispatch({ id: pick.id }));
      }

      case 'select': return report(session.selectSubterm(args || null));
      case 'hyp': return report(session.selectHypothesis(args || null));
      case 'clear': return report(session.dispatch({ id: ACTION.clearSelection }));
      case 'next': return report(session.cursorToHole(1));
      case 'prev': return report(session.cursorToHole(-1));
      case 'goto': return report(session.moveCursor(Number(args)));
      case 'undo': return report(session.undo());
      case 'redo': return report(session.redo());
      case 'refresh': await session.refresh(); showGoal(session.getState()); return true;

      // Bare tactic shorthand.
      case 'intros': case 'intro': case 'induction': case 'exact': case 'unfold':
      case 'fold': case 'rewrite': case 'apply': case 'simp': case 'have': {
        const tactic = cmd === 'intro' ? 'intros' : cmd;
        return report(session.runTactic(tactic as never, args));
      }
      case 'constructor': return report(session.insertTactic('constructor'));
      default:
        say(C.red(`unknown command "${cmd}" — try \`help\``));
        return true;
    }
  };

  /** Report a dispatch result; on success, re-run Lean and show the new goal. */
  const report = async (r: { ok: boolean; error?: string }): Promise<boolean> => {
    if (!r.ok) { say(C.red(`✗ ${r.error}`)); return true; }
    await session.refresh();
    const s = session.getState();
    showGoal(s);
    if (s.status.complete) say(C.green('\n  ✓ proof complete'));
    return true;
  };

  if (RUN) {
    for (const line of RUN.split(';')) {
      say(`${C.dim('>')} ${line.trim()}`);
      if (!(await runCommand(line))) break;
      say();
    }
    say(C.dim(`(${analyzeCount} Lean requests)`));
    return;
  }

  const rl = createInterface({ input: stdin, output: stdout });
  for (;;) {
    const line = await rl.question(C.bold('proof> '));
    let keepGoing: boolean;
    try {
      keepGoing = await runCommand(line);
    } catch (e) {
      say(C.red(String(e instanceof Error ? e.stack ?? e.message : e)));
      keepGoing = true;
    }
    if (!keepGoing) break;
    say();
  }
  rl.close();
}

/** The Lean file to work on: a named preset, or a path. Its declarations come
 *  from a real analyze — the same list the app would show. */
async function loadFile(): Promise<{ source: string; declarations: LeanDeclaration[] }> {
  let source: string;
  if (FILE) {
    source = await readFile(FILE, 'utf8');
  } else {
    const preset = LEAN_PRESETS.find((p) => p.name === PRESET);
    if (!preset) {
      throw new Error(`no preset "${PRESET}". Available: ${LEAN_PRESETS.map((p) => p.name).join(', ')}`);
    }
    source = preset.code;
  }
  say(C.dim('elaborating the file…'));
  const result = await analyzeLeanSource(source, { mathlib: MATHLIB, timeoutMs: 300_000 });
  if (result.bridgeError) throw new Error(`Lean bridge: ${result.bridgeError}`);
  return { source, declarations: result.declarations };
}

main()
  .catch((e) => {
    say(C.red(String(e instanceof Error ? e.stack ?? e.message : e)));
    process.exitCode = 1;
  })
  .finally(() => {
    // Lean's persistent workers hold the event loop open.
    shutdownLeanBridge();
  });
