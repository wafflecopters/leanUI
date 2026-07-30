/**
 * Test doubles for the proof controller — a fake Lean that answers from a
 * rule table instead of running the real thing.
 *
 * Real Lean is the ground truth, and the e2e suites use it. But a whole class
 * of controller bugs (a candidate never generated, a suggestion sorted wrong, a
 * cursor left in the wrong place, an action offered when it can't run) has
 * nothing to do with Lean and everything to do with the wiring — and those
 * deserve tests that run in milliseconds and pin down exact behaviour.
 *
 * The fake speaks the real protocol: it reads the assembled Lean source, finds
 * the `sorry` lines, and reports goals at exactly the (line, column) positions
 * `proofTreeToLean` recorded for those holes — so the controller's range
 * matching is genuinely exercised, not stubbed past.
 *
 * NOT part of the app: only tests and the REPL import this.
 */
import type { AnalyzeResult, LeanDeclaration, LeanGoalState, LeanMessage, TaggedText } from '../lean/types';
import type { AnalyzeInput, LeanAnalyzer } from './analyzer';

/** Plain text → the flat TaggedText the renderers accept. */
export function text(s: string): TaggedText {
  return { t: 'text', s };
}

/**
 * Plain text → a TAGGED tree with subexpression positions, the way Lean's
 * `ppExprTagged` delivers goals.
 *
 * Real goals are clickable because every subexpression carries a `SubExpr.Pos`;
 * a flat text node has none, and code that reads subterms would silently see an
 * empty goal. This tags the whole term at `/` and each whitespace-separated
 * token at `/<i>` — not Lean's exact numbering (positions are opaque strings to
 * everything downstream), but the same SHAPE, so selection really is exercised.
 */
export function taggedTerm(s: string): TaggedText {
  const tokens = s.split(' ');
  const kids: TaggedText[] = [];
  tokens.forEach((tok, i) => {
    if (i > 0) kids.push({ t: 'text', s: ' ' });
    kids.push(tok.length ? { t: 'tag', pos: `/${i}`, child: { t: 'text', s: tok } } : { t: 'text', s: tok });
  });
  return { t: 'tag', pos: '/', child: { t: 'append', kids } };
}

/** A goal state from plain strings, with `plain` built the way Lean builds it
 *  (hypotheses, then `⊢ target`) so code that reads `plain` is tested honestly. */
export function goalState(
  target: string,
  hyps: ReadonlyArray<{ names: string[]; type: string }> = [],
  caseTag?: string,
): LeanGoalState {
  const plain = [...hyps.map((h) => `${h.names.join(' ')} : ${h.type}`), `⊢ ${target}`].join('\n');
  return {
    ...(caseTag ? { case: caseTag } : {}),
    hyps: hyps.map((h) => ({ names: h.names, type: text(h.type) })),
    targetTagged: taggedTerm(target),
    plain,
  };
}

/** What the fake Lean does when a trial contains a given tactic. */
export interface FakeRule {
  /** Matches a trial whose source contains this exact tactic line (trimmed). */
  tactic: string;
  /** Lean rejects the tactic, reporting this error at its own line. */
  error?: string;
  /**
   * Also report a knock-on `unsolved goals` at the DECLARATION line, the way
   * real Lean does when a tactic doesn't exist at all (measured on core Lean:
   * `positivity` gives `unknown tactic` at its own line AND `unsolved goals`
   * at the `theorem`). Lets a test prove the drop survives the second error.
   */
  alsoUnsolvedAtDecl?: boolean;
  /** The goals the tactic leaves. Omitted/empty means it CLOSES the goal. */
  leaves?: Array<{ target: string; case?: string }>;
}

export interface FakeLeanOptions {
  /** The file's declarations (the lemma library the ranker sees). */
  declarations?: LeanDeclaration[];
  /** The goal at an untouched hole — the baseline read, before any trial. */
  baseline?: { target: string; hyps?: Array<{ names: string[]; type: string }>; case?: string };
  rules?: FakeRule[];
  /**
   * Answers for the term probe: expression → the type it still has.
   *
   * `probeTerm` elaborates `have leanuiProbe := <expr>` and reads the probe
   * binder's REMAINING type; its Pi binders are the arguments still missing.
   * Map `'limF.eps_delta'` to `'(epsilon : ℝ) → 0 < epsilon → DPair …'` and the
   * fake reports two open slots, exactly as Lean would.
   */
  probes?: Record<string, string>;
  /** Messages emitted for every request (e.g. a file-level sorry warning). */
  messages?: LeanMessage[];
  /** Called with each request, in order — lets a test assert on what was sent. */
  onRequest?: (input: AnalyzeInput) => void;
}

interface SourceLine {
  /** 1-based. */
  line: number;
  /** 0-based indent width — matches `proofTreeToLean`'s `startCol`. */
  col: number;
  content: string;
}

function scan(source: string): SourceLine[] {
  return source.split('\n').map((raw, i) => ({
    line: i + 1,
    col: raw.length - raw.trimStart().length,
    content: raw.trim(),
  }));
}

/**
 * A fake Lean.
 *
 * Behaviour per request:
 *  - Find the first line matching a rule's tactic. That's the trial's tactic.
 *  - If the rule has an `error`, report it at that line and stop (the trial fails).
 *  - Otherwise report the rule's `leaves` as the goals at the NEXT `sorry`
 *    after the tactic (the tactic's continuation hole). No `leaves` and no
 *    following `sorry` means it closed the goal.
 *  - Every OTHER `sorry` gets the baseline goal, so an untouched proof reads
 *    exactly as it would from real Lean.
 */
export function fakeLean(opts: FakeLeanOptions = {}): LeanAnalyzer {
  const rules = opts.rules ?? [];
  const baseline = opts.baseline;

  return async (input: AnalyzeInput): Promise<AnalyzeResult> => {
    opts.onRequest?.(input);
    const lines = scan(input.source);
    const messages: LeanMessage[] = [...(opts.messages ?? [])];
    const goals: AnalyzeResult['goals'] = [];

    const holes = lines.filter((l) => l.content === 'sorry');

    // A term probe (`have leanuiProbe := <expr>`) is answered by reporting the
    // probe binder in the context of the hole that follows it.
    const probeLine = lines.find((l) => l.content.startsWith('have leanuiProbe := '));
    if (probeLine) {
      const expr = probeLine.content.slice('have leanuiProbe := '.length).trim();
      const type = opts.probes?.[expr];
      const after = holes.find((h) => h.line > probeLine.line);
      if (type === undefined) {
        messages.push({
          severity: 'error',
          startLine: probeLine.line,
          startCol: probeLine.col,
          endLine: probeLine.line,
          endCol: probeLine.col + probeLine.content.length,
          text: `unknown term ${expr}`,
        });
      } else if (after) {
        goals.push(
          holeGoal(after, [
            goalState(baseline?.target ?? 'True', [
              ...(baseline?.hyps ?? []),
              { names: ['leanuiProbe'], type },
            ]),
          ]),
        );
      }
      return result(messages, goals, opts.declarations);
    }

    // The trial's tactic: the first line matching a rule.
    let hit: { rule: FakeRule; at: SourceLine } | null = null;
    for (const l of lines) {
      const rule = rules.find((r) => r.tactic === l.content);
      if (rule) {
        hit = { rule, at: l };
        break;
      }
    }

    if (hit?.rule.error) {
      messages.push({
        severity: 'error',
        startLine: hit.at.line,
        startCol: hit.at.col,
        endLine: hit.at.line,
        endCol: hit.at.col + hit.at.content.length,
        text: hit.rule.error,
      });
      if (hit.rule.alsoUnsolvedAtDecl) {
        // The enclosing `by` — where Lean pins leftover goals.
        const byLine = input.source.split('\n').findIndex((l) => /:=\s*by\b/.test(l)) + 1;
        messages.push({
          severity: 'error',
          startLine: byLine || 1,
          startCol: 0,
          endLine: byLine || 1,
          endCol: 0,
          text: 'unsolved goals',
        });
      }
      // A failed tactic still leaves the other holes reporting their goals.
      for (const h of holes) {
        if (baseline) goals.push(holeGoal(h, [baselineState(baseline)]));
      }
      return result(messages, goals, opts.declarations);
    }

    // The continuation hole belongs to the trialed tactic.
    const contHole = hit ? holes.find((h) => h.line > hit!.at.line) : undefined;
    for (const h of holes) {
      if (contHole && h.line === contHole.line) {
        const leaves = hit?.rule.leaves ?? [];
        if (leaves.length > 0) {
          goals.push(holeGoal(h, leaves.map((g) => goalState(g.target, [], g.case))));
        }
        // No leaves → the tactic closed the goal; the hole reports nothing.
        continue;
      }
      if (baseline) goals.push(holeGoal(h, [baselineState(baseline)]));
    }

    // A trial with no continuation hole that leaves goals reports them as
    // "unsolved goals" at the enclosing `by`, exactly as Lean does.
    if (hit && !contHole && (hit.rule.leaves?.length ?? 0) > 0) {
      messages.push({
        severity: 'error',
        startLine: Math.max(1, hit.at.line - 1),
        startCol: 0,
        endLine: hit.at.line,
        endCol: 0,
        text: 'unsolved goals',
      });
    }

    return result(messages, goals, opts.declarations);
  };
}

function baselineState(b: NonNullable<FakeLeanOptions['baseline']>): LeanGoalState {
  return goalState(b.target, b.hyps ?? [], b.case);
}

function holeGoal(at: SourceLine, states: LeanGoalState[]): AnalyzeResult['goals'][number] {
  return {
    startLine: at.line,
    startCol: at.col,
    endLine: at.line,
    endCol: at.col + at.content.length,
    goals: states,
  };
}

function result(
  messages: LeanMessage[],
  goals: AnalyzeResult['goals'],
  declarations: LeanDeclaration[] = [],
): AnalyzeResult {
  return {
    success: !messages.some((m) => m.severity === 'error'),
    messages,
    goals,
    declarations,
    durationMs: 0,
  };
}

/** An analyzer that always fails at the transport layer (bridge down). */
export const deadAnalyzer: LeanAnalyzer = async () => null;

/** An analyzer whose every response carries a bridge error. */
export function brokenAnalyzer(message = 'lean not found'): LeanAnalyzer {
  return async () => ({
    success: false,
    messages: [],
    goals: [],
    declarations: [],
    bridgeError: message,
    durationMs: 0,
  });
}
