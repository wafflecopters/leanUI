/**
 * Interactive Goal Rendering
 *
 * Generates goal LaTeX with \htmlId annotations on each subterm,
 * enabling click-to-select interaction in the UI.
 *
 * Path scheme:
 *   goal-root   = entire goal
 *   goal-0      = first Pi binder (including "→")
 *   goal-1      = second Pi binder
 *   goal-body   = return type after all binders
 *   goal-t0..N  = individual subterms within binders/body
 */

import { TTKTerm } from '../compiler/kernel';
import { TTerm, occursInTT } from '../compiler/surface';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { betaNormalize } from '../compiler/subst';
import { TacticEngine } from '../tactics/tacticsEngine';
import { ReverseRegistry, SubtermAnnotator } from '../math-editor/tt-to-math';
import { MathNode, mkGroup } from '../math-editor/types';
import { kernelTypeToSurface, buildNameCtx, renderTerm, renderTermAnnotated, extractTypeHead } from './goal-computation';

// ============================================================================
// Types
// ============================================================================

/** Selected subterm identified by its htmlId string. */
export type GoalPath = string;

/** Information about a Pi binder in the goal's root spine. */
export interface GoalBinderInfo {
  readonly index: number;
  readonly name: string;
  readonly domainLatex: string;
  readonly isImplicit: boolean;
}

/** Information about an annotated subterm in the goal. */
export interface SubtermInfo {
  readonly htmlId: string;
  readonly term: TTerm;
  /** True if this subterm is an App whose head is a Const. */
  readonly isAppOfConst: boolean;
  /** The Const name at the head of the App (if isAppOfConst), or the Const name (if tag='Const'). */
  readonly headName?: string;
  /** If term is a Var, the resolved variable name from context. */
  readonly varName?: string;
  /** 1-based occurrence index of this headName in the goal body (for targeted rewriting). */
  readonly occurrenceIndex?: number;
}

/** Result of rendering an interactive goal. */
export interface InteractiveGoal {
  /** Full LaTeX string with \htmlId annotations for each subterm. */
  readonly latex: string;
  /** Pi spine binders extracted from the goal (for intro suggestions). */
  readonly binders: readonly GoalBinderInfo[];
  /** Map from htmlId to subterm info, for all annotated subterms. */
  readonly subtermMap: ReadonlyMap<string, SubtermInfo>;
  /** Map from variable name to its type head name (for induction suggestions). */
  readonly contextVarTypes: ReadonlyMap<string, string>;
}

// ============================================================================
// Pi spine extraction from surface terms
// ============================================================================

interface SurfacePiBinder {
  readonly name: string;
  readonly domain: TTerm;
  readonly body: TTerm;
  readonly isImplicit: boolean;
}

function peelSurfacePi(type: TTerm): SurfacePiBinder | null {
  if (type.tag === 'Binder' && type.binderKind.tag === 'BPiTT') {
    return {
      name: type.name,
      domain: type.domain!,
      body: type.body,
      isImplicit: type.named === true,
    };
  }
  if (type.tag === 'MultiBinder' && type.binderKind.tag === 'BPiTT') {
    const firstName = type.names[0];
    const remainingNames = type.names.slice(1);
    const body: TTerm = remainingNames.length > 0
      ? { ...type, names: remainingNames }
      : type.body;
    return {
      name: firstName,
      domain: type.domain,
      body,
      isImplicit: type.named === true,
    };
  }
  return null;
}

function extractSurfacePiSpine(term: TTerm): { binders: SurfacePiBinder[]; body: TTerm } {
  const binders: SurfacePiBinder[] = [];
  let current = term;
  while (true) {
    const pi = peelSurfacePi(current);
    if (!pi) break;
    binders.push(pi);
    current = pi.body;
  }
  return { binders, body: current };
}

// ============================================================================
// Subterm annotation helpers
// ============================================================================

/** Get the head constant name of an App chain, or null if not Const-headed. */
function getAppHeadName(term: TTerm): string | null {
  let current = term;
  while (current.tag === 'App') current = current.fn;
  return current.tag === 'Const' ? current.name : null;
}

/** Create a SubtermAnnotator that assigns unique IDs and collects SubtermInfo. */
function createAnnotator(): { annotate: SubtermAnnotator; subtermMap: Map<string, SubtermInfo> } {
  let nextId = 0;
  const subtermMap = new Map<string, SubtermInfo>();
  // Count occurrences per headName for targeted rewriting (1-based)
  const headOccurrences = new Map<string, number>();

  const annotate: SubtermAnnotator = (nodes: MathNode[], term: TTerm, ctx: string[]): MathNode[] => {
    const htmlId = `goal-t${nextId++}`;
    const headName = term.tag === 'App' ? getAppHeadName(term) : term.tag === 'Const' ? term.name : undefined;
    const varName = term.tag === 'Var' && term.index < ctx.length ? ctx[term.index] : undefined;
    let occurrenceIndex: number | undefined;
    if (headName) {
      const count = (headOccurrences.get(headName) ?? 0) + 1;
      headOccurrences.set(headName, count);
      occurrenceIndex = count;
    }
    subtermMap.set(htmlId, {
      htmlId,
      term,
      isAppOfConst: term.tag === 'App' && headName !== null,
      headName: headName ?? undefined,
      varName,
      occurrenceIndex,
    });
    return [mkGroup(htmlId, nodes)];
  };

  return { annotate, subtermMap };
}

// ============================================================================
// Annotated LaTeX rendering
// ============================================================================

/**
 * Render a variable name for LaTeX (italicize single chars, textify multi-char).
 */
function binderNameLatex(name: string): string {
  if (name.length === 1) return name;
  if (name.length === 2 && name[1] === "'") return `${name[0]}'`;
  return `\\text{${name}}`;
}

/**
 * Check if a domain type is "simple" (no arrows) — determines \in vs : separator.
 * Simple types: Const, Var, App of Const/Var to args.
 * Complex types: Pi/arrow types.
 */
function isSimpleDomain(domain: TTerm): boolean {
  if (domain.tag === 'Binder' && domain.binderKind.tag === 'BPiTT') return false;
  return true;
}

/** Classified binder info for forall grouping. */
interface ClassifiedBinder {
  readonly index: number;
  readonly binder: SurfacePiBinder;
  readonly isDependent: boolean;
  readonly nameLatex: string;
  /** Context at this binder position (for rendering domain). */
  readonly ctxAtBinder: string[];
  /** Unannotated domain rendering (for grouping comparison). */
  readonly domainKey: string;
}

/**
 * Render an interactive goal with \htmlId annotations.
 *
 * The goal's Pi spine is decomposed into individually-clickable binders,
 * each wrapped in \htmlId{goal-N}{...}. The body is wrapped in \htmlId{goal-body}{...}.
 * Within each section, every subterm gets its own \htmlId{goal-tN}{...}.
 */
export function renderInteractiveGoal(
  engine: TacticEngine,
  goal: MetaVar,
  definitions: DefinitionsMap,
  rev: ReverseRegistry,
): InteractiveGoal {
  // 1. Zonk and normalize
  const zonked = engine.zonkTerm(goal.type, goal.ctx.length);
  const normalized = betaNormalize(zonked);

  // 2. Convert to surface
  const surface = kernelTypeToSurface(normalized, definitions);
  const nameCtx = buildNameCtx(goal.ctx);

  // 3. Compute context variable type heads (for induction suggestions)
  const contextVarTypes = new Map<string, string>();
  for (const entry of goal.ctx) {
    const surfaceType = kernelTypeToSurface(entry.type, definitions);
    const head = extractTypeHead(surfaceType);
    if (head) contextVarTypes.set(entry.name, head);
  }

  // 4. Create annotator for subterm tracking
  const { annotate, subtermMap } = createAnnotator();

  // 4. Extract Pi spine
  const { binders, body } = extractSurfacePiSpine(surface);

  if (binders.length === 0) {
    // No Pi binders — just render the body with annotations
    const bodyLatex = renderTermAnnotated(surface, nameCtx, rev, annotate);
    return {
      latex: `\\htmlId{goal-root}{${bodyLatex}}`,
      binders: [],
      subtermMap,
      contextVarTypes,
    };
  }

  // 5. Classify all binders (first pass — no annotation yet)
  const binderInfos: GoalBinderInfo[] = [];
  const classified: ClassifiedBinder[] = [];
  let ctx = [...nameCtx];

  for (let i = 0; i < binders.length; i++) {
    const b = binders[i];
    const isDependent = b.name !== '_' && b.name !== '' && occursInTT(0, b.body);
    const nameLatex = binderNameLatex(b.name);
    const domainKey = renderTerm(b.domain, ctx, rev);

    binderInfos.push({
      index: i,
      name: b.name,
      domainLatex: domainKey,
      isImplicit: b.isImplicit,
    });

    classified.push({ index: i, binder: b, isDependent, nameLatex, ctxAtBinder: ctx, domainKey });
    ctx = [b.name, ...ctx];
  }

  // 6. Render binders as \forall groups + arrow types
  const parts: string[] = [];
  let pos = 0;

  while (pos < classified.length) {
    const c = classified[pos];

    if (!c.isDependent) {
      // Non-dependent arrow: render as "domain →"
      const domainLatex = renderTermAnnotated(c.binder.domain, c.ctxAtBinder, rev, annotate);
      // Wrap in parens when domain is a function type to avoid ambiguity
      // e.g., (A → C) → not A → C →
      const needsParens = c.binder.domain.tag === 'Binder' && c.binder.domain.binderKind.tag === 'BPiTT';
      const wrapped = needsParens ? `(${domainLatex})` : domainLatex;
      parts.push(`\\htmlId{goal-${c.index}}{${wrapped} \\to}`);
      pos++;
      continue;
    }

    // Start a \forall run: collect consecutive dependent binders
    const runStart = pos;
    while (pos < classified.length && classified[pos].isDependent) {
      pos++;
    }
    const run = classified.slice(runStart, pos);

    // Sub-group the run by domain type (using unannotated rendering for comparison)
    const subgroups: Array<{ entries: ClassifiedBinder[]; separator: string }> = [];
    let gi = 0;
    while (gi < run.length) {
      const groupStart = gi;
      const key = run[gi].domainKey;
      gi++;
      while (gi < run.length && run[gi].domainKey === key) {
        gi++;
      }
      const group = run.slice(groupStart, gi);
      const sep = isSimpleDomain(group[0].binder.domain) ? '\\in' : ':';
      subgroups.push({ entries: group, separator: sep });
    }

    // Render: \forall name₁, name₂ ∈ domain, name₃ : domain₂, ...
    let forallLatex = '\\forall \\,';
    const groupParts: string[] = [];
    for (const sg of subgroups) {
      const names = sg.entries.map(e =>
        `\\htmlId{goal-${e.index}}{${e.nameLatex}}`
      ).join(', ');
      // Render domain ONCE with annotations (using first entry's context)
      const domainLatex = renderTermAnnotated(
        sg.entries[0].binder.domain, sg.entries[0].ctxAtBinder, rev, annotate,
      );
      groupParts.push(`${names} ${sg.separator} ${domainLatex}`);
    }
    forallLatex += groupParts.join(',\\,');
    forallLatex += ',\\,';
    parts.push(forallLatex);
  }

  // 7. Render body with annotations
  const bodyLatex = renderTermAnnotated(body, ctx, rev, annotate);
  parts.push(`\\htmlId{goal-body}{${bodyLatex}}`);

  // 8. Wrap everything
  const fullLatex = `\\htmlId{goal-root}{${parts.join(' ')}}`;

  return {
    latex: fullLatex,
    binders: binderInfos,
    subtermMap,
    contextVarTypes,
  };
}
