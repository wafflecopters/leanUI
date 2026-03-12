/**
 * Interactive Goal Rendering
 *
 * Generates goal LaTeX with \htmlId annotations on each subterm,
 * enabling click-to-select interaction in the UI.
 *
 * Path scheme for Pi spine:
 *   goal-root  = entire goal
 *   goal-0     = first Pi binder (including "→")
 *   goal-1     = second Pi binder
 *   goal-body  = return type after all binders
 */

import { TTKTerm } from '../compiler/kernel';
import { TTerm, occursInTT } from '../compiler/surface';
import { MetaVar, DefinitionsMap } from '../compiler/term';
import { betaNormalize } from '../compiler/subst';
import { TacticEngine } from '../tactics/tacticsEngine';
import { ReverseRegistry } from '../math-editor/tt-to-math';
import { kernelTypeToSurface, buildNameCtx, renderTerm } from './goal-computation';

// ============================================================================
// Types
// ============================================================================

/** Path identifying a subterm in the goal. */
export type GoalPath = readonly number[];

/** Information about a Pi binder in the goal's root spine. */
export interface GoalBinderInfo {
  readonly index: number;
  readonly name: string;
  readonly domainLatex: string;
  readonly isImplicit: boolean;
}

/** Result of rendering an interactive goal. */
export interface InteractiveGoal {
  /** Full LaTeX string with \htmlId annotations for each subterm. */
  readonly latex: string;
  /** Pi spine binders extracted from the goal (for intro suggestions). */
  readonly binders: readonly GoalBinderInfo[];
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
// Annotated LaTeX rendering
// ============================================================================

/**
 * Render a single Pi binder to LaTeX.
 * Named dependent binders render as "(name : domain)", others as just "domain".
 */
function renderBinderLatex(
  binder: SurfacePiBinder,
  ctx: string[],
  rev: ReverseRegistry,
): string {
  const domainLatex = renderTerm(binder.domain, ctx, rev);
  const isNamedDependent = binder.name !== '_' && binder.name !== ''
    && occursInTT(0, binder.body);
  if (isNamedDependent) {
    const nameLatex = binder.name.length === 1
      ? binder.name
      : `\\text{${binder.name}}`;
    return `(${nameLatex} : ${domainLatex})`;
  }
  return domainLatex;
}

/**
 * Render an interactive goal with \htmlId annotations.
 *
 * The goal's Pi spine is decomposed into individually-clickable binders,
 * each wrapped in \htmlId{goal-N}{...}. The body is wrapped in \htmlId{goal-body}{...}.
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

  // 3. Extract Pi spine
  const { binders, body } = extractSurfacePiSpine(surface);

  if (binders.length === 0) {
    // No Pi binders — just render the body
    const bodyLatex = renderTerm(surface, nameCtx, rev);
    return {
      latex: `\\htmlId{goal-root}{${bodyLatex}}`,
      binders: [],
    };
  }

  // 4. Render each binder with \htmlId
  const binderInfos: GoalBinderInfo[] = [];
  const parts: string[] = [];
  let ctx = [...nameCtx];

  for (let i = 0; i < binders.length; i++) {
    const b = binders[i];
    const binderLatex = renderBinderLatex(b, ctx, rev);
    const domainLatex = renderTerm(b.domain, ctx, rev);

    binderInfos.push({
      index: i,
      name: b.name,
      domainLatex,
      isImplicit: b.isImplicit,
    });

    // Wrap binder + arrow in \htmlId
    parts.push(`\\htmlId{goal-${i}}{${binderLatex} \\to}`);

    // Extend context for next binder
    ctx = [b.name, ...ctx];
  }

  // 5. Render body
  const bodyLatex = renderTerm(body, ctx, rev);
  parts.push(`\\htmlId{goal-body}{${bodyLatex}}`);

  // 6. Wrap everything
  const fullLatex = `\\htmlId{goal-root}{${parts.join('\\, ')}}`;

  return {
    latex: fullLatex,
    binders: binderInfos,
  };
}
