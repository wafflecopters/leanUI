/**
 * Goal computation — walks the proof tree alongside a surface type to
 * compute real hypotheses (with types) and goals at each cursor position.
 *
 * This is the bridge between the UI-level proof tree and the structured
 * math editor. Uses the same rendering pipeline (ttermToMathNodes +
 * renderStaticLatex) as the WYSIWYG type signature editor.
 *
 * Case-specific goals: When inside an induction case with constructor
 * metadata, the scrutinee variable is substituted with the constructor
 * pattern (e.g., n → Zero, n → Succ k) and extra hypotheses are added
 * for constructor params and induction hypotheses.
 */

import { TTerm, substTT, shiftSurfaceTerm, mkConstTT, mkAppTT, mkVarTT } from '../compiler/surface';
import { SyntaxRegistry } from '../math-editor/syntax-registry';
import { ReverseRegistry, buildReverseRegistry, ttermToMathNodes } from '../math-editor/tt-to-math';
import { mkRow } from '../math-editor/types';
import { renderStaticLatex } from '../math-editor/render';
import { ProofNode, ProofNodeId, CaseNode } from './proof-tree';

// ============================================================================
// Types
// ============================================================================

export interface TypedHypothesis {
  readonly name: string;
  readonly type: string;  // LaTeX string from structured math renderer
  readonly rawType?: TTerm;  // Raw surface type (for inductive type lookup)
}

export interface TypedProofContext {
  readonly hypotheses: readonly TypedHypothesis[];
  readonly caseLabel?: string;
  readonly inductionVar?: string;
  readonly goal: string;  // LaTeX string from structured math renderer
}

/** Info about an inductive type's constructors (surface-level). */
export interface InductiveInfo {
  readonly name: string;
  readonly constructors: ReadonlyArray<{ readonly name: string; readonly type: TTerm }>;
}

/** Map from inductive type name to its info. */
export type InductiveMap = ReadonlyMap<string, InductiveInfo>;

/** Info about a constructor case for generating case nodes. */
export interface ConstructorCaseInfo {
  readonly label: string;
  readonly constructorName: string;
  readonly paramNames: readonly string[];
}

// ============================================================================
// Core computation
// ============================================================================

/**
 * Compute typed context at cursor position by walking the proof tree
 * alongside the surface type. Peels Pi binders for intros to extract
 * real types. Renders types using the structured math editor pipeline.
 *
 * Returns null if cursor not found in tree.
 */
export function computeTypedContext(
  root: ProofNode,
  cursorId: ProofNodeId,
  surfaceType: TTerm,
  registry: SyntaxRegistry,
  inductiveMap?: InductiveMap,
): TypedProofContext | null {
  const rev = buildReverseRegistry(registry);
  return walkTree(root, cursorId, surfaceType, [], [], [], rev, inductiveMap);
}

/**
 * Peel one Pi binder from a surface type (TTerm).
 * Handles both single Binder and MultiBinder.
 * Returns the domain type and remaining body, or null if not a Pi.
 */
function peelPi(type: TTerm): { name: string; domain: TTerm; body: TTerm; isImplicit: boolean } | null {
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
    // If more names remain, reconstruct MultiBinder with fewer names
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

/** Render a TTerm expression to LaTeX using the structured math editor pipeline. */
function renderTerm(term: TTerm, ctx: string[], rev: ReverseRegistry): string {
  const nodes = ttermToMathNodes(term, rev, ctx);
  return renderStaticLatex(mkRow(nodes));
}

// ============================================================================
// Inductive type helpers
// ============================================================================

/** Extract the head constant name from a type (e.g., 'Nat' from Const('Nat'), 'List' from App(Const('List'), ...)). */
export function extractTypeHead(type: TTerm): string | null {
  if (type.tag === 'Const') return type.name;
  if (type.tag === 'App') return extractTypeHead(type.fn);
  return null;
}

/**
 * Peel explicit (non-implicit) Pi binders from a constructor type,
 * skipping the result type at the end.
 * E.g., for `Succ : Nat -> Nat`, returns [{ name: 'n', domain: Nat }]
 * For `Zero : Nat`, returns []
 */
export function peelConstructorParams(ctorType: TTerm): Array<{ name: string; domain: TTerm }> {
  const params: Array<{ name: string; domain: TTerm }> = [];
  let t = ctorType;
  while (true) {
    const pi = peelPi(t);
    if (!pi) break;
    if (pi.isImplicit) {
      // Skip implicit params
      t = pi.body;
      continue;
    }
    params.push({ name: pi.name, domain: pi.domain });
    t = pi.body;
  }
  // The last type is the return type (e.g., Nat) — don't include it
  // We already collected all Pi params above
  return params;
}

/**
 * Check if a constructor parameter is recursive (references the inductive type).
 */
function isRecursiveParam(domain: TTerm, inductiveName: string): boolean {
  const head = extractTypeHead(domain);
  return head === inductiveName;
}

/**
 * Build a TTerm for a constructor application with named params.
 * E.g., Succ with ['k'] → App(Const('Succ'), Var(0)) in a context where k is at index 0.
 */
function buildConstructorApp(ctorName: string, paramNames: readonly string[]): TTerm {
  let app: TTerm = mkConstTT(ctorName);
  for (let i = paramNames.length - 1; i >= 0; i--) {
    app = mkAppTT(app, mkVarTT(i));
  }
  return app;
}

/**
 * Generate ConstructorCaseInfo for each constructor of an inductive type.
 * Uses scrutinee name for labeling. When rev is provided, renders labels
 * through the structured math pipeline for proper notation.
 */
export function generateCaseInfos(
  scrutinee: string,
  inductiveInfo: InductiveInfo,
  rev?: ReverseRegistry,
): ConstructorCaseInfo[] {
  return inductiveInfo.constructors.map(ctor => {
    const params = peelConstructorParams(ctor.type);
    const paramNames = params.map((p, i) => {
      return p.name !== '_' ? p.name : `x${i}`;
    });

    // Build plain-text label as fallback
    let label = `${scrutinee} = ${ctor.name}`;
    if (paramNames.length > 0) {
      label += ' ' + paramNames.join(' ');
    }

    // Build structured LaTeX label when renderer available
    let labelLatex: string | undefined;
    if (rev) {
      const ctorApp = buildConstructorApp(ctor.name, paramNames);
      // Context: paramNames in reverse order (de Bruijn: index 0 = last param)
      const ctx = [...paramNames].reverse();
      const rhsLatex = renderTerm(ctorApp, ctx, rev);
      labelLatex = `${scrutinee} = ${rhsLatex}`;
    }

    return {
      label,
      constructorName: ctor.name,
      paramNames,
      labelLatex,
    };
  });
}

// ============================================================================
// Case-specific goal computation
// ============================================================================

/**
 * Compute the goal for a specific induction case by substituting the
 * scrutinee variable with the constructor pattern.
 *
 * For a goal P(n) in a case where n = Succ k:
 * 1. Shift goal by numParams (to make room for k in the context)
 * 2. Build constructor application: Succ(Var(0))
 * 3. Substitute the (shifted) scrutinee index with the constructor app
 *
 * Returns the case-specific goal and extra hypotheses (params + IH).
 */
function computeCaseGoal(
  goalType: TTerm,
  scrutineeIndex: number, // de Bruijn index of scrutinee in nameCtx (0 = most recent)
  caseNode: CaseNode,
  inductiveInfo: InductiveInfo,
  nameCtx: readonly string[],
  rev: ReverseRegistry,
): { goal: TTerm; extraHyps: TypedHypothesis[]; extraCtx: string[] } | null {
  if (!caseNode.constructorName) return null;

  const ctor = inductiveInfo.constructors.find(c => c.name === caseNode.constructorName);
  if (!ctor) return null;

  const paramNames = caseNode.constructorParamNames ?? [];
  const numParams = paramNames.length;
  const params = peelConstructorParams(ctor.type);

  if (numParams === 0) {
    // Zero-param constructor (e.g., Zero): just substitute scrutinee with Const
    const caseGoal = substTT(scrutineeIndex, mkConstTT(caseNode.constructorName), goalType);
    return { goal: caseGoal, extraHyps: [], extraCtx: [] };
  }

  // Multi-param constructor (e.g., Succ k):
  // 1. Shift goal to make room for constructor params
  const shifted = shiftSurfaceTerm(numParams, goalType, scrutineeIndex);

  // 2. Build constructor application: Succ(Var(numParams-1), ..., Var(0))
  let ctorApp: TTerm = mkConstTT(caseNode.constructorName);
  for (let j = numParams - 1; j >= 0; j--) {
    ctorApp = mkAppTT(ctorApp, mkVarTT(j));
  }

  // 3. Substitute scrutinee (now at shifted index) with constructor app
  const caseGoal = substTT(scrutineeIndex + numParams, ctorApp, shifted);

  // 4. Build extra hypotheses for constructor params
  const extraHyps: TypedHypothesis[] = [];
  const extraCtx: string[] = [];

  for (let j = 0; j < numParams; j++) {
    const pName = paramNames[j] as string;
    extraCtx.unshift(pName);

    if (j < params.length) {
      extraHyps.push({
        name: pName,
        type: renderTerm(params[j].domain, [...extraCtx, ...nameCtx], rev),
      });
    } else {
      extraHyps.push({ name: pName, type: '?' });
    }
  }

  // 5. Add induction hypothesis for the first recursive param
  for (let j = 0; j < Math.min(numParams, params.length); j++) {
    if (isRecursiveParam(params[j].domain, inductiveInfo.name)) {
      // IH: P(k) — substitute scrutinee with Var(j) in the shifted goal
      const ihPre = substTT(scrutineeIndex + numParams, mkVarTT(j), shifted);
      // Shift for the ih binding itself
      const ihType = shiftSurfaceTerm(1, ihPre, 0);
      const ihName = 'ih';
      extraCtx.unshift(ihName);
      extraHyps.push({
        name: ihName,
        type: renderTerm(ihType, [...extraCtx, ...nameCtx], rev),
      });
      break; // Only one IH for now
    }
  }

  return { goal: caseGoal, extraHyps, extraCtx };
}

// ============================================================================
// Tree walking
// ============================================================================

function walkTree(
  node: ProofNode,
  cursorId: ProofNodeId,
  currentType: TTerm,
  hypotheses: readonly TypedHypothesis[],
  nameCtx: readonly string[],  // de Bruijn name context for rendering
  rawTypeCtx: readonly (TTerm | undefined)[],  // raw domain types parallel to nameCtx
  rev: ReverseRegistry,
  inductiveMap?: InductiveMap,
): TypedProofContext | null {
  // Cursor is on this node
  if (node.id === cursorId) {
    const goal = renderGoal(node, currentType, nameCtx, rev);
    return { hypotheses, goal };
  }

  switch (node.tag) {
    case 'hole':
    case 'exact':
      return null;

    case 'intros': {
      // Peel one Pi binder per intro name
      let type = currentType;
      const extHyps: TypedHypothesis[] = [...hypotheses];
      const extCtx: string[] = [...nameCtx];
      const extRawCtx: (TTerm | undefined)[] = [...rawTypeCtx];

      for (const name of node.names) {
        const pi = peelPi(type);
        if (pi) {
          // Skip implicit binders silently — peel until we get a non-implicit
          let current = pi;
          while (current.isImplicit) {
            extCtx.unshift(current.name);
            extRawCtx.unshift(current.domain);
            const next = peelPi(current.body);
            if (!next) break;
            current = next;
          }

          extHyps.push({
            name,
            type: renderTerm(current.domain, extCtx, rev),
            rawType: current.domain,
          });
          extCtx.unshift(name);
          extRawCtx.unshift(current.domain);
          type = current.body;
        } else {
          // No more Pi binders — can't peel further
          extHyps.push({ name, type: '?' });
          extCtx.unshift(name);
          extRawCtx.unshift(undefined);
        }
      }

      return walkTree(node.child, cursorId, type, extHyps, extCtx, extRawCtx, rev, inductiveMap);
    }

    case 'induction': {
      // Find the scrutinee's de Bruijn index and raw type
      const scrIdx = nameCtx.indexOf(node.scrutinee);
      let scrInductiveInfo: InductiveInfo | undefined;

      if (scrIdx >= 0 && inductiveMap) {
        const rawType = rawTypeCtx[scrIdx];
        if (rawType) {
          const headName = extractTypeHead(rawType);
          if (headName) {
            scrInductiveInfo = inductiveMap.get(headName);
          }
        }
      }

      for (const c of node.cases) {
        // Try to compute case-specific goal
        let caseGoalType = currentType;
        let caseHyps = hypotheses;
        let caseCtx = nameCtx;

        if (scrIdx >= 0 && scrInductiveInfo && c.constructorName) {
          const caseResult = computeCaseGoal(
            currentType, scrIdx, c, scrInductiveInfo, nameCtx, rev,
          );
          if (caseResult) {
            caseGoalType = caseResult.goal;
            caseHyps = [...hypotheses, ...caseResult.extraHyps];
            caseCtx = [...caseResult.extraCtx, ...nameCtx];
          }
        }

        // Cursor is on the case header
        if (c.id === cursorId) {
          return {
            hypotheses: caseHyps,
            caseLabel: c.label,
            inductionVar: node.scrutinee,
            goal: renderTerm(caseGoalType, [...caseCtx], rev),
          };
        }
        // Cursor is somewhere inside the case body
        const result = walkTree(c.body, cursorId, caseGoalType, caseHyps, caseCtx,
          [...rawTypeCtx], rev, inductiveMap);
        if (result) {
          return {
            ...result,
            caseLabel: result.caseLabel ?? c.label,
            inductionVar: result.inductionVar ?? node.scrutinee,
          };
        }
      }
      return null;
    }
  }
}

function renderGoal(node: ProofNode, type: TTerm, nameCtx: readonly string[], rev: ReverseRegistry): string {
  switch (node.tag) {
    case 'hole':
      return renderTerm(type, [...nameCtx], rev);
    case 'exact':
      return node.expr;
    default:
      return renderTerm(type, [...nameCtx], rev);
  }
}
