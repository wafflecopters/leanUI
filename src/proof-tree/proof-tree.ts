/**
 * Immutable proof tree — core data model and pure operations.
 *
 * A proof is a tree of tactic nodes. Each node represents a proof step
 * (intros, induction, exact) and may have children (sub-proofs for cases).
 * The entire state is immutable — every action produces a new state.
 *
 * This module has zero dependencies on the tactics engine or TTK kernel.
 * It operates at the UI/string level for now.
 */

// ============================================================================
// ID Generation
// ============================================================================

export type ProofNodeId = number;

let _nextProofNodeId = 1;
export function freshProofId(): ProofNodeId { return _nextProofNodeId++; }
export function resetProofIds(start = 1): void { _nextProofNodeId = start; }

// ============================================================================
// Data Model
// ============================================================================

export type ProofNode =
  | HoleNode
  | IntrosNode
  | InductionNode
  | ExactNode
  | UnfoldNode
  | FoldNode
  | RewriteNode
  | ApplyNode
  | SimpNode
  | HaveNode
  | SufficesNode;

export interface HoleNode {
  readonly tag: 'hole';
  readonly id: ProofNodeId;
}

export interface IntrosNode {
  readonly tag: 'intros';
  readonly id: ProofNodeId;
  readonly names: readonly string[];
  readonly child: ProofNode;
}

export interface InductionNode {
  readonly tag: 'induction';
  readonly id: ProofNodeId;
  readonly scrutinee: string;
  readonly cases: readonly CaseNode[];
  readonly collapsed: boolean;
  /** true for `cases` tactic (destructuring), false/undefined for `induction` */
  readonly isCases?: boolean;
}

export interface ExactNode {
  readonly tag: 'exact';
  readonly id: ProofNodeId;
  readonly expr: string;
}

export interface UnfoldNode {
  readonly tag: 'unfold';
  readonly id: ProofNodeId;
  /** The definition name to unfold (e.g., 'plus', 'sum'). */
  readonly name: string;
  /** When set, only unfold the Nth occurrence (1-based) of the head constant. */
  readonly occurrence?: number;
  readonly child: ProofNode;
}

export interface FoldNode {
  readonly tag: 'fold';
  readonly id: ProofNodeId;
  /** The definition name to fold (e.g., 'two', 'myZero'). */
  readonly name: string;
  /** When set, only fold the Nth occurrence (1-based) of the definition body. */
  readonly occurrence?: number;
  readonly child: ProofNode;
}

export interface RewriteNode {
  readonly tag: 'rewrite';
  readonly id: ProofNodeId;
  /** The equality lemma name (e.g., 'plusComm'). */
  readonly name: string;
  /** If true, use deep definitional equality for matching (erw vs rw). */
  readonly enhanced?: boolean;
  /** If true, rewrite right-to-left (replace RHS with LHS). */
  readonly reverse: boolean;
  /** 1-based occurrence indices to rewrite (if undefined, rewrite all). */
  readonly occurrences?: readonly number[];
  /** Head constant name of the target subterm (for occurrence-targeted rewrites). */
  readonly targetHead?: string;
  readonly child: ProofNode;
}

export interface ApplyNode {
  readonly tag: 'apply';
  readonly id: ProofNodeId;
  /** The lemma/function name (e.g., 'congSucc'). */
  readonly name: string;
  /** Sub-proofs for each subgoal created by apply. */
  readonly children: readonly ProofNode[];
}

export interface SimpNode {
  readonly tag: 'simp';
  readonly id: ProofNodeId;
  /** Lemma names passed to simp. */
  readonly lemmas: readonly string[];
  /** Individual rewrite/unfold steps discovered by simp. */
  readonly steps: readonly ProofNode[];
  /** Whether the step list is collapsed in the UI. */
  readonly collapsed: boolean;
  /** The continuation proof after simp completes. */
  readonly child: ProofNode;
}

export interface HaveNode {
  readonly tag: 'have';
  readonly id: ProofNodeId;
  /** The hypothesis name (e.g., 'cfd', 'dqb'). */
  readonly name: string;
  /** The proof expression as a string. */
  readonly expr: string;
  /** Optional explicit type annotation as source expression (for display fallback). */
  readonly typeExpr?: string;
  /** Optional kernel-level type term (avoids lossy string roundtrip for proofTree goals). */
  readonly typeKernel?: import('../compiler/kernel').TTKTerm;
  /** Optional interactive proof subtree (alternative to flat expr string).
   *  When present, this subtree proves the have's type interactively via tactics.
   *  The proofTree's goal is the have's type (typeKernel or typeExpr). */
  readonly proofTree?: ProofNode;
  /** The continuation proof after have introduces the binding. */
  readonly child: ProofNode;
}

export interface SufficesNode {
  readonly tag: 'suffices';
  readonly id: ProofNodeId;
  /** The hypothesis name (e.g., 'h'). */
  readonly name: string;
  /** The suffices type expression as a string. */
  readonly typeExpr: string;
  /** The "by" proof — shows original goal follows from h. */
  readonly byProof?: ProofNode;
  /** The continuation proof (proves the suffices type). */
  readonly child: ProofNode;
}

export interface CaseNode {
  readonly tag: 'case';
  readonly id: ProofNodeId;
  readonly label: string;
  readonly body: ProofNode;
  readonly collapsed: boolean;
  /** Constructor name (e.g., 'Zero', 'Succ') — set when induction knows the inductive type */
  readonly constructorName?: string;
  /** Names for constructor parameters (e.g., ['k'] for Succ) */
  readonly constructorParamNames?: readonly string[];
  /** Pre-rendered LaTeX for the case label (e.g., "n = 0" rendered through structured pipeline) */
  readonly labelLatex?: string;
  /** Original (pre-desugar) nested pattern structure, for branches written like
   *  `| MkDPair δF (MkPair posF boundF) =>`. Used by the replay layer to render
   *  the case label through the @syntax registry (so MkDPair can pick up the
   *  user's `\text{witness} $x, \text{and} $y` notation). */
  readonly casePatterns?: readonly import('../compiler/surface').CasePattern[];
}

/** Info needed to create a case with constructor metadata. */
export interface ConstructorCaseInfo {
  readonly label: string;
  readonly constructorName: string;
  readonly paramNames: readonly string[];
  readonly labelLatex?: string;
}

// ============================================================================
// Cursor
// ============================================================================

export interface ProofCursor {
  readonly nodeId: ProofNodeId;
}

// ============================================================================
// State & History
// ============================================================================

export interface ProofTreeState {
  readonly root: ProofNode;
  readonly cursor: ProofCursor;
}

export interface ProofTreeHistory {
  readonly undoStack: readonly ProofTreeState[];
  readonly current: ProofTreeState;
  readonly redoStack: readonly ProofTreeState[];
}

// ============================================================================
// Constructors
// ============================================================================

export function mkHole(): HoleNode {
  return { tag: 'hole', id: freshProofId() };
}

export function mkIntros(names: readonly string[], child: ProofNode): IntrosNode {
  return { tag: 'intros', id: freshProofId(), names, child };
}

export function mkInduction(scrutinee: string, cases: readonly CaseNode[], isCases?: boolean): InductionNode {
  return { tag: 'induction', id: freshProofId(), scrutinee, cases, collapsed: false, isCases };
}

export function mkExact(expr: string): ExactNode {
  return { tag: 'exact', id: freshProofId(), expr };
}

export function mkHave(name: string, expr: string, child: ProofNode, typeExpr?: string, proofTree?: ProofNode, typeKernel?: import('../compiler/kernel').TTKTerm): HaveNode {
  return { tag: 'have', id: freshProofId(), name, expr, child, typeExpr, proofTree, typeKernel };
}

export function mkSuffices(name: string, typeExpr: string, child: ProofNode, byProof?: ProofNode): SufficesNode {
  return { tag: 'suffices', id: freshProofId(), name, typeExpr, byProof, child };
}

export function mkUnfold(name: string, child: ProofNode, occurrence?: number): UnfoldNode {
  return { tag: 'unfold', id: freshProofId(), name, child, occurrence };
}

export function mkFold(name: string, child: ProofNode, occurrence?: number): FoldNode {
  return { tag: 'fold', id: freshProofId(), name, child, occurrence };
}

export function mkRewrite(name: string, child: ProofNode, reverse = false, occurrences?: readonly number[], targetHead?: string, enhanced?: boolean): RewriteNode {
  const node: RewriteNode = { tag: 'rewrite', id: freshProofId(), name, reverse, child };
  if (occurrences !== undefined) (node as any).occurrences = occurrences;
  if (targetHead !== undefined) (node as any).targetHead = targetHead;
  if (enhanced) (node as any).enhanced = true;
  return node;
}

export function mkApply(name: string, children: readonly ProofNode[]): ApplyNode {
  return { tag: 'apply', id: freshProofId(), name, children };
}

export function mkSimp(lemmas: readonly string[], steps: readonly ProofNode[], child: ProofNode): SimpNode {
  return { tag: 'simp', id: freshProofId(), lemmas, steps, collapsed: true, child };
}

/** Format a case label as LaTeX: scrutinee = \text{Ctor}\;p1\;p2 */
function formatCaseLabelLatex(scrutinee: string, ctorName: string, paramNames: readonly string[]): string {
  const escName = (n: string) => n.length === 1 ? n : `\\text{${n}}`;
  const ctorLatex = `\\text{${ctorName}}`;
  if (paramNames.length === 0) return `${escName(scrutinee)} = ${ctorLatex}`;
  const paramsLatex = paramNames.map(escName).join('\\;');
  return `${escName(scrutinee)} = ${ctorLatex}\\;${paramsLatex}`;
}

export function mkCase(
  label: string, body: ProofNode,
  constructorName?: string, constructorParamNames?: readonly string[],
  labelLatex?: string,
  casePatterns?: readonly import('../compiler/surface').CasePattern[],
): CaseNode {
  const node: CaseNode = { tag: 'case', id: freshProofId(), label, body, collapsed: false };
  if (constructorName !== undefined) (node as any).constructorName = constructorName;
  if (constructorParamNames !== undefined) (node as any).constructorParamNames = constructorParamNames;
  if (labelLatex !== undefined) (node as any).labelLatex = labelLatex;
  if (casePatterns !== undefined) (node as any).casePatterns = casePatterns;
  return node;
}

export function createInitialState(): ProofTreeState {
  const root = mkHole();
  return { root, cursor: { nodeId: root.id } };
}

// ============================================================================
// Tree Queries
// ============================================================================

/** Find a ProofNode by ID (does not find CaseNodes — use findCase for those). */
export function findNode(root: ProofNode, id: ProofNodeId): ProofNode | null {
  if (root.id === id) return root;
  switch (root.tag) {
    case 'hole':
    case 'exact':
      return null;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      return findNode(root.child, id);
    case 'have': {
      if (root.proofTree) {
        const found = findNode(root.proofTree, id);
        if (found) return found;
      }
      return findNode(root.child, id);
    }
    case 'suffices': {
      if (root.byProof) {
        const found = findNode(root.byProof, id);
        if (found) return found;
      }
      return findNode(root.child, id);
    }
    case 'apply':
      for (const child of root.children) {
        const found = findNode(child, id);
        if (found) return found;
      }
      return null;
    case 'induction':
      for (const c of root.cases) {
        const found = findNode(c.body, id);
        if (found) return found;
      }
      return null;
    case 'simp': {
      for (const step of root.steps) {
        const found = findNode(step, id);
        if (found) return found;
      }
      return findNode(root.child, id);
    }
  }
}

/** Find a CaseNode by ID. */
export function findCase(root: ProofNode, id: ProofNodeId): CaseNode | null {
  switch (root.tag) {
    case 'hole':
    case 'exact':
      return null;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      return findCase(root.child, id);
    case 'have': {
      if (root.proofTree) {
        const found = findCase(root.proofTree, id);
        if (found) return found;
      }
      return findCase(root.child, id);
    }
    case 'suffices': {
      if (root.byProof) {
        const found = findCase(root.byProof, id);
        if (found) return found;
      }
      return findCase(root.child, id);
    }
    case 'apply':
      for (const child of root.children) {
        const found = findCase(child, id);
        if (found) return found;
      }
      return null;
    case 'induction':
      for (const c of root.cases) {
        if (c.id === id) return c;
        const found = findCase(c.body, id);
        if (found) return found;
      }
      return null;
    case 'simp': {
      for (const step of root.steps) {
        const found = findCase(step, id);
        if (found) return found;
      }
      return findCase(root.child, id);
    }
  }
}

/** Check if a cursor ID lives inside a subtree. */
export function isCursorInSubtree(node: ProofNode, cursorId: ProofNodeId): boolean {
  if (node.id === cursorId) return true;
  switch (node.tag) {
    case 'hole':
    case 'exact':
      return false;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      return isCursorInSubtree(node.child, cursorId);
    case 'have':
      return (!!node.proofTree && isCursorInSubtree(node.proofTree, cursorId)) || isCursorInSubtree(node.child, cursorId);
    case 'suffices':
      return (!!node.byProof && isCursorInSubtree(node.byProof, cursorId)) || isCursorInSubtree(node.child, cursorId);
    case 'apply':
      return node.children.some(child => isCursorInSubtree(child, cursorId));
    case 'induction':
      return node.cases.some(c =>
        c.id === cursorId || isCursorInSubtree(c.body, cursorId)
      );
    case 'simp':
      return node.steps.some(step => isCursorInSubtree(step, cursorId)) ||
        isCursorInSubtree(node.child, cursorId);
  }
}

// ============================================================================
// Linearization — DFS traversal for cursor navigation
// ============================================================================

export interface LinearEntry {
  readonly kind: 'node' | 'case';
  readonly id: ProofNodeId;
  readonly depth: number;
}

export function linearize(root: ProofNode): LinearEntry[] {
  const result: LinearEntry[] = [];
  linearizeImpl(root, 0, result);
  return result;
}

function linearizeImpl(node: ProofNode, depth: number, out: LinearEntry[]): void {
  out.push({ kind: 'node', id: node.id, depth });
  switch (node.tag) {
    case 'hole':
    case 'exact':
      break;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite':
      linearizeImpl(node.child, depth + 1, out);
      break;
    case 'have':
      if (node.proofTree) linearizeImpl(node.proofTree, depth + 1, out);
      linearizeImpl(node.child, depth + 1, out);
      break;
    case 'suffices':
      if (node.byProof) linearizeImpl(node.byProof, depth + 1, out);
      linearizeImpl(node.child, depth + 1, out);
      break;
    case 'apply':
      for (const child of node.children) {
        linearizeImpl(child, depth + 1, out);
      }
      break;
    case 'induction':
      if (!node.collapsed) {
        for (const c of node.cases) {
          out.push({ kind: 'case', id: c.id, depth: depth + 1 });
          if (!c.collapsed) {
            linearizeImpl(c.body, depth + 2, out);
          }
        }
      }
      break;
    case 'simp':
      if (!node.collapsed) {
        for (const step of node.steps) {
          linearizeImpl(step, depth + 1, out);
        }
      }
      linearizeImpl(node.child, depth + 1, out);
      break;
  }
}

// ============================================================================
// Immutable Tree Updates
// ============================================================================

/** Replace a ProofNode by ID, returning new tree. */
export function replaceNode(root: ProofNode, targetId: ProofNodeId, replacement: ProofNode): ProofNode {
  if (root.id === targetId) return replacement;
  switch (root.tag) {
    case 'hole':
    case 'exact':
      return root;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite': {
      const newChild = replaceNode(root.child, targetId, replacement);
      return newChild === root.child ? root : { ...root, child: newChild };
    }
    case 'have': {
      const newProof = root.proofTree ? replaceNode(root.proofTree, targetId, replacement) : undefined;
      const newChild = replaceNode(root.child, targetId, replacement);
      return newProof === root.proofTree && newChild === root.child ? root : { ...root, proofTree: newProof, child: newChild };
    }
    case 'suffices': {
      const newBy = root.byProof ? replaceNode(root.byProof, targetId, replacement) : undefined;
      const newChild = replaceNode(root.child, targetId, replacement);
      return newBy === root.byProof && newChild === root.child ? root : { ...root, byProof: newBy, child: newChild };
    }
    case 'apply': {
      let changed = false;
      const newChildren = root.children.map(child => {
        const newChild = replaceNode(child, targetId, replacement);
        if (newChild !== child) changed = true;
        return newChild;
      });
      return changed ? { ...root, children: newChildren } : root;
    }
    case 'induction': {
      let changed = false;
      const newCases = root.cases.map(c => {
        const newBody = replaceNode(c.body, targetId, replacement);
        if (newBody !== c.body) { changed = true; return { ...c, body: newBody }; }
        return c;
      });
      return changed ? { ...root, cases: newCases } : root;
    }
    case 'simp': {
      let changed = false;
      const newSteps = root.steps.map(step => {
        const newStep = replaceNode(step, targetId, replacement);
        if (newStep !== step) changed = true;
        return newStep;
      });
      const newChild = replaceNode(root.child, targetId, replacement);
      if (newChild !== root.child) changed = true;
      return changed ? { ...root, steps: newSteps, child: newChild } : root;
    }
  }
}

/** Update a CaseNode by ID via an updater function. */
export function updateCase(
  root: ProofNode,
  caseId: ProofNodeId,
  updater: (c: CaseNode) => CaseNode,
): ProofNode {
  switch (root.tag) {
    case 'hole':
    case 'exact':
      return root;
    case 'intros':
    case 'unfold':
    case 'fold':
    case 'rewrite': {
      const newChild = updateCase(root.child, caseId, updater);
      return newChild === root.child ? root : { ...root, child: newChild };
    }
    case 'have': {
      const newProof = root.proofTree ? updateCase(root.proofTree, caseId, updater) : undefined;
      const newChild = updateCase(root.child, caseId, updater);
      return newProof === root.proofTree && newChild === root.child ? root : { ...root, proofTree: newProof, child: newChild };
    }
    case 'suffices': {
      const newBy = root.byProof ? updateCase(root.byProof, caseId, updater) : undefined;
      const newChild = updateCase(root.child, caseId, updater);
      return newBy === root.byProof && newChild === root.child ? root : { ...root, byProof: newBy, child: newChild };
    }
    case 'apply': {
      let changed = false;
      const newChildren = root.children.map(child => {
        const newChild = updateCase(child, caseId, updater);
        if (newChild !== child) changed = true;
        return newChild;
      });
      return changed ? { ...root, children: newChildren } : root;
    }
    case 'induction': {
      let changed = false;
      const newCases = root.cases.map(c => {
        if (c.id === caseId) {
          changed = true;
          return updater(c);
        }
        const newBody = updateCase(c.body, caseId, updater);
        if (newBody !== c.body) { changed = true; return { ...c, body: newBody }; }
        return c;
      });
      return changed ? { ...root, cases: newCases } : root;
    }
    case 'simp': {
      let changed = false;
      const newSteps = root.steps.map(step => {
        const newStep = updateCase(step, caseId, updater);
        if (newStep !== step) changed = true;
        return newStep;
      });
      const newChild = updateCase(root.child, caseId, updater);
      if (newChild !== root.child) changed = true;
      return changed ? { ...root, steps: newSteps, child: newChild } : root;
    }
  }
}

// ============================================================================
// Tactic Operations
// ============================================================================

/** Apply intros at the cursor (must be a hole). */
export function applyIntros(state: ProofTreeState, names: readonly string[]): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const intros = mkIntros(names, childHole);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, intros);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Apply induction at the cursor (must be a hole). */
export function applyInduction(
  state: ProofTreeState,
  scrutinee: string,
  caseLabels: readonly string[],
): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const cases = caseLabels.map(label => mkCase(label, mkHole()));
  const induction = mkInduction(scrutinee, cases);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, induction);

  // Cursor → first case's body hole
  const firstBody = cases.length > 0 ? cases[0].body : null;
  const cursorId = firstBody ? firstBody.id : induction.id;
  return { root: newRoot, cursor: { nodeId: cursorId } };
}

/** Apply induction with constructor metadata at the cursor (must be a hole). */
export function applyInductionWithCtors(
  state: ProofTreeState,
  scrutinee: string,
  ctorInfos: readonly ConstructorCaseInfo[],
): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const cases = ctorInfos.map(info =>
    mkCase(info.label, mkHole(), info.constructorName, info.paramNames, info.labelLatex)
  );
  const induction = mkInduction(scrutinee, cases);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, induction);

  const firstBody = cases.length > 0 ? cases[0].body : null;
  const cursorId = firstBody ? firstBody.id : induction.id;
  return { root: newRoot, cursor: { nodeId: cursorId } };
}

/** Apply have at the cursor (must be a hole). Replaces the hole with a have node + child hole. */
export function applyHave(state: ProofTreeState, name: string, expr: string): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const have = mkHave(name, expr, childHole);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, have);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Insert a have node BEFORE a target node. The new have wraps the target:
 *  parent → target  becomes  parent → newHave(name, expr, child: target) */
export function insertHaveBefore(state: ProofTreeState, targetNodeId: ProofNodeId, name: string, expr: string, typeExpr?: string, proofTree?: ProofNode, typeKernel?: import('../compiler/kernel').TTKTerm): ProofTreeState | null {
  const target = findNode(state.root, targetNodeId);
  if (!target) return null;
  const newHave = mkHave(name, expr, target, typeExpr, proofTree, typeKernel);
  const newRoot = replaceNode(state.root, targetNodeId, newHave);
  return { root: newRoot, cursor: state.cursor };
}

/** Edit a have node's expression. Returns new state or null if node not found. */
export function editHaveExpr(state: ProofTreeState, haveNodeId: ProofNodeId, newExpr: string): ProofTreeState | null {
  function updateNode(root: ProofNode): ProofNode | null {
    if (root.id === haveNodeId && root.tag === 'have') {
      return { ...root, expr: newExpr };
    }
    if ('child' in root && (root as any).child) {
      const newChild = updateNode((root as any).child);
      if (newChild) return { ...root, child: newChild } as any;
    }
    if ('children' in root && (root as any).children) {
      for (let i = 0; i < (root as any).children.length; i++) {
        const newChild = updateNode((root as any).children[i]);
        if (newChild) {
          const newChildren = [...(root as any).children];
          newChildren[i] = newChild;
          return { ...root, children: newChildren } as any;
        }
      }
    }
    if ('cases' in root && (root as any).cases) {
      for (let i = 0; i < (root as any).cases.length; i++) {
        const c = (root as any).cases[i];
        const newBody = updateNode(c.body);
        if (newBody) {
          const newCases = [...(root as any).cases];
          newCases[i] = { ...c, body: newBody };
          return { ...root, cases: newCases } as any;
        }
      }
    }
    if (root.tag === 'suffices' && root.byProof) {
      const newBy = updateNode(root.byProof);
      if (newBy) return { ...root, byProof: newBy };
    }
    return null;
  }
  const newRoot = updateNode(state.root);
  return newRoot ? { ...state, root: newRoot } : null;
}

/** Edit a have node's name. Returns new state or null if node not found. */
export function editHaveName(state: ProofTreeState, haveNodeId: ProofNodeId, newName: string): ProofTreeState | null {
  // Find the old name first
  const haveNode = findNode(state.root, haveNodeId);
  if (!haveNode || haveNode.tag !== 'have') return null;
  const oldName = haveNode.name;

  // Replace occurrences of oldName as a token in expression strings throughout the subtree
  function replaceNameInExpr(expr: string): string {
    // Replace whole-word occurrences: match oldName bounded by word boundaries or parens/spaces
    return expr.replace(new RegExp(`(?<=^|[\\s()])${escapeRegExp(oldName)}(?=$|[\\s()])`, 'g'), newName);
  }

  function rewriteSubtree(node: ProofNode): ProofNode {
    switch (node.tag) {
      case 'exact': return { ...node, expr: replaceNameInExpr(node.expr) };
      case 'have': return { ...node, expr: replaceNameInExpr(node.expr), child: rewriteSubtree(node.child), proofTree: node.proofTree ? rewriteSubtree(node.proofTree) : undefined };
      case 'intros': return { ...node, child: rewriteSubtree(node.child) };
      case 'unfold': return { ...node, child: rewriteSubtree(node.child) };
      case 'fold': return { ...node, child: rewriteSubtree(node.child) };
      case 'rewrite': return { ...node, child: rewriteSubtree(node.child) };
      case 'simp': return { ...node, child: rewriteSubtree(node.child) };
      case 'apply': return { ...node, children: node.children.map(rewriteSubtree) };
      case 'induction': return { ...node, cases: node.cases.map(c => ({ ...c, body: rewriteSubtree(c.body) })) };
      case 'suffices': return { ...node, child: rewriteSubtree(node.child), byProof: node.byProof ? rewriteSubtree(node.byProof) : undefined };
      default: return node;
    }
  }

  function updateNode(root: ProofNode): ProofNode | null {
    if (root.id === haveNodeId && root.tag === 'have') {
      return { ...root, name: newName, child: rewriteSubtree(root.child) };
    }
    if ('child' in root && (root as any).child) {
      const newChild = updateNode((root as any).child);
      if (newChild) return { ...root, child: newChild } as any;
    }
    if ('children' in root && (root as any).children) {
      for (let i = 0; i < (root as any).children.length; i++) {
        const newChild = updateNode((root as any).children[i]);
        if (newChild) {
          const newChildren = [...(root as any).children];
          newChildren[i] = newChild;
          return { ...root, children: newChildren } as any;
        }
      }
    }
    if ('cases' in root && (root as any).cases) {
      for (let i = 0; i < (root as any).cases.length; i++) {
        const c = (root as any).cases[i];
        const newBody = updateNode(c.body);
        if (newBody) {
          const newCases = [...(root as any).cases];
          newCases[i] = { ...c, body: newBody };
          return { ...root, cases: newCases } as any;
        }
      }
    }
    if (root.tag === 'suffices' && root.byProof) {
      const newBy = updateNode(root.byProof);
      if (newBy) return { ...root, byProof: newBy };
    }
    return null;
  }
  const newRoot = updateNode(state.root);
  return newRoot ? { ...state, root: newRoot } : null;
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/** Apply unfold at the cursor (must be a hole). Replaces the hole with an unfold node + child hole. */
export function applyUnfold(state: ProofTreeState, name: string, occurrence?: number): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const unfold = mkUnfold(name, childHole, occurrence);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, unfold);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Apply fold at the cursor (must be a hole). Replaces the hole with a fold node + child hole. */
export function applyFold(state: ProofTreeState, name: string, occurrence?: number): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const fold = mkFold(name, childHole, occurrence);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, fold);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Apply rewrite at the cursor (must be a hole). Replaces the hole with a rewrite node + child hole. */
export function applyRewrite(
  state: ProofTreeState, name: string, reverse = false, occurrences?: readonly number[], targetHead?: string,
): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const rewrite = mkRewrite(name, childHole, reverse, occurrences, targetHead);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, rewrite);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Apply "apply" at the cursor (must be a hole). Replaces the hole with an apply node + child holes.
 *  When numChildren=0 (the apply closes the goal with no remaining subgoals),
 *  no child holes are created and the cursor moves to the apply node itself. */
export function applyApplyTactic(state: ProofTreeState, name: string, numChildren = 1): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const children = Array.from({ length: Math.max(0, numChildren) }, () => mkHole());
  const apply = mkApply(name, children);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, apply);
  return { root: newRoot, cursor: { nodeId: children.length > 0 ? children[0].id : apply.id } };
}

/** Apply simp at the cursor (must be a hole). Replaces the hole with a simp node containing steps + child hole. */
export function applySimp(
  state: ProofTreeState,
  lemmas: readonly string[],
  steps: readonly ProofNode[],
): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const simp = mkSimp(lemmas, steps, childHole);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, simp);
  return { root: newRoot, cursor: { nodeId: childHole.id } };
}

/** Apply exact at the cursor (must be a hole). */
export function applyExact(state: ProofTreeState, expr: string): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const exact = mkExact(expr);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, exact);
  return { root: newRoot, cursor: { nodeId: exact.id } };
}

// ============================================================================
// Case Operations
// ============================================================================

/** Add a case to an induction node. */
export function addCase(
  state: ProofTreeState,
  inductionId: ProofNodeId,
  label: string,
): ProofTreeState | null {
  const node = findNode(state.root, inductionId);
  if (!node || node.tag !== 'induction') return null;

  const newBody = mkHole();
  const newCase = mkCase(label, newBody);
  const updatedNode: InductionNode = { ...node, cases: [...node.cases, newCase] };
  const newRoot = replaceNode(state.root, inductionId, updatedNode);
  return { root: newRoot, cursor: { nodeId: newBody.id } };
}

/** Remove a case from an induction node (blocks removal of last case). */
export function removeCase(
  state: ProofTreeState,
  inductionId: ProofNodeId,
  caseIndex: number,
): ProofTreeState | null {
  const node = findNode(state.root, inductionId);
  if (!node || node.tag !== 'induction') return null;
  if (node.cases.length <= 1) return null;
  if (caseIndex < 0 || caseIndex >= node.cases.length) return null;

  const removedCase = node.cases[caseIndex];
  const newCases = node.cases.filter((_, i) => i !== caseIndex);
  const updatedNode: InductionNode = { ...node, cases: newCases };
  const newRoot = replaceNode(state.root, inductionId, updatedNode);

  // Fix cursor if it was inside the removed case
  if (removedCase.id === state.cursor.nodeId || isCursorInSubtree(removedCase.body, state.cursor.nodeId)) {
    const fallbackIdx = Math.min(caseIndex, newCases.length - 1);
    return { root: newRoot, cursor: { nodeId: newCases[fallbackIdx].body.id } };
  }

  return { root: newRoot, cursor: state.cursor };
}

/** Toggle collapse on a case node. Fixes cursor if it gets hidden. */
export function toggleCollapse(state: ProofTreeState, caseId: ProofNodeId): ProofTreeState {
  const caseNode = findCase(state.root, caseId);
  if (!caseNode) return state;

  const newCollapsed = !caseNode.collapsed;
  const newRoot = updateCase(state.root, caseId, c => ({ ...c, collapsed: newCollapsed }));

  // If collapsing and cursor is inside the case body, move cursor to case header
  let cursor = state.cursor;
  if (newCollapsed && isCursorInSubtree(caseNode.body, state.cursor.nodeId)) {
    cursor = { nodeId: caseId };
  }

  return { root: newRoot, cursor };
}

/** Toggle collapse on a simp node's step list. Fixes cursor if it gets hidden. */
export function toggleSimpCollapse(state: ProofTreeState, nodeId: ProofNodeId): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'simp') return null;

  const newCollapsed = !node.collapsed;
  const updatedNode: SimpNode = { ...node, collapsed: newCollapsed };
  const newRoot = replaceNode(state.root, nodeId, updatedNode);

  // If collapsing and cursor is inside a step, move cursor to simp header
  let cursor = state.cursor;
  if (newCollapsed) {
    const cursorInSteps = node.steps.some(step => isCursorInSubtree(step, state.cursor.nodeId));
    if (cursorInSteps) {
      cursor = { nodeId: nodeId };
    }
  }

  return { root: newRoot, cursor };
}

/** Toggle collapse on an induction node. Fixes cursor if it gets hidden. */
export function toggleInductionCollapse(state: ProofTreeState, nodeId: ProofNodeId): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'induction') return null;

  const newCollapsed = !node.collapsed;
  const updatedNode: InductionNode = { ...node, collapsed: newCollapsed };
  const newRoot = replaceNode(state.root, nodeId, updatedNode);

  // If collapsing and cursor is inside any case, move cursor to induction header
  let cursor = state.cursor;
  if (newCollapsed) {
    const cursorInside = node.cases.some(c =>
      c.id === state.cursor.nodeId || isCursorInSubtree(c.body, state.cursor.nodeId)
    );
    if (cursorInside) {
      cursor = { nodeId: nodeId };
    }
  }

  return { root: newRoot, cursor };
}

// ============================================================================
// Cursor Navigation
// ============================================================================

export function moveCursorUp(state: ProofTreeState): ProofTreeState {
  const entries = linearize(state.root);
  const idx = entries.findIndex(e => e.id === state.cursor.nodeId);
  if (idx <= 0) return state;
  return { ...state, cursor: { nodeId: entries[idx - 1].id } };
}

export function moveCursorDown(state: ProofTreeState): ProofTreeState {
  const entries = linearize(state.root);
  const idx = entries.findIndex(e => e.id === state.cursor.nodeId);
  if (idx < 0 || idx >= entries.length - 1) return state;
  return { ...state, cursor: { nodeId: entries[idx + 1].id } };
}

// ============================================================================
// Editing Operations
// ============================================================================

export function editIntroName(
  state: ProofTreeState, nodeId: ProofNodeId, nameIndex: number, newName: string,
): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'intros') return null;
  if (nameIndex < 0 || nameIndex >= node.names.length) return null;
  const newNames = [...node.names];
  newNames[nameIndex] = newName;
  const newRoot = replaceNode(state.root, nodeId, { ...node, names: newNames });
  return { root: newRoot, cursor: state.cursor };
}

export function addIntroName(
  state: ProofTreeState, nodeId: ProofNodeId, name: string,
): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'intros') return null;
  const newRoot = replaceNode(state.root, nodeId, { ...node, names: [...node.names, name] });
  return { root: newRoot, cursor: state.cursor };
}

export function removeIntroName(
  state: ProofTreeState, nodeId: ProofNodeId, nameIndex: number,
): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'intros') return null;
  if (nameIndex < 0 || nameIndex >= node.names.length) return null;
  if (node.names.length <= 1) return null; // must keep at least one
  const newNames = [...node.names];
  newNames.splice(nameIndex, 1);
  const newRoot = replaceNode(state.root, nodeId, { ...node, names: newNames });
  return { root: newRoot, cursor: state.cursor };
}

export function editScrutinee(
  state: ProofTreeState, nodeId: ProofNodeId, newScrutinee: string,
): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'induction') return null;
  const newRoot = replaceNode(state.root, nodeId, { ...node, scrutinee: newScrutinee });
  return { root: newRoot, cursor: state.cursor };
}

export function editExact(
  state: ProofTreeState, nodeId: ProofNodeId, newExpr: string,
): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node || node.tag !== 'exact') return null;
  const newRoot = replaceNode(state.root, nodeId, { ...node, expr: newExpr });
  return { root: newRoot, cursor: state.cursor };
}

export function editCaseLabel(
  state: ProofTreeState, caseId: ProofNodeId, newLabel: string,
): ProofTreeState {
  const newRoot = updateCase(state.root, caseId, c => ({ ...c, label: newLabel }));
  return { root: newRoot, cursor: state.cursor };
}

/** Rename a constructor parameter in a case node and regenerate the label. */
export function editCaseParamName(
  state: ProofTreeState, caseId: ProofNodeId, paramIndex: number, newName: string,
): ProofTreeState | null {
  // Find the parent induction to get the scrutinee name
  const findInductionParent = (root: ProofNode, targetCaseId: ProofNodeId): { scrutinee: string } | null => {
    switch (root.tag) {
      case 'induction':
        if (root.cases.some(c => c.id === targetCaseId)) return { scrutinee: root.scrutinee };
        for (const c of root.cases) {
          const r = findInductionParent(c.body, targetCaseId);
          if (r) return r;
        }
        return null;
      case 'intros':
      case 'unfold':
      case 'fold':
      case 'rewrite':
        return findInductionParent(root.child, targetCaseId);
      case 'have': {
        if (root.proofTree) {
          const r = findInductionParent(root.proofTree, targetCaseId);
          if (r) return r;
        }
        return findInductionParent(root.child, targetCaseId);
      }
      case 'suffices': {
        if (root.byProof) {
          const r = findInductionParent(root.byProof, targetCaseId);
          if (r) return r;
        }
        return findInductionParent(root.child, targetCaseId);
      }
      case 'apply':
        for (const child of root.children) {
          const r = findInductionParent(child, targetCaseId);
          if (r) return r;
        }
        return null;
      case 'simp':
        for (const step of root.steps) {
          const r = findInductionParent(step, targetCaseId);
          if (r) return r;
        }
        return findInductionParent(root.child, targetCaseId);
      default:
        return null;
    }
  };

  const parent = findInductionParent(state.root, caseId);
  if (!parent) return null;

  const newRoot = updateCase(state.root, caseId, c => {
    if (!c.constructorParamNames || paramIndex < 0 || paramIndex >= c.constructorParamNames.length) return c;
    const newParamNames = [...c.constructorParamNames];
    newParamNames[paramIndex] = newName;
    // Regenerate plain-text label
    const label = newParamNames.length > 0
      ? `${parent.scrutinee} = ${c.constructorName} ${newParamNames.join(' ')}`
      : `${parent.scrutinee} = ${c.constructorName}`;
    const labelLatex = c.constructorName
      ? formatCaseLabelLatex(parent.scrutinee, c.constructorName, newParamNames)
      : undefined;
    return { ...c, constructorParamNames: newParamNames, label, labelLatex };
  });
  return { root: newRoot, cursor: state.cursor };
}

// ============================================================================
// Structural Operations
// ============================================================================

/** Revert any non-hole node back to a fresh hole. */
export function clearNode(state: ProofTreeState, nodeId: ProofNodeId): ProofTreeState | null {
  const node = findNode(state.root, nodeId);
  if (!node) return null;
  if (node.tag === 'hole') return null;

  const newHole = mkHole();
  const newRoot = replaceNode(state.root, nodeId, newHole);
  return { root: newRoot, cursor: { nodeId: newHole.id } };
}

// ============================================================================
// Context Computation — derive hypotheses + goal from path to cursor
// ============================================================================

export interface ContextEntry {
  readonly name: string;
  readonly source: 'intro' | 'case-ih';
}

export interface ProofContext {
  readonly hypotheses: readonly ContextEntry[];
  readonly caseLabel?: string;
  readonly inductionVar?: string;
  readonly goalDescription: string;
}

/**
 * Walk the tree from root to the cursor node, collecting hypotheses and
 * case information encountered along the way.
 */
export function computeContext(root: ProofNode, cursorId: ProofNodeId): ProofContext | null {
  return computeContextImpl(root, cursorId, []);
}

function computeContextImpl(
  node: ProofNode,
  cursorId: ProofNodeId,
  hypotheses: readonly ContextEntry[],
): ProofContext | null {
  // Cursor is on this node
  if (node.id === cursorId) {
    return {
      hypotheses,
      goalDescription: node.tag === 'hole' ? '?' : node.tag === 'exact' ? node.expr : '',
    };
  }

  switch (node.tag) {
    case 'hole':
    case 'exact':
      return null;

    case 'intros': {
      const extended: ContextEntry[] = [
        ...hypotheses,
        ...node.names.map(name => ({ name, source: 'intro' as const })),
      ];
      return computeContextImpl(node.child, cursorId, extended);
    }

    case 'unfold':
    case 'fold':
    case 'rewrite':
      return computeContextImpl(node.child, cursorId, hypotheses);

    case 'have': {
      // proofTree proves the have's type — h is NOT in scope yet
      if (node.proofTree) {
        const ptResult = computeContextImpl(node.proofTree, cursorId, hypotheses);
        if (ptResult) return ptResult;
      }
      // child continues after have — h IS in scope
      const extended: ContextEntry[] = [
        ...hypotheses,
        { name: node.name, source: 'intro' as const },
      ];
      return computeContextImpl(node.child, cursorId, extended);
    }
    case 'suffices': {
      const extended: ContextEntry[] = [
        ...hypotheses,
        { name: node.name, source: 'intro' as const },
      ];
      // byProof has h in scope (proves original goal given h : T)
      if (node.byProof) {
        const byResult = computeContextImpl(node.byProof, cursorId, extended);
        if (byResult) return byResult;
      }
      // child proves the suffices type (h NOT in scope — that's what's being proved)
      return computeContextImpl(node.child, cursorId, hypotheses);
    }

    case 'simp':
      // Steps are read-only sub-nodes; check child continuation
      return computeContextImpl(node.child, cursorId, hypotheses);

    case 'apply':
      for (const child of node.children) {
        const result = computeContextImpl(child, cursorId, hypotheses);
        if (result) return result;
      }
      return null;

    case 'induction': {
      for (const c of node.cases) {
        // Cursor is on the case header
        if (c.id === cursorId) {
          return {
            hypotheses,
            caseLabel: c.label,
            inductionVar: node.scrutinee,
            goalDescription: '',
          };
        }
        // Cursor is somewhere inside the case body
        const result = computeContextImpl(c.body, cursorId, hypotheses);
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

// ============================================================================
// History (Undo / Redo)
// ============================================================================

export function createHistory(state: ProofTreeState): ProofTreeHistory {
  return { undoStack: [], current: state, redoStack: [] };
}

/** Push a structural change. Clears redo stack. */
export function pushState(history: ProofTreeHistory, newState: ProofTreeState): ProofTreeHistory {
  return {
    undoStack: [...history.undoStack, history.current],
    current: newState,
    redoStack: [],
  };
}

/** Update current state without creating an undo point (cursor-only moves). */
export function updateCurrent(history: ProofTreeHistory, newState: ProofTreeState): ProofTreeHistory {
  return { ...history, current: newState };
}

export function undo(history: ProofTreeHistory): ProofTreeHistory {
  if (history.undoStack.length === 0) return history;
  const newUndo = history.undoStack.slice(0, -1);
  const prev = history.undoStack[history.undoStack.length - 1];
  return {
    undoStack: newUndo,
    current: prev,
    redoStack: [...history.redoStack, history.current],
  };
}

export function redo(history: ProofTreeHistory): ProofTreeHistory {
  if (history.redoStack.length === 0) return history;
  const newRedo = history.redoStack.slice(0, -1);
  const next = history.redoStack[history.redoStack.length - 1];
  return {
    undoStack: [...history.undoStack, history.current],
    current: next,
    redoStack: newRedo,
  };
}
