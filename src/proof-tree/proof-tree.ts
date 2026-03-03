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
  | UnfoldNode;

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

export function mkInduction(scrutinee: string, cases: readonly CaseNode[]): InductionNode {
  return { tag: 'induction', id: freshProofId(), scrutinee, cases, collapsed: false };
}

export function mkExact(expr: string): ExactNode {
  return { tag: 'exact', id: freshProofId(), expr };
}

export function mkUnfold(name: string, child: ProofNode): UnfoldNode {
  return { tag: 'unfold', id: freshProofId(), name, child };
}

export function mkCase(
  label: string, body: ProofNode,
  constructorName?: string, constructorParamNames?: readonly string[],
  labelLatex?: string,
): CaseNode {
  const node: CaseNode = { tag: 'case', id: freshProofId(), label, body, collapsed: false };
  if (constructorName !== undefined) (node as any).constructorName = constructorName;
  if (constructorParamNames !== undefined) (node as any).constructorParamNames = constructorParamNames;
  if (labelLatex !== undefined) (node as any).labelLatex = labelLatex;
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
      return findNode(root.child, id);
    case 'unfold':
      return findNode(root.child, id);
    case 'induction':
      for (const c of root.cases) {
        const found = findNode(c.body, id);
        if (found) return found;
      }
      return null;
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
      return findCase(root.child, id);
    case 'induction':
      for (const c of root.cases) {
        if (c.id === id) return c;
        const found = findCase(c.body, id);
        if (found) return found;
      }
      return null;
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
      return isCursorInSubtree(node.child, cursorId);
    case 'induction':
      return node.cases.some(c =>
        c.id === cursorId || isCursorInSubtree(c.body, cursorId)
      );
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
      linearizeImpl(node.child, depth + 1, out);
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
    case 'unfold': {
      const newChild = replaceNode(root.child, targetId, replacement);
      return newChild === root.child ? root : { ...root, child: newChild };
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
    case 'unfold': {
      const newChild = updateCase(root.child, caseId, updater);
      return newChild === root.child ? root : { ...root, child: newChild };
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

/** Apply unfold at the cursor (must be a hole). Replaces the hole with an unfold node + child hole. */
export function applyUnfold(state: ProofTreeState, name: string): ProofTreeState | null {
  const node = findNode(state.root, state.cursor.nodeId);
  if (!node || node.tag !== 'hole') return null;

  const childHole = mkHole();
  const unfold = mkUnfold(name, childHole);
  const newRoot = replaceNode(state.root, state.cursor.nodeId, unfold);
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
      return computeContextImpl(node.child, cursorId, hypotheses);

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
