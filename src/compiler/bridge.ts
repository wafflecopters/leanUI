/**
 * TT Bridge: Connecting UI ExpressionNodes to TT proof terms
 *
 * This module provides the translation layer between:
 * 1. UI representation (ExpressionNode - the AST from user input)
 * 2. TT representation (TTerm - typed terms with De Bruijn indices)
 *
 * Key responsibilities:
 * - Convert ExpressionNode to TTerm (UI → TT)
 * - Create proof terms for let-bindings
 * - Manage holes and proof state
 * - Track proof construction as user applies rules
 */

import {
  TTerm,
  mkHoleTT,
  mkVarTT,
  mkAppTT,
  mkPropTT,
  mkLetTT,
  mkEq,
  mkTrans,
  TT_CONSTANTS,
  prettyPrintTT,
  replaceHoleTT,
} from './surface';
import { ExpressionNode, LetElement } from '../types/enhanced-focus';

// Alias for backward compatibility
const fillHole = replaceHoleTT;

// ============================================================================
// UI → TT Conversion
// ============================================================================

/**
 * Convert a UI ExpressionNode to a TT term.
 *
 * This is a simple initial version that handles:
 * - Variables
 * - Literals (as constants)
 * - Binary operations (+, *, etc.)
 * - Equality
 *
 * Context provides the mapping from variable names to De Bruijn indices.
 */
/**
 * Convert ExpressionNode focus path to TTerm path.
 * 
 * ExpressionNode and TTerm have different tree structures:
 * - ExpressionNode for `a + b`: binop with children [a, b]
 * - TTerm for `a + b`: App(App(+, a), b)
 * 
 * So ExpressionNode path [0] (left child) maps to TTerm path [0, 1]
 * And ExpressionNode path [1] (right child) maps to TTerm path [1]
 */
export function expressionPathToTTermPath(
  expr: ExpressionNode,
  exprPath: number[]
): number[] {
  if (exprPath.length === 0) {
    return [];
  }

  const [head, ...rest] = exprPath;

  switch (expr.type) {
    case 'binop':
      if (head === 0) {
        // Left child: in TTerm, this is [0, 1] (fn.arg of App(App(op, left), right))
        const leftChild = expr.children[0];
        const remainingPath = expressionPathToTTermPath(leftChild, rest);
        return [0, 1, ...remainingPath];
      } else if (head === 1) {
        // Right child: in TTerm, this is [1] (arg of App(App(op, left), right))
        const rightChild = expr.children[1];
        const remainingPath = expressionPathToTTermPath(rightChild, rest);
        return [1, ...remainingPath];
      }
      throw new Error(`Invalid binop child index: ${head}`);

    case 'unop':
      if (head === 0) {
        // Unary operator child: in TTerm, this is [1] (arg of App(op, child))
        const child = expr.children[0];
        const remainingPath = expressionPathToTTermPath(child, rest);
        return [1, ...remainingPath];
      }
      throw new Error(`Invalid unop child index: ${head}`);

    case 'application':
      // Application: each child is just [head, ...]
      // This maps directly since both are application nodes
      if (head >= 0 && head < expr.children.length) {
        const child = expr.children[head];
        const remainingPath = expressionPathToTTermPath(child, rest);
        // In TTerm, applications are right-associative nested Apps
        // For now, assume direct mapping (may need refinement)
        return [head, ...remainingPath];
      }
      throw new Error(`Invalid application child index: ${head}`);

    case 'equality':
      if (head === 0) {
        // Left side of equality: in TTerm eq is App(App(App(eq, type), left), right)
        // So left is [0, 1] (the fn.arg of the middle App)
        const leftChild = expr.children[0];
        const remainingPath = expressionPathToTTermPath(leftChild, rest);
        return [0, 1, ...remainingPath];
      } else if (head === 1) {
        // Right side: [1]
        const rightChild = expr.children[1];
        const remainingPath = expressionPathToTTermPath(rightChild, rest);
        return [1, ...remainingPath];
      }
      throw new Error(`Invalid equality child index: ${head}`);

    case 'variable':
    case 'literal':
    case 'hole':
      // Leaf nodes - no further path
      return [];

    default:
      // For unknown types, pass through directly (may not be correct)
      return exprPath;
  }
}

export function expressionNodeToTTerm(
  expr: ExpressionNode,
  context: Map<string, number> = new Map(),
  typeContext: Map<string, TTerm> = new Map()  // NEW: maps variable names to their types
): TTerm {
  switch (expr.type) {
    case 'variable':
      const varName = String(expr.value);
      if (context.has(varName)) {
        return mkVarTT(context.get(varName)!);
      }
      return {
        tag: 'Const',
        name: varName,
      };

    case 'literal':
      // Numbers are constants
      const numValue = String(expr.value);
      return {
        tag: 'Const',
        name: numValue,
      };

    case 'binop':
      if (expr.children.length !== 2) {
        throw new Error(`Binary operator ${expr.operator} requires exactly 2 children`);
      }
      const left = expressionNodeToTTerm(expr.children[0], context, typeContext);
      const right = expressionNodeToTTerm(expr.children[1], context, typeContext);

      // Create function application: (op left right)
      // For example, a + b becomes (+ a b)
      const opConst: TTerm = {
        tag: 'Const',
        name: expr.operator!,
      };

      return mkAppTT(mkAppTT(opConst, left), right);

    case 'equality':
      // Equality: (eq type left right)
      if (expr.children.length !== 2) {
        throw new Error('Equality requires exactly 2 children');
      }
      const eqLeft = expressionNodeToTTerm(expr.children[0], context, typeContext);
      const eqRight = expressionNodeToTTerm(expr.children[1], context, typeContext);

      // eq : Π (A : Type), A → A → Prop
      // Infer the type by finding a variable in the expression and getting its type from typeContext
      const inferredType = (() => {
        // Helper: extract first variable name from ExpressionNode
        const extractFirstVar = (node: ExpressionNode): string | null => {
          if (node.type === 'variable' && typeof node.value === 'string') {
            return node.value;
          }
          for (const child of node.children) {
            const varName = extractFirstVar(child);
            if (varName) return varName;
          }
          return null;
        };

        const varName = extractFirstVar(expr.children[0]);
        if (varName && typeContext.has(varName)) {
          return typeContext.get(varName)!;
        }
        return TT_CONSTANTS.Real; // Fallback
      })();

      const eqConst = TT_CONSTANTS.Eq;
      return mkAppTT(mkAppTT(mkAppTT(eqConst, inferredType), eqLeft), eqRight);

    case 'unop':
      if (expr.children.length !== 1) {
        throw new Error(`Unary operator ${expr.operator} requires exactly 1 child`);
      }
      const operand = expressionNodeToTTerm(expr.children[0], context, typeContext);
      const unOpConst: TTerm = {
        tag: 'Const',
        name: expr.operator!,
      };
      return mkAppTT(unOpConst, operand);

    case 'application':
      // Function application: f a b c...
      // children[0] is the function, rest are arguments
      if (expr.children.length === 0) {
        throw new Error('Application requires at least a function');
      }

      // Convert function and all arguments to TT terms
      const func = expressionNodeToTTerm(expr.children[0], context, typeContext);
      const args = expr.children.slice(1).map(arg => expressionNodeToTTerm(arg, context, typeContext));

      // Build nested applications: (((f a) b) c)
      let result = func;
      for (const arg of args) {
        result = mkAppTT(result, arg);
      }
      return result;

    case 'inequality':
      // Handle inequality similar to equality
      // For now, treat as a binary relation
      if (expr.children.length !== 2) {
        throw new Error('Inequality requires exactly 2 children');
      }
      const ineqLeft = expressionNodeToTTerm(expr.children[0], context, typeContext);
      const ineqRight = expressionNodeToTTerm(expr.children[1], context, typeContext);

      // Create a constant for the inequality operator
      const ineqOp: TTerm = {
        tag: 'Const',
        name: expr.operator || '<',
      };

      return mkAppTT(mkAppTT(ineqOp, ineqLeft), ineqRight);

    case 'hole':
      // A hole in the UI AST represents a proof hole
      // Convert to a TT Hole term
      // The hole's value field contains the hole identifier
      // The hole's children[0] contains the expression we're working on (for display)
      const holeId = String(expr.value || 'unknown_hole');

      // For now, we'll create a hole with Prop type
      // In the future, we might want to infer the type from the expression inside
      return mkHoleTT(holeId, mkPropTT(), Array.from(context.entries()).map(([name]) => ({
        name,
        type: TT_CONSTANTS.Real  // Simplified - should track actual types
      })));

    default:
      throw new Error(`Unsupported expression type: ${expr.type}`);
  }
}

// ============================================================================
// Proof Term Construction for Let-Bindings (DEPRECATED)
// ============================================================================

/**
 * @deprecated This interface is deprecated. Use TermDefinition instead.
 * 
 * Create a TT proof term structure for a let-binding claim.
 *
 * For a claim like: thm: a+a = 2*a
 *
 * We create:
 * ```
 * Let (defType: a+a = 2*a)
 *     (defVal: _incomplete_ "id0" (refl {x=(a+a)}))
 *     (body: ...)
 * ```
 *
 * The key insight:
 * - The TYPE is the proposition we're proving (a+a = 2*a)
 * - The VALUE starts as a hole with an initial proof term (refl for equality start)
 * - As the user applies rules, we fill in the hole progressively
 * 
 * NEW ARCHITECTURE:
 * - Let-bindings are now part of the TermDefinition.value
 * - They are nested using the BLet binder kind
 * - No need for separate LetProofTerm tracking
 */
export interface LetProofTerm {
  letId: string;           // ID of the let-binding
  letName: string;         // Name (e.g., "thm")
  propType: TTerm;         // The proposition type (e.g., a+a = 2*a)
  proofTerm: TTerm;        // Current proof term (starts with holes)
  holes: string[];         // IDs of unfilled holes
  completed: boolean;      // Whether all holes are filled
}

/**
 * @deprecated Use the new equality proof system with EqualityProofState instead.
 * 
 * Initialize a proof term for an equality claim.
 *
 * For equality chaining, we start with:
 * - Type: left = goal (e.g., a+a = 2*a)
 * - Term: hole "proof" with expected type (left = goal)
 *
 * As user applies transformations:
 * - We build up an equality chain using transitivity
 * - Each step is: trans (step1) (step2)
 * - Each atomic step might be: refl, or an axiom/rule application
 */
export function createEqualityProofTerm(
  letBinding: LetElement,
  goal: ExpressionNode
): LetProofTerm {
  // Get the left side (starting point) from the claim
  const left = letBinding.value.children[0];
  const leftTT = expressionNodeToTTerm(left);
  const goalTT = expressionNodeToTTerm(goal);

  // Create the proposition type: left = goal
  const propType = mkAppTT(
    mkAppTT(
      mkAppTT(TT_CONSTANTS.Eq, TT_CONSTANTS.Real),
      leftTT
    ),
    goalTT
  );

  // Create initial proof term: a hole with the type
  const holeId = `proof_${letBinding.id}`;
  const proofTerm = mkHoleTT(holeId, propType, []);

  return {
    letId: letBinding.id,
    letName: letBinding.name,
    propType,
    proofTerm,
    holes: [holeId],
    completed: false
  };
}

/**
 * @deprecated Use the new TermDefinition-based architecture instead.
 * 
 * Create a proof term for an induction claim.
 *
 * For induction on n with P(n), we create:
 * ```
 * nat_elim
 *   (λn. P(n))           -- motive
 *   ?base                -- base case hole
 *   (λk. λIH. ?step)     -- inductive step with IH
 *   n                    -- value being inducted on
 * ```
 */
export function createInductionProofTerm(
  letBinding: LetElement,
  _inductionVar: string,
  _baseValue: number,
  _predicate: ExpressionNode
): LetProofTerm {
  // TODO: Implement induction proof term construction
  // For now, return a placeholder with a hole

  const holeId = `induction_${letBinding.id}`;
  const proofTerm = mkHoleTT(holeId, mkPropTT(), []);

  return {
    letId: letBinding.id,
    letName: letBinding.name,
    propType: mkPropTT(), // Placeholder
    proofTerm,
    holes: [holeId],
    completed: false
  };
}

// ============================================================================
// Proof Term Updates (as user applies rules) - DEPRECATED
// ============================================================================

/**
 * @deprecated Use the equality proof system with applyEqualityStep instead.
 * 
 * Apply a transformation step to the proof term.
 *
 * This is called when the user applies a rule in the UI.
 * We need to update the proof term to reflect this transformation.
 *
 * For equality chaining:
 * - Each step is justified by a rule (e.g., "add both sides", "factor", etc.)
 * - These become proof term constructors (axioms or derived rules)
 * - We chain them with transitivity
 *
 * @param currentProof - The current proof term state
 * @param from - Expression before transformation
 * @param to - Expression after transformation
 * @param rule - Rule applied (name and params)
 * @returns Updated proof term
 */
export function applyProofStep(
  currentProof: LetProofTerm,
  _from: ExpressionNode,
  _to: ExpressionNode,
  _rule: { name: string; id: string; params?: any }
): LetProofTerm {
  // For now, we keep the proof term as a hole
  // In a full implementation, we would:
  // 1. Create a proof term for this specific step (based on the rule)
  // 2. Combine it with the existing proof using transitivity
  // 3. Update hole status

  // Placeholder: just return current state
  return currentProof;
}

/**
 * @deprecated No longer needed - proof completion is tracked in TermDefinition.
 * 
 * Check if the proof is complete (goal reached).
 *
 * For equality chaining, we check if:
 * - Current expression matches the goal
 * - All holes are filled
 */
export function checkProofComplete(
  _currentProof: LetProofTerm,
  currentExpression: ExpressionNode,
  goal: ExpressionNode
): boolean {
  // Simple check: string representation matches
  const currentStr = currentExpression.raw;
  const goalStr = goal.raw;

  return currentStr === goalStr;
}

// ============================================================================
// Pretty Printing for Debug
// ============================================================================

/**
 * Pretty-print a let proof term for display
 */
export function prettyPrintLetProof(proof: LetProofTerm, context: string[] = []): string {
  const typeStr = prettyPrintTT(proof.propType, context);
  const termStr = prettyPrintTT(proof.proofTerm, context);

  return `${proof.letName} : ${typeStr}\n${proof.letName} = ${termStr}`;
}

/**
 * Convert multiple let-bindings to a full proof term structure
 */
export function buildFullProofTerm(proofs: LetProofTerm[]): TTerm | null {
  if (proofs.length === 0) return null;

  // Build nested let expressions
  // let thm1 : Type1 := proof1 in
  // let thm2 : Type2 := proof2 in
  // ...

  let body: TTerm = proofs[proofs.length - 1].proofTerm;

  for (let i = proofs.length - 1; i >= 0; i--) {
    const proof = proofs[i];
    body = mkLetTT(
      `proof${i}`,
      proof.propType,
      proof.proofTerm,
      i === 0 ? { tag: 'Var', index: 0 } : body // Last one refers to itself
    );
  }

  return body;
}

// ============================================================================
// Equality Proof Construction
// ============================================================================

/**
 * State for tracking an equality proof as it's being constructed.
 * 
 * This tracks a proof of (startExpr = targetExpr) as the user applies
 * transformation steps.
 */
export interface EqualityProofState {
  /** The starting expression (where we begin the chain) */
  startExpr: TTerm;

  /** The target expression (where we want to end up) */
  targetExpr: TTerm;

  /** Current position in the equality chain */
  currentExpr: TTerm;

  /** The proof term being built (may contain holes) */
  proofTerm: TTerm;

  /** ID of the current hole to fill (empty if proof complete) */
  currentHoleId: string;

  /** Whether the proof is complete (no holes remaining) */
  isComplete: boolean;
}

/**
 * Start an equality proof.
 * 
 * Creates initial state for proving startExpr = targetExpr.
 * For "left" direction, we start at startExpr and work toward targetExpr.
 * For "right" direction, we start at targetExpr and work toward startExpr,
 * then use symmetry.
 * 
 * @param startExpr - Starting expression
 * @param targetExpr - Target expression to reach
 * @param direction - Which side to start from
 * @returns Initial equality proof state
 */
export function startEqualityProof(
  startExpr: TTerm,
  targetExpr: TTerm,
  direction: 'left' | 'right'
): EqualityProofState {
  if (direction === 'left') {
    // Prove: startExpr = targetExpr
    // Start with a hole for the entire proof
    const holeId = 'eq_proof_init';
    const proofTerm = mkHoleTT(holeId, mkEq(startExpr, targetExpr), []);

    return {
      startExpr,
      targetExpr,
      currentExpr: startExpr,
      proofTerm,
      currentHoleId: holeId,
      isComplete: false
    };
  } else {
    // Prove: targetExpr = startExpr (then we'll use sym to get startExpr = targetExpr)
    // For "right" mode, we actually want to build the proof in reverse
    const holeId = 'eq_proof_init';
    const proofTerm = mkHoleTT(holeId, mkEq(targetExpr, startExpr), []);

    return {
      startExpr: targetExpr,
      targetExpr: startExpr,
      currentExpr: targetExpr,
      proofTerm,
      currentHoleId: holeId,
      isComplete: false
    };
  }
}

/**
 * Apply a transformation step to an equality proof.
 * 
 * Given a proof state and a transformation that proves currentExpr = newExpr,
 * extend the proof using transitivity.
 * 
 * @param state - Current proof state
 * @param ruleName - Name of the rule being applied
 * @param newExpr - The expression after transformation
 * @returns Updated proof state
 */
export function applyEqualityStep(
  state: EqualityProofState,
  ruleName: string,
  newExpr: TTerm
): EqualityProofState {
  // The rule proves: state.currentExpr = newExpr
  // For now, represent the rule as a constant
  // 
  // TODO: Build actual proof term from rule application
  // TODO: Detect when rule is applied to subexpression and use cong
  //       For example, if currentExpr = (a + b) and user transforms a → 1*a
  //       then newExpr = (1*a + b), we should build:
  //       cong (λx => x + b) (introduce_one_mul a)
  //       instead of just (introduce_one_mul)
  const ruleProof: TTerm = {
    tag: 'Const',
    name: ruleName,
  };

  // Check if we've reached the target
  if (termsEqual(newExpr, state.targetExpr)) {
    // Final step! Fill the hole with just the rule proof
    const finalProof = fillHole(
      state.proofTerm,
      state.currentHoleId,
      ruleProof
    );

    return {
      ...state,
      currentExpr: newExpr,
      proofTerm: finalProof,
      currentHoleId: '',
      isComplete: true
    };
  }

  // Not at target yet, use transitivity
  // trans : (current = new) → (new = target) → (current = target)
  const newHoleId = `eq_step_${crypto.randomUUID()}`;
  const restProof = mkHoleTT(newHoleId, mkEq(newExpr, state.targetExpr), []);

  // Build: trans ruleProof restProof
  const transProof = mkTrans(ruleProof, restProof);

  // Fill the current hole with this transitivity proof
  const newProofTerm = fillHole(
    state.proofTerm,
    state.currentHoleId,
    transProof
  );

  return {
    ...state,
    currentExpr: newExpr,
    proofTerm: newProofTerm,
    currentHoleId: newHoleId,
    isComplete: false
  };
}

/**
 * Check if two terms are structurally equal.
 * 
 * This is a simple structural equality check.
 * In a real system, we'd use alpha-equivalence and normalization.
 * 
 * @param a - First term
 * @param b - Second term
 * @returns True if terms are equal
 */
function termsEqual(a: TTerm, b: TTerm): boolean {
  if (a.tag !== b.tag) return false;

  switch (a.tag) {
    case 'Var':
      return b.tag === 'Var' && a.index === b.index;

    case 'Const':
      return b.tag === 'Const' && a.name === b.name;

    case 'Sort':
      return b.tag === 'Sort' && a.level === b.level;

    case 'Hole':
      return b.tag === 'Hole' && a.id === b.id;

    case 'App':
      return b.tag === 'App' &&
        termsEqual(a.fn, b.fn) &&
        termsEqual(a.arg, b.arg);

    case 'Binder':
      if (b.tag !== 'Binder') return false;
      if (a.name !== b.name) return false;
      if (a.binderKind.tag !== b.binderKind.tag) return false;
      // Handle optional domain (both undefined, or both defined and equal)
      if (a.domain === undefined && b.domain === undefined) {
        // OK
      } else if (a.domain !== undefined && b.domain !== undefined) {
        if (!termsEqual(a.domain, b.domain)) return false;
      } else {
        return false; // One undefined, one defined
      }
      if (!termsEqual(a.body, b.body)) return false;
      if (a.binderKind.tag === 'BLetTT' && b.binderKind.tag === 'BLetTT') {
        return termsEqual(a.binderKind.defVal, b.binderKind.defVal);
      }
      return true;

    case 'Annot':
      return b.tag === 'Annot' &&
        termsEqual(a.term, b.term) &&
        termsEqual(a.type, b.type);

    case 'Match':
      if (b.tag !== 'Match') return false;
      if (!termsEqual(a.scrutinee, b.scrutinee)) return false;
      if (a.clauses.length !== b.clauses.length) return false;
      for (let i = 0; i < a.clauses.length; i++) {
        if (!termsEqual(a.clauses[i].rhs, b.clauses[i].rhs)) return false;
      }
      return true;

    case 'ULevel':
      return b.tag === 'ULevel';

    case 'ULit':
      return b.tag === 'ULit' && a.n === b.n;

    case 'UOmega':
      return b.tag === 'UOmega';

    case 'MultiBinder':
      if (b.tag !== 'MultiBinder') return false;
      if (a.names.length !== b.names.length) return false;
      for (let i = 0; i < a.names.length; i++) {
        if (a.names[i] !== b.names[i]) return false;
      }
      if (a.binderKind.tag !== b.binderKind.tag) return false;
      if (!termsEqual(a.domain, b.domain)) return false;
      return termsEqual(a.body, b.body);

    case 'AbsurdMarker':
      return b.tag === 'AbsurdMarker';

    case 'WithClause':
      return b.tag === 'WithClause';
  }
}
