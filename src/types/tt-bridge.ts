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
  mkHole,
  mkVar,
  mkApp,
  mkProp,
  mkLet,
  TT_CONSTANTS,
  prettyPrint,
} from './tt-core';
import { ExpressionNode, LetElement } from './enhanced-focus';

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
export function expressionNodeToTTerm(
  expr: ExpressionNode,
  context: Map<string, number> = new Map()
): TTerm {
  switch (expr.type) {
    case 'variable':
      const varName = String(expr.value);
      if (context.has(varName)) {
        return mkVar(context.get(varName)!);
      }
      // Not in context - treat as a constant (like 'a', 'b', etc.)
      // For now, we'll create a const with Real type
      return {
        tag: 'Const',
        name: varName,
        type: TT_CONSTANTS.Real
      };

    case 'literal':
      // Numbers are constants
      const numValue = String(expr.value);
      return {
        tag: 'Const',
        name: numValue,
        type: TT_CONSTANTS.Real
      };

    case 'binop':
      if (expr.children.length !== 2) {
        throw new Error(`Binary operator ${expr.operator} requires exactly 2 children`);
      }
      const left = expressionNodeToTTerm(expr.children[0], context);
      const right = expressionNodeToTTerm(expr.children[1], context);

      // Create function application: (op left right)
      // For example, a + b becomes (+ a b)
      const opConst: TTerm = {
        tag: 'Const',
        name: expr.operator!,
        type: TT_CONSTANTS.Real // Simplified - operators should have proper function types
      };

      return mkApp(mkApp(opConst, left), right);

    case 'equality':
      // Equality: (eq type left right)
      if (expr.children.length !== 2) {
        throw new Error('Equality requires exactly 2 children');
      }
      const eqLeft = expressionNodeToTTerm(expr.children[0], context);
      const eqRight = expressionNodeToTTerm(expr.children[1], context);

      // eq : Π (A : Type), A → A → Prop
      // We need: (((eq Real) left) right)
      const eqConst = TT_CONSTANTS.Eq;
      return mkApp(mkApp(mkApp(eqConst, TT_CONSTANTS.Real), eqLeft), eqRight);

    case 'unop':
      if (expr.children.length !== 1) {
        throw new Error(`Unary operator ${expr.operator} requires exactly 1 child`);
      }
      const operand = expressionNodeToTTerm(expr.children[0], context);
      const unOpConst: TTerm = {
        tag: 'Const',
        name: expr.operator!,
        type: TT_CONSTANTS.Real
      };
      return mkApp(unOpConst, operand);

    case 'application':
      // Function application: f a b c...
      // children[0] is the function, rest are arguments
      if (expr.children.length === 0) {
        throw new Error('Application requires at least a function');
      }

      // Convert function and all arguments to TT terms
      const func = expressionNodeToTTerm(expr.children[0], context);
      const args = expr.children.slice(1).map(arg => expressionNodeToTTerm(arg, context));

      // Build nested applications: (((f a) b) c)
      let result = func;
      for (const arg of args) {
        result = mkApp(result, arg);
      }
      return result;

    case 'inequality':
      // Handle inequality similar to equality
      // For now, treat as a binary relation
      if (expr.children.length !== 2) {
        throw new Error('Inequality requires exactly 2 children');
      }
      const ineqLeft = expressionNodeToTTerm(expr.children[0], context);
      const ineqRight = expressionNodeToTTerm(expr.children[1], context);

      // Create a constant for the inequality operator
      const ineqOp: TTerm = {
        tag: 'Const',
        name: expr.operator || '<',
        type: TT_CONSTANTS.Real
      };

      return mkApp(mkApp(ineqOp, ineqLeft), ineqRight);

    default:
      throw new Error(`Unsupported expression type: ${expr.type}`);
  }
}

// ============================================================================
// Proof Term Construction for Let-Bindings
// ============================================================================

/**
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
  const propType = mkApp(
    mkApp(
      mkApp(TT_CONSTANTS.Eq, TT_CONSTANTS.Real),
      leftTT
    ),
    goalTT
  );

  // Create initial proof term: a hole with the type
  const holeId = `proof_${letBinding.id}`;
  const proofTerm = mkHole(holeId, propType, []);

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
  const proofTerm = mkHole(holeId, mkProp(), []);

  return {
    letId: letBinding.id,
    letName: letBinding.name,
    propType: mkProp(), // Placeholder
    proofTerm,
    holes: [holeId],
    completed: false
  };
}

// ============================================================================
// Proof Term Updates (as user applies rules)
// ============================================================================

/**
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
  const typeStr = prettyPrint(proof.propType, context);
  const termStr = prettyPrint(proof.proofTerm, context);

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
    body = mkLet(
      `proof${i}`,
      proof.propType,
      proof.proofTerm,
      i === 0 ? { tag: 'Var', index: 0 } : body // Last one refers to itself
    );
  }

  return body;
}
