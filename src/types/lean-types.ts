// TypeScript types for Lean 4 structures
// These will eventually be replaced with actual Lean API bindings

export interface LeanType {
  kind: 'type';
  name: string;
  universe?: number;
}

export interface LeanArrow {
  kind: 'arrow';
  domain: LeanExpr;
  codomain: LeanExpr;
}

export interface LeanApp {
  kind: 'app';
  function: LeanExpr;
  argument: LeanExpr;
}

export interface LeanConst {
  kind: 'const';
  name: string;
  universes?: number[];
}

export interface LeanVar {
  kind: 'var';
  index: number;
}

export interface LeanLambda {
  kind: 'lambda';
  name: string;
  type: LeanExpr;
  body: LeanExpr;
}

export interface LeanForall {
  kind: 'forall';
  name: string;
  type: LeanExpr;
  body: LeanExpr;
}

export interface LeanLet {
  kind: 'let';
  name: string;
  type: LeanExpr;
  value: LeanExpr;
  body: LeanExpr;
}

// Union type for all possible Lean expressions
export type LeanExpr =
  | LeanType
  | LeanArrow
  | LeanApp
  | LeanConst
  | LeanVar
  | LeanLambda
  | LeanForall
  | LeanLet;

// Lean environment context
export interface LeanContext {
  assumptions: Map<string, LeanExpr>; // Variable name -> type
  definitions: Map<string, { type: LeanExpr; value?: LeanExpr }>; // Definition name -> type and value
}

// Result of parsing/type checking
export interface LeanParseResult {
  success: boolean;
  expr?: LeanExpr;
  type?: LeanExpr;
  errors?: string[];
  context?: LeanContext;
}

// Mathematical constants and functions we support
export const LEAN_MATH_CONSTANTS = {
  // Real numbers
  'ℝ': { kind: 'const', name: 'Real' } as LeanConst,
  'Real': { kind: 'const', name: 'Real' } as LeanConst,

  // Calculus
  'deriv': { kind: 'const', name: 'deriv' } as LeanConst,
  'integral': { kind: 'const', name: 'integral' } as LeanConst,

  // Basic arithmetic
  'mul': { kind: 'const', name: 'HMul.hMul' } as LeanConst,
  'add': { kind: 'const', name: 'HAdd.hAdd' } as LeanConst,
  'sub': { kind: 'const', name: 'HSub.hSub' } as LeanConst,
  'div': { kind: 'const', name: 'HDiv.hDiv' } as LeanConst,

  // Function application
  'app': { kind: 'const', name: 'Function.comp' } as LeanConst,
} as const;

// Helper types for our specific mathematical expressions
export interface DerivativeExpr {
  kind: 'derivative';
  function: LeanExpr;
  variable: string;
}

export interface MultiplicationExpr {
  kind: 'multiplication';
  left: LeanExpr;
  right: LeanExpr;
}

export interface FunctionApplicationExpr {
  kind: 'function_app';
  function: LeanExpr;
  argument: LeanExpr;
}

// Extended expression type that includes our mathematical constructs
export type MathematicalLeanExpr = LeanExpr | DerivativeExpr | MultiplicationExpr | FunctionApplicationExpr;