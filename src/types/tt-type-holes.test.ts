/**
 * Tests for Type Hole System
 * 
 * Verifies that unknown types create holes instead of assuming Real
 */

import {
  mkHole,
  mkType,
  mkConst,
  mkProp,
  mkEq,
  mkApp,
  mkPi,
  prettyPrint,
  createRootTermDefinition,
  TT_CONSTANTS
} from './tt-core';
import { expressionNodeToTTerm } from './tt-bridge';
import { ExpressionNode } from './enhanced-focus';

/**
 * Simple assertion helper
 */
function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
}

/**
 * Run a test with a description
 */
function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

// ============================================================================
// Type Hole Creation Tests
// ============================================================================

test('creates a type hole with Type_1 as its type', () => {
  const typeHole = mkHole('type_a', mkType(1), []);

  assert(typeHole.tag === 'Hole', 'should be a Hole');
  if (typeHole.tag === 'Hole') {
    assert(typeHole.id === 'type_a', 'hole ID should be type_a');
    assert(typeHole.type.tag === 'Sort', 'type should be Sort');
    if (typeHole.type.tag === 'Sort') {
      assert(typeHole.type.level === 1, 'level should be 1');
    }
  }
});

test('builds goal with type holes for unknown variable types', () => {
  // Create a type hole for 'a'
  const typeHole = mkHole('type_a', mkType(1), []);
  const hypotheses: Array<[string, any]> = [['a', typeHole]];

  // Goal: a + a = 2 * a (where a has unknown type)
  const aWithTypeHole = mkConst('a', typeHole);
  const goalExpr = mkEq(
    mkApp(mkApp(mkConst('+', mkProp()), aWithTypeHole), aWithTypeHole),
    mkApp(mkApp(mkConst('*', mkProp()), mkConst('2', TT_CONSTANTS.Real)), aWithTypeHole)
  );

  const termDef = createRootTermDefinition('_root', hypotheses, goalExpr, 'proof', []);

  // The type should contain the hole
  const printed = prettyPrint(termDef.type);
  assert(printed.includes('?type_a'), 'printed type should contain ?type_a');
});

test('distinguishes type holes from concrete types', () => {
  const typeHole = mkHole('type_a', mkType(1), []);
  const realType = TT_CONSTANTS.Real;

  assert(typeHole.tag === 'Hole', 'type hole should be Hole');
  assert(realType.tag === 'Const', 'Real should be Const');
});

// ============================================================================
// Expression Conversion with Type Context Tests
// ============================================================================

test('uses type from context instead of assuming Real', () => {
  // Create expression: a + a
  const aNode: ExpressionNode = {
    id: 'a1',
    type: 'variable',
    value: 'a',
    raw: 'a',
    children: []
  };

  const expr: ExpressionNode = {
    id: 'expr1',
    type: 'binop',
    operator: '+',
    raw: 'a + a',
    children: [aNode, { ...aNode, id: 'a2' }]
  };

  // Create type context with a type hole for 'a'
  const typeHole = mkHole('type_a', mkType(1), []);
  const typeContext = new Map<string, any>();
  typeContext.set('a', typeHole);

  // Convert with type context
  const ttTerm = expressionNodeToTTerm(expr, new Map(), typeContext);

  // The 'a' constants should have the type hole, not Real
  // Structure: (+ a a) where both 'a' have type ?type_a
  assert(ttTerm.tag === 'App', 'result should be App');
  if (ttTerm.tag === 'App') {
    assert(ttTerm.arg.tag === 'Const', 'arg should be Const');
    if (ttTerm.arg.tag === 'Const') {
      assert(ttTerm.arg.name === 'a', 'arg name should be "a"');
      assert(ttTerm.arg.type.tag === 'Hole', 'arg type should be Hole');
      if (ttTerm.arg.type.tag === 'Hole') {
        assert(ttTerm.arg.type.id === 'type_a', 'hole ID should be type_a');
      }
    }
  }
});

test('falls back to Real if variable not in type context', () => {
  const expr: ExpressionNode = {
    id: 'expr1',
    type: 'variable',
    value: 'x',
    raw: 'x',
    children: []
  };

  // Empty type context - should fall back to Real
  const ttTerm = expressionNodeToTTerm(expr, new Map(), new Map());

  assert(ttTerm.tag === 'Const', 'should be Const');
  if (ttTerm.tag === 'Const') {
    assert(ttTerm.name === 'x', 'name should be "x"');
    assert(ttTerm.type === TT_CONSTANTS.Real, 'should fall back to Real');
  }
});

// ============================================================================
// Pi Type with Type Holes Tests
// ============================================================================

test('creates dependent function type with type hole', () => {
  // (a : ?type_a) → Prop
  const typeHole = mkHole('type_a', mkType(1), []);
  const piType = mkPi(typeHole, mkProp(), 'a');

  assert(piType.tag === 'Binder', 'should be Binder');
  if (piType.tag === 'Binder') {
    assert(piType.binderKind.tag === 'BPi', 'should be Pi');
    assert(piType.domain.tag === 'Hole', 'domain should be Hole');
    assert(piType.body.tag === 'Sort', 'body should be Sort (Prop)');
  }
});

test('prints Pi type with type hole correctly', () => {
  const typeHole = mkHole('type_a', mkType(1), []);
  const piType = mkPi(typeHole, mkProp(), 'a');

  const printed = prettyPrint(piType);
  assert(printed.includes('?type_a'), 'should contain ?type_a');
  assert(printed.includes('a'), 'should contain variable name');
});

console.log('\n✅ All type hole tests passed!');
