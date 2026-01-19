/**
 * Tests for name resolution (symbol validation)
 */

import { mkConstTT, mkTypeTT, mkPiTT, mkVarTT, mkLambdaTT, mkAppTT } from '../compiler/surface';
import {
  emptySymbolContext,
  addSymbol,
  isSymbolDefined,
  validateTerm,
  validateDeclaration,
  validateDeclarations
} from './name-resolution';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assert(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

console.log('\n' + '='.repeat(80));
console.log('NAME RESOLUTION TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Symbol Context Tests
// ============================================================================

test('emptySymbolContext: creates empty context', () => {
  const ctx = emptySymbolContext();
  assert(ctx.size === 0, 'Empty context has no symbols');
  assert(!isSymbolDefined(ctx, 'Nat'), 'No symbols are defined');
});

test('addSymbol: adds symbol to context', () => {
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  assert(isSymbolDefined(ctx, 'Nat'), 'Nat is defined');
  assert(!isSymbolDefined(ctx, 'Bool'), 'Bool is not defined');
});

test('addSymbol: does not mutate original context', () => {
  const ctx1 = emptySymbolContext();
  const ctx2 = addSymbol(ctx1, 'Nat');

  assert(!isSymbolDefined(ctx1, 'Nat'), 'Original context unchanged');
  assert(isSymbolDefined(ctx2, 'Nat'), 'New context has symbol');
});

test('addSymbol: can build up context incrementally', () => {
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');
  ctx = addSymbol(ctx, 'Bool');
  ctx = addSymbol(ctx, 'List');

  assert(isSymbolDefined(ctx, 'Nat'), 'Nat defined');
  assert(isSymbolDefined(ctx, 'Bool'), 'Bool defined');
  assert(isSymbolDefined(ctx, 'List'), 'List defined');
  assert(!isSymbolDefined(ctx, 'Vec'), 'Vec not defined');
});

// ============================================================================
// Term Validation Tests - Success Cases
// ============================================================================

test('validateTerm: Var succeeds (no symbols)', () => {
  const term = mkVarTT(0);
  const ctx = emptySymbolContext();

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'Var validates successfully');
});

test('validateTerm: Sort succeeds (no symbols)', () => {
  const term = mkTypeTT(0);
  const ctx = emptySymbolContext();

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'Sort validates successfully');
});

test('validateTerm: Const succeeds when symbol is defined', () => {
  const term = mkConstTT('Nat');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'Const validates when symbol exists');
});

test('validateTerm: Pi with defined symbol succeeds', () => {
  // (n : Nat) -> Nat
  const term = mkPiTT(mkConstTT('Nat'), mkVarTT(0), 'n');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'Pi validates when all symbols exist');
});

test('validateTerm: Lambda with defined symbols succeeds', () => {
  // λ(n : Nat). Nat
  const term = mkLambdaTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'Lambda validates when all symbols exist');
});

test('validateTerm: App with defined symbols succeeds', () => {
  // f x (where both f and x are constants)
  const term = mkAppTT(mkConstTT('f'), mkConstTT('x'));
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'f');
  ctx = addSymbol(ctx, 'x');

  const result = validateTerm(term, ctx);
  assert(result.success === true, 'App validates when all symbols exist');
});

// ============================================================================
// Term Validation Tests - Failure Cases
// ============================================================================

test('validateTerm: Const fails when symbol undefined', () => {
  const term = mkConstTT('Nat');
  const ctx = emptySymbolContext();

  const result = validateTerm(term, ctx);
  assert(result.success === false, 'Validation fails for undefined symbol');
  if (!result.success) {
    assert(result.errors.length === 1, 'Exactly one error');
    assert(result.errors[0].symbolName === 'Nat', 'Error mentions Nat');
    assert(result.errors[0].message.includes('Undefined symbol'), 'Error message correct');
  }
});

test('validateTerm: Pi fails when domain symbol undefined', () => {
  // (n : Nat) -> Bool  (Nat undefined, Bool defined)
  const term = mkPiTT(mkConstTT('Nat'), mkConstTT('Bool'), 'n');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Bool');

  const result = validateTerm(term, ctx);
  assert(result.success === false, 'Validation fails when domain symbol undefined');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error for Nat');
    assert(result.errors[0].symbolName === 'Nat', 'Error is for Nat');
  }
});

test('validateTerm: Pi fails when body symbol undefined', () => {
  // (n : Nat) -> Bool  (Nat defined, Bool undefined)
  const term = mkPiTT(mkConstTT('Nat'), mkConstTT('Bool'), 'n');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateTerm(term, ctx);
  assert(result.success === false, 'Validation fails when body symbol undefined');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error for Bool');
    assert(result.errors[0].symbolName === 'Bool', 'Error is for Bool');
  }
});

test('validateTerm: collects multiple errors', () => {
  // (a : Foo) -> Bar  (both undefined)
  const term = mkPiTT(mkConstTT('Foo'), mkConstTT('Bar'), 'a');
  const ctx = emptySymbolContext();

  const result = validateTerm(term, ctx);
  assert(result.success === false, 'Validation fails');
  if (!result.success) {
    assert(result.errors.length === 2, 'Two errors collected');
    const symbolNames = result.errors.map(e => e.symbolName).sort();
    assert(symbolNames[0] === 'Bar', 'Bar error collected');
    assert(symbolNames[1] === 'Foo', 'Foo error collected');
  }
});

test('validateTerm: App collects errors from fn and arg', () => {
  // foo bar (both undefined)
  const term = mkAppTT(mkConstTT('Foo'), mkConstTT('bar'));
  const ctx = emptySymbolContext();

  const result = validateTerm(term, ctx);
  assert(result.success === false, 'Validation fails');
  if (!result.success) {
    assert(result.errors.length === 2, 'Two errors');
    const symbolNames = result.errors.map(e => e.symbolName).sort();
    assert(symbolNames[0] === 'bar', 'bar error');
    assert(symbolNames[1] === 'foo', 'foo error');
  }
});

// ============================================================================
// Declaration Validation Tests
// ============================================================================

test('validateDeclaration: type signature only', () => {
  // id : Nat -> Nat
  const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateDeclaration('id', declType, undefined, undefined, ctx);
  assert(result.success === true, 'Declaration validates');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'id'), 'id added to context');
    assert(isSymbolDefined(result.value, 'Nat'), 'Nat still in context');
  }
});

test('validateDeclaration: definition only', () => {
  // id = λ(x : Nat). x
  const declValue = mkLambdaTT(mkConstTT('Nat'), mkVarTT(0), 'x');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateDeclaration('id', undefined, declValue, undefined, ctx);
  assert(result.success === true, 'Declaration validates');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'id'), 'id added to context');
  }
});

test('validateDeclaration: both type and value', () => {
  // id : Nat -> Nat
  // id = λ(x : Nat). x
  const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
  const declValue = mkLambdaTT(mkConstTT('Nat'), mkVarTT(0), 'x');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateDeclaration('id', declType, declValue, undefined, ctx);
  assert(result.success === true, 'Declaration validates');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'id'), 'id added to context');
  }
});

test('validateDeclaration: self-reference allowed', () => {
  // rec : Nat -> Nat
  // rec = λ(x : Nat). rec x  (recursive call to itself)
  const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
  const declValue = mkLambdaTT(mkConstTT('Nat'), mkAppTT(mkConstTT('rec'), mkVarTT(0)), 'x');
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateDeclaration('rec', declType, declValue, undefined, ctx);
  assert(result.success === true, 'Self-reference validates');
});

test('validateDeclaration: inductive with constructors', () => {
  // inductive Bool : Type where
  //   True : Bool
  //   False : Bool
  const declType = mkTypeTT(0);
  const constructors = [
    { name: 'True', type: mkConstTT('Bool') },
    { name: 'False', type: mkConstTT('Bool') }
  ];
  const ctx = emptySymbolContext();

  const result = validateDeclaration('Bool', declType, undefined, constructors, ctx);
  assert(result.success === true, 'Inductive validates');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'Bool'), 'Bool in context');
    assert(isSymbolDefined(result.value, 'True'), 'True in context');
    assert(isSymbolDefined(result.value, 'False'), 'False in context');
  }
});

test('validateDeclaration: fails when type uses undefined symbol', () => {
  // bad : Foo -> Bar  (both undefined)
  const declType = mkPiTT(mkConstTT('Foo'), mkConstTT('Bar'), 'x');
  const ctx = emptySymbolContext();

  const result = validateDeclaration('bad', declType, undefined, undefined, ctx);
  assert(result.success === false, 'Validation fails');
  if (!result.success) {
    assert(result.errors.length === 2, 'Two errors');
  }
});

test('validateDeclaration: fails when value uses undefined symbol', () => {
  // id = λ(x : Foo). x  (Foo undefined)
  const declValue = mkLambdaTT(mkConstTT('Foo'), mkVarTT(0), 'x');
  const ctx = emptySymbolContext();

  const result = validateDeclaration('id', undefined, declValue, undefined, ctx);
  assert(result.success === false, 'Validation fails');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error');
    assert(result.errors[0].symbolName === 'Foo', 'Error for Foo');
  }
});

// ============================================================================
// Multiple Declarations Tests
// ============================================================================

test('validateDeclarations: empty list succeeds', () => {
  const result = validateDeclarations([]);
  assert(result.success === true, 'Empty list validates');
  if (result.success) {
    assert(result.value.size === 0, 'Context is empty');
  }
});

test('validateDeclarations: single declaration', () => {
  // id : Type -> Type
  const declType = mkPiTT(mkTypeTT(0), mkTypeTT(0), 'x');
  const declarations = [
    { name: 'id', type: declType }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === true, 'Validates successfully');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'id'), 'id in final context');
  }
});

test('validateDeclarations: forward reference within block', () => {
  // id : Nat -> Nat
  // test = id
  const declarations = [
    { name: 'Nat', type: mkTypeTT(0) },
    { name: 'id', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x') },
    { name: 'test', value: mkConstTT('id') }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === true, 'Forward reference works');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'Nat'), 'Nat in context');
    assert(isSymbolDefined(result.value, 'id'), 'id in context');
    assert(isSymbolDefined(result.value, 'test'), 'test in context');
  }
});

test('validateDeclarations: continues after errors', () => {
  // bad : Foo  (Foo undefined)
  // good : Type
  const declarations = [
    { name: 'bad', type: mkConstTT('Foo') },
    { name: 'good', type: mkTypeTT(0) }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Fails due to error in first decl');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error collected');
    assert(result.errors[0].symbolName === 'Foo', 'Error for Foo');
  }
});

test('validateDeclarations: collects all errors', () => {
  // bad1 : Foo  (undefined)
  // bad2 : Bar  (undefined)
  const declarations = [
    { name: 'bad1', type: mkConstTT('Foo') },
    { name: 'bad2', type: mkConstTT('Bar') }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Fails');
  if (!result.success) {
    assert(result.errors.length === 2, 'Two errors');
    const symbols = result.errors.map(e => e.symbolName).sort();
    assert(symbols[0] === 'Bar', 'Bar error');
    assert(symbols[1] === 'Foo', 'Foo error');
  }
});

test('validateDeclarations: uses initial context', () => {
  // Start with Nat already defined
  let initialCtx = emptySymbolContext();
  initialCtx = addSymbol(initialCtx, 'Nat');

  // id : Nat -> Nat
  const declarations = [
    { name: 'id', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x') }
  ];

  const result = validateDeclarations(declarations, initialCtx);
  assert(result.success === true, 'Validates with initial context');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'Nat'), 'Nat still in context');
    assert(isSymbolDefined(result.value, 'id'), 'id added to context');
  }
});

// ============================================================================
// Real-World Examples
// ============================================================================

test('Real-world: Nat and plus function', () => {
  // inductive Nat : Type where
  //   Zero : Nat
  //   Succ : Nat -> Nat
  //
  // plus : Nat -> Nat -> Nat

  const declarations = [
    {
      name: 'Nat',
      type: mkTypeTT(0),
      constructors: [
        { name: 'Zero', type: mkConstTT('Nat') },
        { name: 'Succ', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n') }
      ]
    },
    {
      name: 'plus',
      type: mkPiTT(mkConstTT('Nat'), mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'b'), 'a')
    }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === true, 'Real example validates');
  if (result.success) {
    assert(isSymbolDefined(result.value, 'Nat'), 'Nat defined');
    assert(isSymbolDefined(result.value, 'Zero'), 'Zero defined');
    assert(isSymbolDefined(result.value, 'Succ'), 'Succ defined');
    assert(isSymbolDefined(result.value, 'plus'), 'plus defined');
  }
});

test('Real-world: typo in type (Na instead of Nat)', () => {
  // plus : Na -> Nat -> Nat  (typo: Na)

  const declarations = [
    {
      name: 'Nat',
      type: mkTypeTT(0)
    },
    {
      name: 'plus',
      type: mkPiTT(mkConstTT('Na'), mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'b'), 'a')
    }
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Detects typo');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error');
    assert(result.errors[0].symbolName === 'Na', 'Error for Na');
    assert(result.errors[0].message.includes('Undefined symbol'), 'Helpful message');
  }
});

// ============================================================================
// Duplicate Name Detection Tests
// ============================================================================

test('validateDeclaration: fails when symbol already defined', () => {
  // Define Nat, then try to redefine it
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const result = validateDeclaration('Nat', mkTypeTT(0), undefined, undefined, ctx);
  assert(result.success === false, 'Fails for duplicate symbol');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error');
    assert(result.errors[0].symbolName === 'Nat', 'Error for Nat');
    assert(result.errors[0].message.includes('already defined'), 'Error says already defined');
  }
});

test('validateDeclaration: fails when constructor name conflicts with existing symbol', () => {
  // Define True, then try to define Bool with True constructor
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'True');

  const constructors = [
    { name: 'True', type: mkConstTT('Bool') },
    { name: 'False', type: mkConstTT('Bool') }
  ];

  const result = validateDeclaration('Bool', mkTypeTT(0), undefined, constructors, ctx);
  assert(result.success === false, 'Fails for duplicate constructor');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error');
    assert(result.errors[0].symbolName === 'True', 'Error for True');
    assert(result.errors[0].message.includes('already defined'), 'Error says already defined');
  }
});

test('validateDeclaration: fails when inductive name conflicts with existing symbol', () => {
  // Define Nat type, then try to redefine as inductive
  let ctx = emptySymbolContext();
  ctx = addSymbol(ctx, 'Nat');

  const constructors = [
    { name: 'Zero', type: mkConstTT('Nat') },
    { name: 'Succ', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n') }
  ];

  const result = validateDeclaration('Nat', mkTypeTT(0), undefined, constructors, ctx);
  assert(result.success === false, 'Fails for duplicate inductive name');
  if (!result.success) {
    assert(result.errors.some(e => e.symbolName === 'Nat'), 'Error for Nat');
    assert(result.errors.some(e => e.message.includes('already defined')), 'Error says already defined');
  }
});

test('validateDeclarations: fails when second declaration redefines first', () => {
  // foo : Type
  // foo = Type  (same name - should fail)
  // Note: This is different from foo : Type followed by foo = value which is a valid pattern match style
  // Here we're testing when declarations are passed separately to validateDeclarations
  const declarations = [
    { name: 'foo', type: mkTypeTT(1) },
    { name: 'foo', type: mkTypeTT(0) }  // Redefinition
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Fails for redefinition');
  if (!result.success) {
    assert(result.errors.length === 1, 'One error');
    assert(result.errors[0].symbolName === 'foo', 'Error for foo');
    assert(result.errors[0].message.includes('already defined'), 'Error says already defined');
  }
});

test('validateDeclarations: fails when term uses same name as previously defined inductive', () => {
  // inductive Bar : Type where Zero : Bar
  // Bar : Type  (trying to redefine Bar)
  const declarations = [
    {
      name: 'Bar',
      type: mkTypeTT(0),
      constructors: [
        { name: 'Zero', type: mkConstTT('Bar') }
      ]
    },
    { name: 'Bar', type: mkTypeTT(1) }  // Redefinition of Bar
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Fails for redefinition of inductive');
  if (!result.success) {
    assert(result.errors.some(e => e.symbolName === 'Bar'), 'Error for Bar');
  }
});

test('validateDeclarations: fails when term uses same name as constructor', () => {
  // inductive Bar : Type where Zero : Bar
  // Zero : Type  (trying to redefine Zero)
  const declarations = [
    {
      name: 'Bar',
      type: mkTypeTT(0),
      constructors: [
        { name: 'Zero', type: mkConstTT('Bar') }
      ]
    },
    { name: 'Zero', type: mkTypeTT(1) }  // Redefinition of Zero
  ];

  const result = validateDeclarations(declarations);
  assert(result.success === false, 'Fails for redefinition of constructor');
  if (!result.success) {
    assert(result.errors.some(e => e.symbolName === 'Zero'), 'Error for Zero');
  }
});

console.log('\n' + '='.repeat(80));
console.log('ALL NAME RESOLUTION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
