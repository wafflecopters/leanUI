/**
 * Tests for name resolution (symbol validation)
 */

import { describe, test, expect } from 'vitest';
import { mkConstTT, mkTypeTT, mkPiTT, mkVarTT, mkLambdaTT, mkAppTT } from '../compiler/surface';
import {
  emptySymbolContext,
  addSymbol,
  isSymbolDefined,
  validateTerm,
  validateDeclaration,
  validateDeclarations
} from './name-resolution';

describe('Name Resolution', () => {
  describe('Symbol Context', () => {
    test('emptySymbolContext creates empty context', () => {
      const ctx = emptySymbolContext();
      expect(ctx.size).toBe(0);
      expect(isSymbolDefined(ctx, 'Nat')).toBe(false);
    });

    test('addSymbol adds symbol to context', () => {
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      expect(isSymbolDefined(ctx, 'Nat')).toBe(true);
      expect(isSymbolDefined(ctx, 'Bool')).toBe(false);
    });

    test('addSymbol does not mutate original context', () => {
      const ctx1 = emptySymbolContext();
      const ctx2 = addSymbol(ctx1, 'Nat');

      expect(isSymbolDefined(ctx1, 'Nat')).toBe(false);
      expect(isSymbolDefined(ctx2, 'Nat')).toBe(true);
    });

    test('addSymbol can build up context incrementally', () => {
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');
      ctx = addSymbol(ctx, 'Bool');
      ctx = addSymbol(ctx, 'List');

      expect(isSymbolDefined(ctx, 'Nat')).toBe(true);
      expect(isSymbolDefined(ctx, 'Bool')).toBe(true);
      expect(isSymbolDefined(ctx, 'List')).toBe(true);
      expect(isSymbolDefined(ctx, 'Vec')).toBe(false);
    });
  });

  describe('Term Validation - Success Cases', () => {
    test('Var succeeds (no symbols)', () => {
      const term = mkVarTT(0);
      const ctx = emptySymbolContext();

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });

    test('Sort succeeds (no symbols)', () => {
      const term = mkTypeTT(0);
      const ctx = emptySymbolContext();

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });

    test('Const succeeds when symbol is defined', () => {
      const term = mkConstTT('Nat');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });

    test('Pi with defined symbol succeeds', () => {
      // (n : Nat) -> Nat
      const term = mkPiTT(mkConstTT('Nat'), mkVarTT(0), 'n');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });

    test('Lambda with defined symbols succeeds', () => {
      // λ(n : Nat). Nat
      const term = mkLambdaTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });

    test('App with defined symbols succeeds', () => {
      // f x (where both f and x are constants)
      const term = mkAppTT(mkConstTT('f'), mkConstTT('x'));
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'f');
      ctx = addSymbol(ctx, 'x');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(true);
    });
  });

  describe('Term Validation - Failure Cases', () => {
    test('Const fails when symbol undefined', () => {
      const term = mkConstTT('Nat');
      const ctx = emptySymbolContext();

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Nat');
        expect(result.errors[0].message).toContain('Undefined symbol');
      }
    });

    test('Pi fails when domain symbol undefined', () => {
      // (n : Nat) -> Bool  (Nat undefined, Bool defined)
      const term = mkPiTT(mkConstTT('Nat'), mkConstTT('Bool'), 'n');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Bool');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Nat');
      }
    });

    test('Pi fails when body symbol undefined', () => {
      // (n : Nat) -> Bool  (Nat defined, Bool undefined)
      const term = mkPiTT(mkConstTT('Nat'), mkConstTT('Bool'), 'n');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Bool');
      }
    });

    test('collects multiple errors', () => {
      // (a : Foo) -> Bar  (both undefined)
      const term = mkPiTT(mkConstTT('Foo'), mkConstTT('Bar'), 'a');
      const ctx = emptySymbolContext();

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(2);
        const symbolNames = result.errors.map(e => e.symbolName).sort();
        expect(symbolNames[0]).toBe('Bar');
        expect(symbolNames[1]).toBe('Foo');
      }
    });

    test('App collects errors from fn and arg', () => {
      // Foo bar (both undefined)
      const term = mkAppTT(mkConstTT('Foo'), mkConstTT('bar'));
      const ctx = emptySymbolContext();

      const result = validateTerm(term, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(2);
        const symbolNames = result.errors.map(e => e.symbolName).sort();
        expect(symbolNames[0]).toBe('Foo');
        expect(symbolNames[1]).toBe('bar');
      }
    });
  });

  describe('Declaration Validation', () => {
    test('type signature only', () => {
      // id : Nat -> Nat
      const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateDeclaration('id', declType, undefined, undefined, ctx);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
        expect(isSymbolDefined(result.value, 'Nat')).toBe(true);
      }
    });

    test('definition only', () => {
      // id = λ(x : Nat). x
      const declValue = mkLambdaTT(mkConstTT('Nat'), mkVarTT(0), 'x');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateDeclaration('id', undefined, declValue, undefined, ctx);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
      }
    });

    test('both type and value', () => {
      // id : Nat -> Nat
      // id = λ(x : Nat). x
      const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
      const declValue = mkLambdaTT(mkConstTT('Nat'), mkVarTT(0), 'x');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateDeclaration('id', declType, declValue, undefined, ctx);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
      }
    });

    test('self-reference allowed', () => {
      // rec : Nat -> Nat
      // rec = λ(x : Nat). rec x  (recursive call to itself)
      const declType = mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x');
      const declValue = mkLambdaTT(mkConstTT('Nat'), mkAppTT(mkConstTT('rec'), mkVarTT(0)), 'x');
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateDeclaration('rec', declType, declValue, undefined, ctx);
      expect(result.success).toBe(true);
    });

    test('inductive with constructors', () => {
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
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'Bool')).toBe(true);
        expect(isSymbolDefined(result.value, 'True')).toBe(true);
        expect(isSymbolDefined(result.value, 'False')).toBe(true);
      }
    });

    test('fails when type uses undefined symbol', () => {
      // bad : Foo -> Bar  (both undefined)
      const declType = mkPiTT(mkConstTT('Foo'), mkConstTT('Bar'), 'x');
      const ctx = emptySymbolContext();

      const result = validateDeclaration('bad', declType, undefined, undefined, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(2);
      }
    });

    test('fails when value uses undefined symbol', () => {
      // id = λ(x : Foo). x  (Foo undefined)
      const declValue = mkLambdaTT(mkConstTT('Foo'), mkVarTT(0), 'x');
      const ctx = emptySymbolContext();

      const result = validateDeclaration('id', undefined, declValue, undefined, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Foo');
      }
    });
  });

  describe('Multiple Declarations', () => {
    test('empty list succeeds', () => {
      const result = validateDeclarations([]);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.value.size).toBe(0);
      }
    });

    test('single declaration', () => {
      // id : Type -> Type
      const declType = mkPiTT(mkTypeTT(0), mkTypeTT(0), 'x');
      const declarations = [
        { name: 'id', type: declType }
      ];

      const result = validateDeclarations(declarations);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
      }
    });

    test('forward reference within block', () => {
      // id : Nat -> Nat
      // test = id
      const declarations = [
        { name: 'Nat', type: mkTypeTT(0) },
        { name: 'id', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x') },
        { name: 'test', value: mkConstTT('id') }
      ];

      const result = validateDeclarations(declarations);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'Nat')).toBe(true);
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
        expect(isSymbolDefined(result.value, 'test')).toBe(true);
      }
    });

    test('continues after errors', () => {
      // bad : Foo  (Foo undefined)
      // good : Type
      const declarations = [
        { name: 'bad', type: mkConstTT('Foo') },
        { name: 'good', type: mkTypeTT(0) }
      ];

      const result = validateDeclarations(declarations);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Foo');
      }
    });

    test('collects all errors', () => {
      // bad1 : Foo  (undefined)
      // bad2 : Bar  (undefined)
      const declarations = [
        { name: 'bad1', type: mkConstTT('Foo') },
        { name: 'bad2', type: mkConstTT('Bar') }
      ];

      const result = validateDeclarations(declarations);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(2);
        const symbols = result.errors.map(e => e.symbolName).sort();
        expect(symbols[0]).toBe('Bar');
        expect(symbols[1]).toBe('Foo');
      }
    });

    test('uses initial context', () => {
      // Start with Nat already defined
      let initialCtx = emptySymbolContext();
      initialCtx = addSymbol(initialCtx, 'Nat');

      // id : Nat -> Nat
      const declarations = [
        { name: 'id', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'x') }
      ];

      const result = validateDeclarations(declarations, initialCtx);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'Nat')).toBe(true);
        expect(isSymbolDefined(result.value, 'id')).toBe(true);
      }
    });
  });

  describe('Real-World Examples', () => {
    test('Nat and plus function', () => {
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
      expect(result.success).toBe(true);
      if (result.success) {
        expect(isSymbolDefined(result.value, 'Nat')).toBe(true);
        expect(isSymbolDefined(result.value, 'Zero')).toBe(true);
        expect(isSymbolDefined(result.value, 'Succ')).toBe(true);
        expect(isSymbolDefined(result.value, 'plus')).toBe(true);
      }
    });

    test('typo in type (Na instead of Nat)', () => {
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
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Na');
        expect(result.errors[0].message).toContain('Undefined symbol');
      }
    });
  });

  describe('Duplicate Name Detection', () => {
    test('fails when symbol already defined', () => {
      // Define Nat, then try to redefine it
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const result = validateDeclaration('Nat', mkTypeTT(0), undefined, undefined, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('Nat');
        expect(result.errors[0].message).toContain('already defined');
      }
    });

    test('fails when constructor name conflicts with existing symbol', () => {
      // Define True, then try to define Bool with True constructor
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'True');

      const constructors = [
        { name: 'True', type: mkConstTT('Bool') },
        { name: 'False', type: mkConstTT('Bool') }
      ];

      const result = validateDeclaration('Bool', mkTypeTT(0), undefined, constructors, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('True');
        expect(result.errors[0].message).toContain('already defined');
      }
    });

    test('fails when inductive name conflicts with existing symbol', () => {
      // Define Nat type, then try to redefine as inductive
      let ctx = emptySymbolContext();
      ctx = addSymbol(ctx, 'Nat');

      const constructors = [
        { name: 'Zero', type: mkConstTT('Nat') },
        { name: 'Succ', type: mkPiTT(mkConstTT('Nat'), mkConstTT('Nat'), 'n') }
      ];

      const result = validateDeclaration('Nat', mkTypeTT(0), undefined, constructors, ctx);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some(e => e.symbolName === 'Nat')).toBe(true);
        expect(result.errors.some(e => e.message.includes('already defined'))).toBe(true);
      }
    });

    test('fails when second declaration redefines first', () => {
      // foo : Type
      // foo = Type  (same name - should fail)
      const declarations = [
        { name: 'foo', type: mkTypeTT(1) },
        { name: 'foo', type: mkTypeTT(0) }  // Redefinition
      ];

      const result = validateDeclarations(declarations);
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBe(1);
        expect(result.errors[0].symbolName).toBe('foo');
        expect(result.errors[0].message).toContain('already defined');
      }
    });

    test('fails when term uses same name as previously defined inductive', () => {
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
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some(e => e.symbolName === 'Bar')).toBe(true);
      }
    });

    test('fails when term uses same name as constructor', () => {
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
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.some(e => e.symbolName === 'Zero')).toBe(true);
      }
    });
  });
});
