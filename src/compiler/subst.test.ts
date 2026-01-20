/**
 * Tests for substitution functions in subst.ts
 *
 * These tests verify:
 * 1. applySubstitutionToContext - removing a variable from a context and substituting
 * 2. enumerateAppliedSubstitutions - iterating through substitutions with index adjustment
 * 3. applySubstitutionToMetaVars - handling metavariable contexts
 * 4. applySubstitutionToConstraints - handling constraint contexts
 * 5. minFreeVarIndex - finding minimum free variable index
 */

import { describe, test, expect } from "bun:test";
import { mkVar, TTKTerm, mkLZero } from "./kernel";
import { Constraint, MetaVar, TTKContext } from "./term";
import {
  applySubstitutionToContext,
  applySubstitutionToConstraints,
  applySubstitutionToMetaVars,
  enumerateAppliedSubstitutions,
  minFreeVarIndex,
  subst,
} from "./subst";

// ============================================================================
// Helper Functions
// ============================================================================

const Type: TTKTerm = { tag: 'Sort', level: mkLZero() };
const mkApp = (fn: TTKTerm, arg: TTKTerm): TTKTerm => ({ tag: 'App', fn, arg });
const mkConst = (name: string): TTKTerm => ({ tag: 'Const', name });
const mkPi = (name: string, domain: TTKTerm, body: TTKTerm): TTKTerm => ({
  tag: 'Binder',
  name,
  binderKind: { tag: 'BPi' },
  domain,
  body,
});

function assertTermEqual(actual: TTKTerm, expected: TTKTerm, _message?: string): void {
  const actualStr = JSON.stringify(actual);
  const expectedStr = JSON.stringify(expected);
  expect(actualStr).toBe(expectedStr);
}

function assertTTKContextEqual(actual: TTKContext, expected: TTKContext, message?: string): void {
  expect(actual.length).toBe(expected.length);
  for (let i = 0; i < actual.length; i++) {
    expect(actual[i].name).toBe(expected[i].name);
    assertTermEqual(actual[i].type, expected[i].type, `${message} - type at position ${i}`);
  }
}

// ============================================================================
// Tests for minFreeVarIndex
// ============================================================================

describe('minFreeVarIndex', () => {
  test('closed term (Type) returns Infinity', () => {
    const result = minFreeVarIndex(Type);
    expect(result).toBe(Infinity);
  });

  test('single variable', () => {
    const result = minFreeVarIndex(mkVar(3));
    expect(result).toBe(3);
  });

  test('multiple variables in App', () => {
    const term = mkApp(mkVar(5), mkVar(2));
    const result = minFreeVarIndex(term);
    expect(result).toBe(2);
  });

  test('bound variable in Pi is not counted', () => {
    // Pi (x : Type) . x  -- the x in body is bound, not free
    const term = mkPi('x', Type, mkVar(0));
    const result = minFreeVarIndex(term);
    expect(result).toBe(Infinity);
  });

  test('free variable in Pi body', () => {
    // Pi (x : Type) . y  where y is free (index 1 in body = index 0 from outside)
    const term = mkPi('x', Type, mkVar(1));
    const result = minFreeVarIndex(term);
    expect(result).toBe(0);
  });
});

// ============================================================================
// Tests for subst (basic sanity checks)
// ============================================================================

describe('subst', () => {
  test('replace matching variable', () => {
    // subst(1, Type, Var(1)) = Type
    const result = subst(1, Type, mkVar(1));
    assertTermEqual(result, Type);
  });

  test('decrement variable above target', () => {
    // subst(1, Type, Var(3)) = Var(2)
    const result = subst(1, Type, mkVar(3));
    assertTermEqual(result, mkVar(2));
  });

  test('leave variable below target unchanged', () => {
    // subst(2, Type, Var(1)) = Var(1)
    const result = subst(2, Type, mkVar(1));
    assertTermEqual(result, mkVar(1));
  });
});

// ============================================================================
// Tests for applySubstitutionToContext
// ============================================================================

describe('applySubstitutionToContext', () => {
  test('remove last entry (varIndex=0)', () => {
    // Context: [A: Type, x: A]
    // De Bruijn from tail: A=1, x=0
    // From x's perspective (position 1): Var(0) = A
    // So x's type is stored as Var(0)
    //
    // Remove x (varIndex=0)
    // Result: [A: Type]
    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: mkVar(0) },
    ];

    const result = applySubstitutionToContext(ctx, 0, Type);

    const expected: TTKContext = [
      { name: 'A', type: Type },
    ];

    assertTTKContextEqual(result, expected);
  });

  test('remove first entry (varIndex=n-1)', () => {
    // Context: [A: Type, x: A]
    // De Bruijn from tail: A=1, x=0
    //
    // Remove A (varIndex=1)
    // After removal: [x: ???]
    // x's type was Var(0) = A, substitute with Type
    // Result: [x: Type]
    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: mkVar(0) },
    ];

    const result = applySubstitutionToContext(ctx, 1, Type);

    const expected: TTKContext = [
      { name: 'x', type: Type },
    ];

    assertTTKContextEqual(result, expected);
  });

  test('remove middle entry', () => {
    // Context: [A: Type, B: Type, x: B]
    // Array positions: A=0, B=1, x=2
    // De Bruijn from tail: A=2, B=1, x=0
    //
    // From x's perspective (position 2):
    //   Var(0) = B (position 1)
    //   Var(1) = A (position 0)
    // x's type is B, stored as Var(0)
    //
    // Remove B (varIndex=1, array position 1)
    // After removal: [A: Type, x: ???]
    // x's type was Var(0) = B, substitute with Type
    // Result: [A: Type, x: Type]

    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'x', type: mkVar(0) },  // x: B (B is Var(0) from x's perspective)
    ];

    const result = applySubstitutionToContext(ctx, 1, Type);

    const expected: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: Type },  // B was replaced with Type
    ];

    assertTTKContextEqual(result, expected);
  });

  test('entry references variable BEFORE removed one', () => {
    // Context: [A: Type, B: Type, x: A]
    // From x's perspective (position 2):
    //   Var(0) = B (position 1)
    //   Var(1) = A (position 0)
    // x's type is A, stored as Var(1)
    //
    // Remove B (varIndex=1, array position 1)
    // After removal: [A: Type, x: A]
    // x's type was Var(1) = A
    // Since Var(1) > localIdx=0, it decrements to Var(0)
    // From x's NEW perspective (position 1): Var(0) = A ✓

    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'x', type: mkVar(1) },  // x: A (A is Var(1) from x's perspective)
    ];

    const result = applySubstitutionToContext(ctx, 1, Type);

    const expected: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: mkVar(0) },  // A is now Var(0) from x's new perspective
    ];

    assertTTKContextEqual(result, expected);
  });

  test('multiple entries after removed one', () => {
    // Context: [A: Type, B: Type, x: A, y: B]
    // Array positions: A=0, B=1, x=2, y=3
    // De Bruijn from tail: A=3, B=2, x=1, y=0
    //
    // From x's perspective (position 2):
    //   Var(0) = B, Var(1) = A
    // x's type is A = Var(1)
    //
    // From y's perspective (position 3):
    //   Var(0) = x, Var(1) = B, Var(2) = A
    // y's type is B = Var(1)
    //
    // Remove B (varIndex=2, array position 1)
    // cutoff = 4 - 2 - 1 = 1
    //
    // After removal: [A: Type, x: A, y: ???]
    //
    // For x (new position 1, came from 2):
    //   localIdx = 1 - 1 = 0
    //   x's type was Var(1) (A), localIdx=0
    //   Var(1) > 0, decrement to Var(0)
    //
    // For y (new position 2, came from 3):
    //   localIdx = 2 - 1 = 1
    //   y's type was Var(1) (B), substitute at index 1
    //   Var(1) == localIdx, replace with shiftedValue = Type

    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'x', type: mkVar(1) },  // A is Var(1) from x's perspective
      { name: 'y', type: mkVar(1) },  // B is Var(1) from y's perspective
    ];

    const result = applySubstitutionToContext(ctx, 2, Type);

    const expected: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: mkVar(0) },  // A is now Var(0)
      { name: 'y', type: Type },       // B replaced with Type
    ];

    assertTTKContextEqual(result, expected);
  });

  test('Vec example', () => {
    // Context: [A: Type, w5: Nat, w6: Type, w7: Nat, h: w6, tail: (Vec w6 (Succ w7))]
    // Array positions: A=0, w5=1, w6=2, w7=3, h=4, tail=5
    // De Bruijn from tail: A=5, w5=4, w6=3, w7=2, h=1, tail=0
    //
    // From h's perspective (position 4):
    //   Var(0) = w7 (pos 3)
    //   Var(1) = w6 (pos 2)
    //   Var(2) = w5 (pos 1)
    //   Var(3) = A (pos 0)
    // h's type is w6 = Var(1)
    //
    // From tail's perspective (position 5):
    //   Var(0) = h (pos 4)
    //   Var(1) = w7 (pos 3)
    //   Var(2) = w6 (pos 2)
    //   Var(3) = w5 (pos 1)
    //   Var(4) = A (pos 0)
    // tail's type is (Vec w6 (Succ w7)) = (Vec Var(2) (Succ Var(1)))
    //
    // Remove w6 (varIndex=3, array position 2)
    // cutoff = 6 - 3 - 1 = 2
    //
    // After removal: [A, w5, w7, h, tail]
    //
    // For h (new position 3, came from 4):
    //   localIdx = 3 - 2 = 1
    //   h's type was Var(1) (w6), substitute at index 1
    //   Replace with Type
    //
    // For tail (new position 4, came from 5):
    //   localIdx = 4 - 2 = 2
    //   tail's type was (Vec Var(2) (Succ Var(1)))
    //   Var(2) = w6, substitute at index 2 → Type
    //   Var(1) = w7, 1 < 2 so stays Var(1)
    //   Result: (Vec Type (Succ Var(1)))

    const Nat = mkConst('Nat');
    const Vec = mkConst('Vec');
    const Succ = mkConst('Succ');

    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'w5', type: Nat },
      { name: 'w6', type: Type },
      { name: 'w7', type: Nat },
      { name: 'h', type: mkVar(1) },  // w6 is Var(1) from h's perspective
      { name: 'tail', type: mkApp(mkApp(Vec, mkVar(2)), mkApp(Succ, mkVar(1))) },
    ];

    const result = applySubstitutionToContext(ctx, 3, Type);

    const expected: TTKContext = [
      { name: 'A', type: Type },
      { name: 'w5', type: Nat },
      { name: 'w7', type: Nat },
      { name: 'h', type: Type },
      { name: 'tail', type: mkApp(mkApp(Vec, Type), mkApp(Succ, mkVar(1))) },
    ];

    assertTTKContextEqual(result, expected);
  });

  test('value with variables gets shifted', () => {
    // Context: [A: Type, B: A, x: B]
    // From x's perspective: Var(0)=B, Var(1)=A
    // x's type is B = Var(0)
    //
    // Remove B (varIndex=1)
    // Substitute with value = Var(0) (which is A from main context after removal)
    // Note: after removing B, main context is [A, x], so Var(0) in value refers to A
    //
    // For x (came from position 2):
    //   localIdx = 0
    //   x's type was Var(0) = B
    //   Replace Var(0) with shiftedValue
    //   shiftedValue needs to be A from x's NEW perspective
    //   From x's new perspective (position 1): Var(0) = A
    //   So result should be Var(0)

    const ctx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: mkVar(0) },  // B: A (A is Var(0) from B's perspective)
      { name: 'x', type: mkVar(0) },  // x: B (B is Var(0) from x's perspective)
    ];

    // value = Var(1) means A in the ORIGINAL context [A, B, x]
    // After adjustment for removal: value references A which stays at same position
    // After removal, value should be Var(0) in context [A, x]
    // But we pass value in the ORIGINAL context, and the function adjusts it
    const value = mkVar(1);  // A in original context

    const result = applySubstitutionToContext(ctx, 1, value);

    // Expected: [A: Type, x: A]
    // From x's new perspective: A is Var(0)
    const expected: TTKContext = [
      { name: 'A', type: Type },
      { name: 'x', type: mkVar(0) },  // x: A
    ];

    assertTTKContextEqual(result, expected);
  });
});

// ============================================================================
// Tests for enumerateAppliedSubstitutions
// ============================================================================

describe('enumerateAppliedSubstitutions', () => {
  test('single substitution', () => {
    const substs = new Map<number, TTKTerm>([
      [2, Type],
    ]);

    const results = [...enumerateAppliedSubstitutions(substs)];

    expect(results.length).toBe(1);
    expect(results[0].varIndex).toBe(2);
    assertTermEqual(results[0].value, Type);
  });

  test('indices adjust after each yield', () => {
    // Substitutions: {0 -> A, 2 -> B}
    // After yielding {0 -> A} and removing index 0:
    //   Index 2 becomes index 1
    // So we should get: {0 -> A}, {1 -> B'}
    // where B' = subst(0, A, B)

    const A = mkConst('A');
    const B = mkConst('B');

    const substs = new Map<number, TTKTerm>([
      [0, A],
      [2, B],
    ]);

    const results = [...enumerateAppliedSubstitutions(substs)];

    expect(results.length).toBe(2);

    // Order depends on Map iteration, but let's check both are present
    const indices = results.map(r => r.varIndex).sort();
    // After first yield at 0, index 2 becomes 1
    // So we should see [0, 1] as the indices
    expect(indices[0]).toBe(0);
    expect(indices[1]).toBe(1);
  });

  test('value gets substituted', () => {
    // Substitutions: {1 -> Type, 2 -> Var(1)}
    // When we process index 1 first:
    //   Remaining: {2 -> Var(1)}
    //   Apply subst(1, Type, Var(1)) = Type
    //   Adjust index: 2 > 1, so 2 becomes 1
    //   New remaining: {1 -> Type}
    // Yields: {1 -> Type}, {1 -> Type}

    const substs = new Map<number, TTKTerm>([
      [1, Type],
      [2, mkVar(1)],  // References the variable at index 1
    ]);

    const results = [...enumerateAppliedSubstitutions(substs)];

    expect(results.length).toBe(2);

    // Second result should have Type as value (substituted)
    const second = results[1];
    assertTermEqual(second.value, Type, 'Second value should be Type after substitution');
  });
});

// ============================================================================
// Tests for applySubstitutionToMetaVars
// ============================================================================

describe('applySubstitutionToMetaVars', () => {
  test('variable not in metavar context', () => {
    // Main signature length: 5
    // MetaVar ctx length: 3 (prefix of main)
    // varIndex = 1 (second from tail of main)
    //
    // Variables in metavar's ctx: indices 4, 3, 2 (from main's tail)
    // varIndex = 1 is NOT in metavar's ctx (1 < 5-3=2)
    // So no changes should be made

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: Type },
    ];
    const metaType = mkVar(0);  // References C

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    const result = applySubstitutionToMetaVars(metaVars, 5, 1, Type);

    expect(result.size).toBe(1);
    const m = result.get('?m0')!;
    assertTermEqual(m.type, metaType, 'Type should be unchanged');
    assertTTKContextEqual(m.ctx, metaCtx, 'Context should be unchanged');
  });

  test('variable in metavar context', () => {
    // Main signature length: 5
    // MetaVar ctx length: 3 (prefix of main)
    // varIndex = 3 (fourth from tail of main)
    //
    // Variables in metavar's ctx: indices 4, 3, 2 (from main's tail)
    // varIndex = 3 IS in metavar's ctx (3 >= 5-3=2)
    // localVarIndex = 3 - 2 = 1
    //
    // If metavar type is Var(1), it should be substituted

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: mkVar(0) },  // C: B
    ];
    const metaType = mkVar(1);  // References B (index 1 from tail of metaCtx)

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    // Substitute at varIndex=3 (B in main) with Type
    const result = applySubstitutionToMetaVars(metaVars, 5, 3, Type);

    const m = result.get('?m0')!;

    // Type should be Type (B was substituted)
    assertTermEqual(m.type, Type, 'Type should be substituted');

    // Context should have B removed
    expect(m.ctx.length).toBe(2);
  });

  test('value with variable references that ARE in metavar context', () => {
    // Main sig: [A: Type, B: Type, C: Nat, D: Nat, E: Nat]
    // Indices:   4       3       2       1       0
    //
    // MetaVar ctx length: 4 → has [A, B, C, D] → indices 4, 3, 2, 1
    // varIndex = 3 (B)
    // value = (Succ #2) which references C (index 2)
    //
    // C (index 2) IS in metavar's ctx (2 >= 5-4=1) ✓
    // So this should work without escaping error

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: Nat },
      { name: 'D', type: Nat },
    ];
    // MetaVar type references B (index 2 from tail of metaCtx of length 4)
    const metaType = mkVar(2);

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    // value = (Succ #2) in main context references C
    const value = mkApp(Succ, mkVar(2));

    const result = applySubstitutionToMetaVars(metaVars, 5, 3, value);

    const m = result.get('?m0')!;

    // After substitution:
    // - B is removed from ctx
    // - metaType was Var(2) referencing B, now replaced with shifted value
    // - In metavar's new ctx of length 3, the value needs to reference C
    //   which is now at index 1 from tail
    // localVarIndex = 3 - (5-4) = 3 - 1 = 2
    // shiftAmount = 4 - 5 = -1
    // shiftedValue = (Succ #1)
    // After subst, type = (Succ #1)
    expect(m.ctx.length).toBe(3);
    assertTermEqual(m.type, mkApp(Succ, mkVar(1)));
  });

  test('value with escaping variable - throws error when type references removed var', () => {
    // Main sig: [A: Type, B: Type, C: Nat, D: Nat, E: Nat]
    // Indices:   4       3       2       1       0
    //
    // MetaVar ctx length: 2 → has [A, B] → indices 4, 3
    // varIndex = 3 (B)
    // value = (Succ #2) which references C (index 2)
    //
    // C (index 2) is NOT in metavar's ctx (2 < 5-2=3) ✗
    // Type references B (the removed var), so we need the value → escaping error

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];
    const metaType = mkVar(0);  // References B (the removed var!)

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    // value = (Succ #2) references C which is NOT in metavar's ctx
    const value = mkApp(Succ, mkVar(2));

    expect(() => {
      applySubstitutionToMetaVars(metaVars, 5, 3, value);
    }).toThrow(/Escaping variable/);
  });

  test('escaping value is OK if nothing references the removed var', () => {
    // Main sig: [A: Type, B: Type, C: Nat, D: Nat, E: Nat]
    // Indices:   4       3       2       1       0
    //
    // MetaVar ctx length: 2 → has [A, B] → indices 4, 3
    // varIndex = 3 (B)
    // value = (Succ #2) which references C (index 2) - would escape!
    //
    // BUT: metaType = Nat (constant, doesn't reference B)
    // So the value is never substituted, escaping doesn't matter

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];
    const metaType = Nat;  // Does NOT reference B

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    // value = (Succ #2) references C which is NOT in metavar's ctx
    // But that's OK because nothing needs this value!
    const value = mkApp(Succ, mkVar(2));

    const result = applySubstitutionToMetaVars(metaVars, 5, 3, value);

    const m = result.get('?m0')!;
    expect(m.ctx.length).toBe(1);  // B removed
    assertTermEqual(m.type, Nat);  // Type unchanged (was constant)
  });

  test('multiple metavars with different context sizes', () => {
    // Main sig length: 5
    // ?m0 has ctx length 1 → variable 3 not in scope
    // ?m1 has ctx length 4 → variable 3 in scope, value var 2 also in scope
    // ?m2 has ctx length 5 → variable 3 in scope, value var 2 also in scope

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const metaVars = new Map<string, MetaVar>([
      ['?m0', {
        ctx: [{ name: 'A', type: Type }],
        type: Nat,  // Doesn't reference any vars
      }],
      ['?m1', {
        ctx: [
          { name: 'A', type: Type },
          { name: 'B', type: Type },
          { name: 'C', type: Nat },
          { name: 'D', type: Nat },
        ],
        type: mkVar(2),  // References B
      }],
      ['?m2', {
        ctx: [
          { name: 'A', type: Type },
          { name: 'B', type: Type },
          { name: 'C', type: Nat },
          { name: 'D', type: Nat },
          { name: 'E', type: Nat },
        ],
        type: mkVar(3),  // References B
      }],
    ]);

    // Remove B (varIndex=3), substitute with (Succ #2) referencing C
    const value = mkApp(Succ, mkVar(2));
    const result = applySubstitutionToMetaVars(metaVars, 5, 3, value);

    // ?m0: unchanged (varIndex 3 not in ctx of length 1)
    const m0 = result.get('?m0')!;
    expect(m0.ctx.length).toBe(1);
    assertTermEqual(m0.type, Nat);

    // ?m1: ctx shrinks to 3, type substituted
    const m1 = result.get('?m1')!;
    expect(m1.ctx.length).toBe(3);
    // localVarIndex = 3 - (5-4) = 2, shiftAmount = 4-5 = -1
    // Var(2) → (Succ #1)
    assertTermEqual(m1.type, mkApp(Succ, mkVar(1)));

    // ?m2: ctx shrinks to 4, type substituted
    const m2 = result.get('?m2')!;
    expect(m2.ctx.length).toBe(4);
    // localVarIndex = 3 - (5-5) = 3, shiftAmount = 5-5 = 0
    // Var(3) → (Succ #2)
    assertTermEqual(m2.type, mkApp(Succ, mkVar(2)));
  });

  test('metavar type does not reference removed var - just decrements higher indices', () => {
    // If the metavar type doesn't reference the removed variable,
    // subst just decrements indices above the removed one

    const Nat = mkConst('Nat');

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: Nat },
    ];
    // metaType = Var(2) references A (not B which is at index 1)
    const metaType = mkVar(2);

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType }],
    ]);

    // Remove B (varIndex=3 in main of length 5)
    // localVarIndex = 3 - (5-3) = 1
    const result = applySubstitutionToMetaVars(metaVars, 5, 3, Type);

    const m = result.get('?m0')!;
    expect(m.ctx.length).toBe(2);
    // Var(2) was above localVarIndex=1, so it decrements to Var(1)
    // (A is now at index 1 in the smaller context)
    assertTermEqual(m.type, mkVar(1));
  });

  test('metavar with solution gets solution substituted too', () => {
    const Nat = mkConst('Nat');
    const Zero = mkConst('Zero');

    const metaCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: Nat },
    ];
    const metaType = mkVar(1);  // References B
    const metaSolution = mkVar(1);  // Solution also references B

    const metaVars = new Map<string, MetaVar>([
      ['?m0', { ctx: metaCtx, type: metaType, solution: metaSolution }],
    ]);

    // Remove B (varIndex=3), substitute with Zero
    const result = applySubstitutionToMetaVars(metaVars, 5, 3, Zero);

    const m = result.get('?m0')!;
    expect(m.ctx.length).toBe(2);
    assertTermEqual(m.type, Zero);
    assertTermEqual(m.solution!, Zero);
  });
});

// ============================================================================
// Tests for applySubstitutionToConstraints
// ============================================================================

describe('applySubstitutionToConstraints', () => {
  test('variable not in constraint context', () => {
    const constraintCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];
    const rhs = mkVar(0);  // References B

    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs },
    ];

    // varIndex = 0, but constraint ctx has length 2
    // Variables in constraint ctx: indices 4, 3 (if main length is 5)
    // varIndex = 0 is NOT in constraint ctx (0 < 5-2=3)
    const result = applySubstitutionToConstraints(constraints, 5, 0, Type);

    expect(result.length).toBe(1);
    assertTermEqual(result[0].rhs, rhs, 'RHS should be unchanged');
    assertTTKContextEqual(result[0].ctx, constraintCtx, 'Context should be unchanged');
  });

  test('variable in constraint context', () => {
    const constraintCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];
    const rhs = mkVar(0);  // References B (index 0 from tail of constraintCtx)

    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs },
    ];

    // Main length = 5, constraint ctx length = 2
    // Variables in constraint ctx: indices 4, 3 (from main's tail)
    // varIndex = 3 IS in constraint ctx (3 >= 5-2=3)
    // localVarIndex = 3 - 3 = 0
    const result = applySubstitutionToConstraints(constraints, 5, 3, Type);

    expect(result.length).toBe(1);

    // RHS should be Type (B was substituted)
    assertTermEqual(result[0].rhs, Type, 'RHS should be substituted');

    // Context should have B removed
    expect(result[0].ctx.length).toBe(1);
  });

  test('value with escaping variable - throws error when rhs references removed var', () => {
    // Constraint ctx length: 2 → has [A, B] → indices 4, 3
    // varIndex = 3 (B)
    // value = (Succ #2) which references C (index 2)
    // C is NOT in constraint's ctx, AND rhs references B → escaping error

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const constraintCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];

    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: mkVar(0) },  // rhs references B!
    ];

    const value = mkApp(Succ, mkVar(2));  // References index 2 (outside ctx)

    expect(() => {
      applySubstitutionToConstraints(constraints, 5, 3, value);
    }).toThrow(/Escaping variable/);
  });

  test('escaping value is OK in constraint if nothing references removed var', () => {
    // Constraint ctx length: 2 → has [A, B] → indices 4, 3
    // varIndex = 3 (B)
    // value = (Succ #2) which references C - would escape!
    // BUT: rhs = Nat (constant, doesn't reference B)
    // So the value is never substituted, escaping doesn't matter

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const constraintCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
    ];

    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs: Nat },  // rhs does NOT reference B
    ];

    const value = mkApp(Succ, mkVar(2));  // Would escape, but we don't need it

    const result = applySubstitutionToConstraints(constraints, 5, 3, value);

    expect(result.length).toBe(1);
    expect(result[0].ctx.length).toBe(1);  // B removed
    assertTermEqual(result[0].rhs, Nat);  // rhs unchanged
  });

  test('value with variable references in constraint context', () => {
    // Constraint ctx length: 4 → has [A, B, C, D] → indices 4, 3, 2, 1
    // varIndex = 3 (B)
    // value = (Succ #2) references C (index 2), which IS in ctx

    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const constraintCtx: TTKContext = [
      { name: 'A', type: Type },
      { name: 'B', type: Type },
      { name: 'C', type: Nat },
      { name: 'D', type: Nat },
    ];
    // rhs references B (index 2 from tail of ctx length 4)
    const rhs = mkVar(2);

    const constraints: Constraint[] = [
      { ctx: constraintCtx, meta: '?m0', rhs },
    ];

    const value = mkApp(Succ, mkVar(2));  // (Succ C)

    const result = applySubstitutionToConstraints(constraints, 5, 3, value);

    expect(result.length).toBe(1);
    expect(result[0].ctx.length).toBe(3);
    // localVarIndex = 3 - (5-4) = 2, shiftAmount = 4-5 = -1
    // shiftedValue = (Succ #1)
    // rhs was Var(2), replaced with (Succ #1)
    assertTermEqual(result[0].rhs, mkApp(Succ, mkVar(1)));
  });

  test('multiple constraints with different context sizes', () => {
    const Nat = mkConst('Nat');
    const Succ = mkConst('Succ');

    const constraints: Constraint[] = [
      // ctx length 1 → varIndex 3 not in scope
      { ctx: [{ name: 'A', type: Type }], meta: '?m0', rhs: Nat },
      // ctx length 4 → varIndex 3 in scope
      {
        ctx: [
          { name: 'A', type: Type },
          { name: 'B', type: Type },
          { name: 'C', type: Nat },
          { name: 'D', type: Nat },
        ],
        meta: '?m1',
        rhs: mkVar(2),  // References B
      },
    ];

    const value = mkApp(Succ, mkVar(2));  // (Succ C)
    const result = applySubstitutionToConstraints(constraints, 5, 3, value);

    expect(result.length).toBe(2);

    // First constraint unchanged
    expect(result[0].ctx.length).toBe(1);
    assertTermEqual(result[0].rhs, Nat);

    // Second constraint modified
    expect(result[1].ctx.length).toBe(3);
    assertTermEqual(result[1].rhs, mkApp(Succ, mkVar(1)));
  });
});
