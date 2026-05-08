/**
 * Phase 2 tests for @impl=nat NatImpl registry + iota-view rule in WHNF.
 *
 * The kernel verifies an inductive has the Nat shape (1 nullary + 1 unary
 * recursive ctor) and discovers Zero/Succ ctors structurally — independent
 * of the actual ctor names.
 *
 * The iota-view rule expands NatLit n inside Match expressions:
 *   NatLit 0       → Const(zeroCtor)
 *   NatLit (n+1)   → App(Const(succCtor), NatLit n)
 * so existing pattern matching against Zero/Succ keeps working for literals.
 */

import { describe, test, expect } from 'vitest';
import { TTKTerm } from './kernel';
import {
  DefinitionsMap,
  createDefinitionsMap,
  addInductiveDefinition,
  registerNatImpl,
} from './term';
import { whnf } from './whnf';
import { compileTTFromText } from './compile';

// ---------------------------------------------------------------------------
// Helpers: build small inductive types

/** Add a Peano-style nat with the given inductive/zero/succ ctor names. */
function addNatInductive(
  defs: DefinitionsMap,
  indName: string,
  zeroName: string,
  succName: string,
): DefinitionsMap {
  const indConst: TTKTerm = { tag: 'Const', name: indName };
  return addInductiveDefinition(
    defs,
    indName,
    { tag: 'Sort', level: { tag: 'ULit', n: 1 } }, // : Type
    [
      { name: zeroName, type: indConst }, // zero : T
      {
        name: succName,
        type: { tag: 'Binder', binderKind: { tag: 'BPi' }, name: '_', domain: indConst, body: indConst }, // succ : T → T
      },
    ],
    [], // indexPositions
  );
}

// ---------------------------------------------------------------------------

describe('registerNatImpl: structural discovery', () => {
  test('Zero/Succ ctors are discovered by structure (not by name)', () => {
    let defs = createDefinitionsMap();
    defs = addNatInductive(defs, 'Nat', 'Zero', 'Succ');
    const err = registerNatImpl(defs, 'Nat');
    expect(err).toBeNull();

    expect(defs.natImplByCtor!.get('Zero')).toEqual({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
    expect(defs.natImplByCtor!.get('Succ')).toEqual({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
  });

  test('Works with arbitrary ctor names (Z/S)', () => {
    let defs = createDefinitionsMap();
    defs = addNatInductive(defs, 'Nat', 'Z', 'S');
    const err = registerNatImpl(defs, 'Nat');
    expect(err).toBeNull();
    expect(defs.natImplByCtor!.get('Z')?.zeroCtor).toBe('Z');
    expect(defs.natImplByCtor!.get('S')?.succCtor).toBe('S');
  });

  test('Works regardless of constructor declaration order (Succ-first)', () => {
    let defs = createDefinitionsMap();
    const indConst: TTKTerm = { tag: 'Const', name: 'Nat' };
    defs = addInductiveDefinition(
      defs,
      'Nat',
      { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      [
        // Succ first, Zero second — should still discover correctly
        {
          name: 'Succ',
          type: { tag: 'Binder', binderKind: { tag: 'BPi' }, name: '_', domain: indConst, body: indConst },
        },
        { name: 'Zero', type: indConst },
      ],
      [],
    );
    const err = registerNatImpl(defs, 'Nat');
    expect(err).toBeNull();
    expect(defs.natImplByCtor!.get('Zero')?.zeroCtor).toBe('Zero');
    expect(defs.natImplByCtor!.get('Succ')?.succCtor).toBe('Succ');
  });

  test('Two @impl=nat types coexist with different ctor names', () => {
    let defs = createDefinitionsMap();
    defs = addNatInductive(defs, 'Nat', 'Zero', 'Succ');
    defs = addNatInductive(defs, 'Tally', 'Empty', 'Tick');
    expect(registerNatImpl(defs, 'Nat')).toBeNull();
    expect(registerNatImpl(defs, 'Tally')).toBeNull();

    expect(defs.natImplByCtor!.get('Zero')?.inductiveName).toBe('Nat');
    expect(defs.natImplByCtor!.get('Empty')?.inductiveName).toBe('Tally');
    expect(defs.natImplByCtor!.get('Succ')?.inductiveName).toBe('Nat');
    expect(defs.natImplByCtor!.get('Tick')?.inductiveName).toBe('Tally');
  });
});

describe('registerNatImpl: shape verification (rejection cases)', () => {
  test('Rejects inductive with 1 ctor', () => {
    let defs = createDefinitionsMap();
    const indConst: TTKTerm = { tag: 'Const', name: 'Singleton' };
    defs = addInductiveDefinition(
      defs,
      'Singleton',
      { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      [{ name: 'Only', type: indConst }],
      [],
    );
    const err = registerNatImpl(defs, 'Singleton');
    expect(err).toContain('exactly 2 constructors');
  });

  test('Rejects inductive with 3 ctors', () => {
    let defs = createDefinitionsMap();
    const indConst: TTKTerm = { tag: 'Const', name: 'Tri' };
    defs = addInductiveDefinition(
      defs,
      'Tri',
      { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      [
        { name: 'A', type: indConst },
        { name: 'B', type: indConst },
        { name: 'C', type: indConst },
      ],
      [],
    );
    const err = registerNatImpl(defs, 'Tri');
    expect(err).toContain('exactly 2 constructors');
  });

  test('Rejects inductive with two nullary ctors (Bool-like)', () => {
    let defs = createDefinitionsMap();
    const indConst: TTKTerm = { tag: 'Const', name: 'Bool' };
    defs = addInductiveDefinition(
      defs,
      'Bool',
      { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      [
        { name: 'True', type: indConst },
        { name: 'False', type: indConst },
      ],
      [],
    );
    const err = registerNatImpl(defs, 'Bool');
    expect(err).toMatch(/two nullary|nullary 'T' constructor/);
  });

  test("Rejects inductive whose 'Succ' takes 2 args", () => {
    let defs = createDefinitionsMap();
    const indConst: TTKTerm = { tag: 'Const', name: 'BadNat' };
    defs = addInductiveDefinition(
      defs,
      'BadNat',
      { tag: 'Sort', level: { tag: 'ULit', n: 1 } },
      [
        { name: 'Z', type: indConst },
        // Two-arg ctor: BadNat → BadNat → BadNat
        {
          name: 'Combine',
          type: {
            tag: 'Binder', binderKind: { tag: 'BPi' }, name: '_', domain: indConst,
            body: { tag: 'Binder', binderKind: { tag: 'BPi' }, name: '_', domain: indConst, body: indConst },
          },
        },
      ],
      [],
    );
    const err = registerNatImpl(defs, 'BadNat');
    expect(err).toContain("unsupported shape");
  });

  test('Rejects unknown inductive', () => {
    const defs = createDefinitionsMap();
    const err = registerNatImpl(defs, 'Nonexistent');
    expect(err).toContain('not found');
  });
});

describe('iota-view rule: NatLit reduces inside Match', () => {
  function makeNatDefs(): DefinitionsMap {
    let defs = createDefinitionsMap();
    defs = addNatInductive(defs, 'Nat', 'Zero', 'Succ');
    expect(registerNatImpl(defs, 'Nat')).toBeNull();
    return defs;
  }

  test('NatLit 0 matches Zero clause', () => {
    const defs = makeNatDefs();
    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'NatLit', value: 0n },
      clauses: [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: { tag: 'Const', name: 'zero_branch' } },
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'k' }] }], rhs: { tag: 'Const', name: 'succ_branch' } },
      ],
    };
    const reduced = whnf(matchTerm, { definitions: defs });
    expect(reduced).toEqual({ tag: 'Const', name: 'zero_branch' });
  });

  test('NatLit 5 matches Succ clause with predecessor binding', () => {
    const defs = makeNatDefs();
    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'NatLit', value: 5n },
      clauses: [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: { tag: 'Const', name: 'zero_branch' } },
        // Succ k → k (just return the predecessor)
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'k' }] }], rhs: { tag: 'Var', index: 0 } },
      ],
    };
    const reduced = whnf(matchTerm, { definitions: defs });
    // Expected: NatLit 4 (5's predecessor)
    expect(reduced).toEqual({ tag: 'NatLit', value: 4n });
  });

  test('NatLit 1 fully reduces to NatLit 0 via Succ predecessor', () => {
    const defs = makeNatDefs();
    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'NatLit', value: 1n },
      clauses: [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: { tag: 'Const', name: 'zero_branch' } },
        { patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'k' }] }], rhs: { tag: 'Var', index: 0 } },
      ],
    };
    const reduced = whnf(matchTerm, { definitions: defs });
    expect(reduced).toEqual({ tag: 'NatLit', value: 0n });
  });

  test('Without registered NatImpl, NatLit stays stuck inside Match', () => {
    const defs = createDefinitionsMap();
    // We DON'T call registerNatImpl, so the registry is empty.
    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'NatLit', value: 0n },
      clauses: [
        { patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }], rhs: { tag: 'Const', name: 'zero_branch' } },
      ],
    };
    const reduced = whnf(matchTerm, { definitions: defs });
    // Stays as Match with NatLit scrutinee — not reduced
    expect(reduced.tag).toBe('Match');
    expect((reduced as any).scrutinee).toEqual({ tag: 'NatLit', value: 0n });
  });

  test('Iota uses the right NatImpl when two coexist (different ctor names)', () => {
    let defs = createDefinitionsMap();
    defs = addNatInductive(defs, 'Nat', 'Zero', 'Succ');
    defs = addNatInductive(defs, 'Tally', 'Empty', 'Tick');
    expect(registerNatImpl(defs, 'Nat')).toBeNull();
    expect(registerNatImpl(defs, 'Tally')).toBeNull();

    // Match against Tally's ctors: Empty / Tick
    const matchTerm: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'NatLit', value: 0n },
      clauses: [
        { patterns: [{ tag: 'PCtor', name: 'Empty', args: [] }], rhs: { tag: 'Const', name: 'empty_branch' } },
        { patterns: [{ tag: 'PCtor', name: 'Tick', args: [{ tag: 'PVar', name: 'k' }] }], rhs: { tag: 'Var', index: 0 } },
      ],
    };
    const reduced = whnf(matchTerm, { definitions: defs });
    expect(reduced).toEqual({ tag: 'Const', name: 'empty_branch' });
  });
});

describe('@impl=nat annotation: end-to-end via compileTTFromText', () => {
  test('@syntax @impl=nat populates the registry', () => {
    const result = compileTTFromText(`
@syntax @impl=nat
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`);
    expect(result.success).toBe(true);
    const reg = result.definitions?.natImplByCtor;
    expect(reg).toBeDefined();
    expect(reg!.get('Zero')).toEqual({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
    expect(reg!.get('Succ')).toEqual({ inductiveName: 'Nat', zeroCtor: 'Zero', succCtor: 'Succ' });
  });

  test('Custom Nat impl with non-standard ctor names (Z/S) works', () => {
    const result = compileTTFromText(`
@syntax @impl=nat
inductive Counter : Type where
  Z : Counter
  S : Counter -> Counter
`);
    expect(result.success).toBe(true);
    const reg = result.definitions?.natImplByCtor;
    expect(reg!.get('Z')?.zeroCtor).toBe('Z');
    expect(reg!.get('S')?.succCtor).toBe('S');
  });

  test('Without @impl=nat, no registry entries are added', () => {
    const result = compileTTFromText(`
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat
`);
    expect(result.success).toBe(true);
    const reg = result.definitions?.natImplByCtor;
    // Either absent or empty map
    expect(reg === undefined || reg.size === 0).toBe(true);
  });
});
