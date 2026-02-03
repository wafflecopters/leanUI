import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { getTypeAtCursor } from './type-info';

describe('Absurd clause bugs', () => {
  test('ElabMap correctness: absurd clauses at beginning', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {x : A} -> Equal x x

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero (LeqSucc leq) = #absurd
leqCanonical (LeqSucc leq) LeqZero = #absurd
leqCanonical LeqZero LeqZero = refl
leqCanonical (LeqSucc pleq) (LeqSucc qleq) = ?Bar
    `.trim();

    const result = compileTTFromText(source);

    // Find the leqCanonical declaration
    const leqCanonicalBlock = result.blocks.find(b =>
      b.declarations.some(d => d.name === 'leqCanonical')
    );
    expect(leqCanonicalBlock).toBeDefined();

    const leqCanonicalDecl = leqCanonicalBlock!.declarations.find(d => d.name === 'leqCanonical');
    expect(leqCanonicalDecl).toBeDefined();

    // Log the source map for inspection
    console.log('\n=== SOURCE MAP ===');
    if (leqCanonicalDecl!.sourceMap) {
      const sortedEntries = Array.from(leqCanonicalDecl!.sourceMap.entries())
        .filter(([key]) => key.startsWith('value.clauses'))
        .sort((a, b) => a[0].localeCompare(b[0]));
      for (const [path, range] of sortedEntries) {
        console.log(`${path}: line ${range.start.line}, col ${range.start.col}`);
      }
    }

    // Log the elab map for inspection
    console.log('\n=== ELAB MAP ===');
    if (leqCanonicalDecl!.elabMap) {
      const sortedEntries = Array.from(leqCanonicalDecl!.elabMap.entries())
        .filter(([key]) => key.startsWith('value.clauses'))
        .sort((a, b) => a[0].localeCompare(b[0]));
      for (const [kernelPath, surfacePath] of sortedEntries) {
        console.log(`${kernelPath} -> ${surfacePath}`);
      }
    }

    // Log type info map for inspection
    console.log('\n=== TYPE INFO MAP ===');
    if (leqCanonicalDecl!.typeInfoMap) {
      const sortedEntries = Array.from(leqCanonicalDecl!.typeInfoMap.entries())
        .filter(([key]) => key.startsWith('value.clauses'))
        .sort((a, b) => a[0].localeCompare(b[0]));
      for (const [path, info] of sortedEntries) {
        console.log(`${path}: ${info.kernelPath}`);
      }
    }

    // Surface clause 0: LeqZero (LeqSucc leq) = #absurd (line 13)
    // Surface clause 1: (LeqSucc leq) LeqZero = #absurd (line 14)
    // Surface clause 2: LeqZero LeqZero = refl (line 15)
    // Surface clause 3: (LeqSucc pleq) (LeqSucc qleq) = ?Bar (line 16)

    // Kernel (after filtering absurd):
    // Kernel clause 0: LeqZero LeqZero = refl
    // Kernel clause 1: (LeqSucc pleq) (LeqSucc qleq) = ?Bar

    // Verify ElabMap correctness
    expect(leqCanonicalDecl!.elabMap?.get('value.clauses[0]')).toBe('value.clauses[2]');
    expect(leqCanonicalDecl!.elabMap?.get('value.clauses[1]')).toBe('value.clauses[3]');
  });

  test('ElabMap correctness: absurd clauses at end', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {x : A} -> Equal x x

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

test : {a b : Nat} -> (p q : Leq a b) -> Equal p q
test LeqZero LeqZero = refl
test (LeqSucc pleq) (LeqSucc qleq) = ?Bar
test LeqZero (LeqSucc leq) = #absurd
test (LeqSucc leq) LeqZero = #absurd
    `.trim();

    const result = compileTTFromText(source);
    const testDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test');

    expect(testDecl).toBeDefined();

    // Surface clauses: 0=refl, 1=?Bar, 2=absurd, 3=absurd
    // Kernel clauses: 0=refl, 1=?Bar
    expect(testDecl!.elabMap?.get('value.clauses[0]')).toBe('value.clauses[0]');
    expect(testDecl!.elabMap?.get('value.clauses[1]')).toBe('value.clauses[1]');
  });

  test('ElabMap correctness: absurd clauses in middle', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {x : A} -> Equal x x

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

test : {a b : Nat} -> (p q : Leq a b) -> Equal p q
test LeqZero LeqZero = refl
test LeqZero (LeqSucc leq) = #absurd
test (LeqSucc leq) LeqZero = #absurd
test (LeqSucc pleq) (LeqSucc qleq) = ?Bar
    `.trim();

    const result = compileTTFromText(source);
    const testDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test');

    expect(testDecl).toBeDefined();

    // Surface clauses: 0=refl, 1=absurd, 2=absurd, 3=?Bar
    // Kernel clauses: 0=refl, 1=?Bar
    expect(testDecl!.elabMap?.get('value.clauses[0]')).toBe('value.clauses[0]');
    expect(testDecl!.elabMap?.get('value.clauses[1]')).toBe('value.clauses[3]');
  });

  test('Type-at cursor works with absurd clauses', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {x : A} -> Equal x x

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero (LeqSucc leq) = #absurd
leqCanonical (LeqSucc leq) LeqZero = #absurd
leqCanonical LeqZero LeqZero = refl
leqCanonical (LeqSucc pleq) (LeqSucc qleq) = ?Bar
    `.trim();

    const result = compileTTFromText(source);
    const leqCanonicalDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'leqCanonical');

    expect(leqCanonicalDecl).toBeDefined();
    expect(leqCanonicalDecl!.sourceMap).toBeDefined();
    expect(leqCanonicalDecl!.elabMap).toBeDefined();
    expect(leqCanonicalDecl!.typeInfoMap).toBeDefined();

    // Find the source range for "LeqZero" in the third clause (first pattern)
    // This is surface clause 2 (after two absurd clauses)
    const leqZeroRange = leqCanonicalDecl!.sourceMap!.get('value.clauses[2].patterns[0]');
    expect(leqZeroRange).toBeDefined();
    // Line number should match the third non-absurd clause
    expect(leqZeroRange!.start.line).toBeGreaterThanOrEqual(14);

    // Get type-at cursor for this position
    const typeAtCursor = getTypeAtCursor(
      leqZeroRange!.start.pos,
      leqCanonicalDecl!.sourceMap!,
      leqCanonicalDecl!.elabMap!,
      leqCanonicalDecl!.typeInfoMap!,
      result.definitions
    );

    // Should successfully find type information
    expect(typeAtCursor).toBeDefined();
    expect(typeAtCursor!.prettyType).toBeTruthy();
  });

  test('Error location correctness with absurd clauses', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

bad : {a b : Nat} -> (p q : Leq a b) -> Nat
bad LeqZero (LeqSucc leq) = #absurd
bad (LeqSucc leq) LeqZero = #absurd
bad LeqZero LeqZero = True
bad (LeqSucc pleq) (LeqSucc qleq) = Zero
    `.trim();

    const result = compileTTFromText(source);
    const badDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'bad');

    expect(badDecl).toBeDefined();
    expect(badDecl!.checkSuccess).toBe(false);
    expect(badDecl!.checkErrors).toBeDefined();
    expect(badDecl!.checkErrors!.length).toBeGreaterThan(0);

    // The error should be on the third clause (line 13: "bad LeqZero LeqZero = True")
    // In kernel space, this is clause 0 (after filtering absurd clauses)
    // In surface space, this is clause 2 (before filtering)
    const error = badDecl!.checkErrors![0];
    expect(error.env.indexPath).toBeDefined();

    // The error path uses KERNEL indices
    const pathStr = error.env.indexPath.map(seg =>
      seg.kind === 'array' ? `[${seg.index}]` : `.${seg.name}`
    ).join('');

    // Should reference kernel clause 0 (the first non-absurd clause)
    expect(pathStr).toContain('clauses[0]');

    // Verify the ElabMap correctly maps kernel clause 0 to surface clause 2
    expect(badDecl!.elabMap?.get('value.clauses[0]')).toBe('value.clauses[2]');
  });

  test('All absurd clauses - no kernel clauses generated', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

allAbsurd : {a b : Nat} -> (p q : Leq a b) -> Nat
allAbsurd LeqZero (LeqSucc leq) = #absurd
allAbsurd (LeqSucc leq) LeqZero = #absurd
    `.trim();

    const result = compileTTFromText(source);
    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'allAbsurd');

    expect(decl).toBeDefined();

    // When all clauses are absurd, the function may not have a kernelValue
    // or may have a Match with zero clauses
    if (decl!.kernelValue) {
      expect(decl!.kernelValue.tag).toBe('Match');
      if (decl!.kernelValue.tag === 'Match') {
        expect(decl!.kernelValue.clauses.length).toBe(0);
      }
    }

    // ElabMap should have no clause mappings (no kernel clauses to map)
    const clauseEntries = Array.from(decl!.elabMap?.entries() || [])
      .filter(([key]) => key.startsWith('value.clauses'));
    expect(clauseEntries.length).toBe(0);

    // When all clauses are absurd, the function might have type/totality errors
    // because there are no valid clauses to provide a value
    // This is expected - we're just testing that ElabMap handling is correct
  });
});
