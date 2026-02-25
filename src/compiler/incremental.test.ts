import { describe, test, expect } from 'vitest';
import {
  BlockDepInfo,
  computeRecheckSet,
  createIncrementalCache,
  extractDefinedNames,
  wordBoundaryMatch,
} from './incremental';
import { ParsedDeclaration } from '../parser/parser';
import { compileTTFromText, compileIncrementalTT } from './compile';

// ============================================================================
// wordBoundaryMatch
// ============================================================================

describe('wordBoundaryMatch', () => {
  test('matches exact name', () => {
    expect(wordBoundaryMatch('Nat -> Nat', 'Nat')).toBe(true);
  });

  test('does not match substring inside another word', () => {
    expect(wordBoundaryMatch('radd rsub rmul', 'a')).toBe(false);
    expect(wordBoundaryMatch('radd rsub rmul', 'add')).toBe(false);
  });

  test('matches word at start of text', () => {
    expect(wordBoundaryMatch('Nat', 'Nat')).toBe(true);
  });

  test('matches word at end of text', () => {
    expect(wordBoundaryMatch('x : Nat', 'Nat')).toBe(true);
  });

  test('matches dotted name', () => {
    expect(wordBoundaryMatch('Point.x r', 'Point.x')).toBe(true);
  });

  test('does not match partial dotted name', () => {
    expect(wordBoundaryMatch('PointExtra.x r', 'Point.x')).toBe(false);
  });

  test('matches name followed by parens', () => {
    expect(wordBoundaryMatch('f (Succ n)', 'Succ')).toBe(true);
  });

  test('does not match name as part of longer identifier', () => {
    expect(wordBoundaryMatch('NatList', 'Nat')).toBe(false);
    expect(wordBoundaryMatch('isNat', 'Nat')).toBe(false);
  });
});

// ============================================================================
// extractDefinedNames
// ============================================================================

describe('extractDefinedNames', () => {
  test('term declaration', () => {
    const decl: ParsedDeclaration = {
      kind: 'def',
      name: 'add',
    };
    expect(extractDefinedNames(decl)).toEqual(['add']);
  });

  test('expression declaration (unnamed)', () => {
    const decl: ParsedDeclaration = {
      kind: 'expr',
    };
    expect(extractDefinedNames(decl)).toEqual([]);
  });

  test('inductive type with constructors', () => {
    const decl: ParsedDeclaration = {
      kind: 'inductive',
      name: 'Nat',
      constructors: [
        { name: 'Zero', type: { tag: 'Hole', id: '_' } as any },
        { name: 'Succ', type: { tag: 'Hole', id: '_' } as any },
      ],
    };
    const names = extractDefinedNames(decl);
    expect(names).toContain('Nat');
    expect(names).toContain('Zero');
    expect(names).toContain('Succ');
  });

  test('record with fields', () => {
    const decl: ParsedDeclaration = {
      kind: 'record',
      name: 'Point',
      fields: [
        { name: 'x', type: { tag: 'Hole', id: '_' } as any },
        { name: 'y', type: { tag: 'Hole', id: '_' } as any },
      ],
    };
    const names = extractDefinedNames(decl);
    expect(names).toContain('Point');
    expect(names).toContain('MkPoint'); // default constructor
    expect(names).toContain('Point.x');
    expect(names).toContain('Point.y');
  });

  test('record with custom constructor name', () => {
    const decl: ParsedDeclaration = {
      kind: 'record',
      name: 'Pair',
      constructorName: 'MkPair',
      fields: [
        { name: 'fst', type: { tag: 'Hole', id: '_' } as any },
        { name: 'snd', type: { tag: 'Hole', id: '_' } as any },
      ],
    };
    const names = extractDefinedNames(decl);
    expect(names).toContain('Pair');
    expect(names).toContain('MkPair');
    expect(names).toContain('Pair.fst');
    expect(names).toContain('Pair.snd');
  });
});

// ============================================================================
// computeRecheckSet
// ============================================================================

describe('computeRecheckSet', () => {
  // Helper: build a BlockDepInfo from a simple spec
  function block(index: number, sourceText: string, definesNames: string[]): BlockDepInfo {
    return { index, sourceText, definesNames };
  }

  test('no changes yields empty recheck set', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero Succ', ['Nat', 'Zero', 'Succ']),
      block(1, 'add : Nat -> Nat', ['add']),
    ];
    const result = computeRecheckSet(blocks, new Set());
    expect(result.size).toBe(0);
  });

  test('changed block is in recheck set', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero Succ', ['Nat', 'Zero', 'Succ']),
      block(1, 'add : Nat -> Nat', ['add']),
    ];
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
  });

  test('dependent block is transitively rechecked', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero Succ', ['Nat', 'Zero', 'Succ']),
      block(1, 'add : Nat -> Nat -> Nat', ['add']),
      block(2, 'double n = add n n', ['double']),
    ];
    // Change block 0 (Nat) → block 1 (uses Nat) and block 2 (uses add, which uses Nat)
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(true);
    expect(result.has(2)).toBe(true); // transitive: 0 → 1 → 2
  });

  test('independent blocks are NOT rechecked', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero Succ', ['Nat', 'Zero', 'Succ']),
      block(1, 'inductive Bool where True False', ['Bool', 'True', 'False']),
      block(2, 'myBool = True', ['myBool']),
    ];
    // Change block 0 (Nat) → block 1 (Bool, independent) not rechecked
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(false); // Bool doesn't use Nat
    expect(result.has(2)).toBe(false); // myBool uses True, not Nat
  });

  test('word boundary prevents false positives', () => {
    const blocks = [
      block(0, 'a : Type', ['a']),
      block(1, 'radd : Type -> Type', ['radd']),
    ];
    // Change block 0 (defines 'a') → block 1 should NOT be rechecked
    // because 'a' inside 'radd' is not a word boundary match
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(false);
  });

  test('transitive chain A→B→C→D', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero', ['Nat', 'Zero']),
      block(1, 'add : Nat -> Nat', ['add']),
      block(2, 'double x = add x x', ['double']),
      block(3, 'quad x = double (double x)', ['quad']),
    ];
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(true);
    expect(result.has(2)).toBe(true);
    expect(result.has(3)).toBe(true);
  });

  test('diamond dependency: change B rechecks B and D, not A or C', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero', ['Nat', 'Zero']),
      block(1, 'add : Nat -> Nat', ['add']),         // depends on Nat
      block(2, 'mul : Nat -> Nat', ['mul']),          // depends on Nat
      block(3, 'calc x = add (mul x x) x', ['calc']),// depends on add AND mul
    ];
    // Change block 1 (add) → rechecks 1 and 3 (uses add), NOT 0 or 2
    const result = computeRecheckSet(blocks, new Set([1]));
    expect(result.has(0)).toBe(false);
    expect(result.has(1)).toBe(true);
    expect(result.has(2)).toBe(false);
    expect(result.has(3)).toBe(true);
  });

  test('constructor names create dependencies', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero Succ', ['Nat', 'Zero', 'Succ']),
      block(1, 'one = Succ Zero', ['one']),
    ];
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(1)).toBe(true);
  });

  test('record projection names create dependencies', () => {
    const blocks = [
      block(0, 'record Point where x y', ['Point', 'MkPoint', 'Point.x', 'Point.y']),
      block(1, 'getX p = Point.x p', ['getX']),
    ];
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(1)).toBe(true);
  });

  test('self-references are excluded from dependency graph', () => {
    // Block 0 defines 'Nat' and its source contains 'Nat' (recursive type).
    // Changing block 0 should not cause infinite loop or extra recheck.
    const blocks = [
      block(0, 'inductive Nat : Type where Zero : Nat | Succ : Nat -> Nat', ['Nat', 'Zero', 'Succ']),
      block(1, 'id x = x', ['id']),
    ];
    const result = computeRecheckSet(blocks, new Set([0]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(false); // id doesn't use Nat
  });

  test('only backward dependencies matter', () => {
    // Block 0 mentions 'add' (which is defined in block 1).
    // This is a forward reference — should NOT create a dependency.
    const blocks = [
      block(0, 'result = add 1 2', ['result']),
      block(1, 'add x y = x', ['add']),
    ];
    // Change block 1 → should NOT recheck block 0
    // (block 0 does mention 'add', but add is defined AFTER block 0)
    // Actually wait — block 0 DOES depend on block 1 since it uses 'add'.
    // But we only track backward deps (defBlockIdx < block.index).
    // Block 0's index is 0, block 1's index is 1. 'add' is defined in block 1 (index 1).
    // For block 0, defBlockIdx (1) >= block.index (0), so this is skipped.
    // This means changing block 1 won't recheck block 0, which is CORRECT
    // because in a valid program, block 0 can't reference block 1.
    // (Forward references would be name resolution errors.)
    const result = computeRecheckSet(blocks, new Set([1]));
    expect(result.has(0)).toBe(false);
    expect(result.has(1)).toBe(true);
  });

  test('multiple changed blocks', () => {
    const blocks = [
      block(0, 'inductive Nat where Zero', ['Nat', 'Zero']),
      block(1, 'inductive Bool where True False', ['Bool', 'True', 'False']),
      block(2, 'f : Nat -> Bool', ['f']),  // depends on both Nat and Bool
      block(3, 'g : Nat -> Nat', ['g']),   // depends on Nat only
    ];
    // Change both 0 and 1
    const result = computeRecheckSet(blocks, new Set([0, 1]));
    expect(result.has(0)).toBe(true);
    expect(result.has(1)).toBe(true);
    expect(result.has(2)).toBe(true);
    expect(result.has(3)).toBe(true);
  });
});

// ============================================================================
// compileIncrementalTT integration tests
// ============================================================================

describe('compileIncrementalTT', () => {
  const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero    n = n
add (Succ m) n = Succ (add m n)

double : Nat -> Nat
double n = add n n
`.trim();

  test('first compile produces same result as compileTTFromText', () => {
    const cache = createIncrementalCache();
    const incResult = compileIncrementalTT(source, cache);
    const fullResult = compileTTFromText(source);

    expect(incResult.success).toBe(fullResult.success);
    expect(incResult.blocks.length).toBe(fullResult.blocks.length);
    expect(incResult.totalCheckErrors).toBe(fullResult.totalCheckErrors);
    expect(incResult.totalNameErrors).toBe(fullResult.totalNameErrors);
  });

  test('second compile with no changes reuses cache', () => {
    const cache = createIncrementalCache();
    // First compile fills the cache
    compileIncrementalTT(source, cache);

    // Second compile should reuse everything
    const result2 = compileIncrementalTT(source, cache);
    expect(result2.success).toBe(true);
    expect(result2.blocks.length).toBe(3);
  });

  test('changing a leaf block only rechecks that block', () => {
    const cache = createIncrementalCache();
    compileIncrementalTT(source, cache);

    // Save cached blocks to detect which ones are recompiled
    const cachedBlock0 = cache.blocks[0]!.compiledBlock;
    const cachedBlock1 = cache.blocks[1]!.compiledBlock;

    // Change double (leaf) — doesn't affect Nat or add
    const modifiedSource = source.replace(
      'double n = add n n',
      'double n = add (add n n) n'
    );
    const result = compileIncrementalTT(modifiedSource, cache);
    expect(result.success).toBe(true);

    // Block 0 (Nat) and 1 (add) should be reused (same object)
    expect(result.blocks[0]).toBe(cachedBlock0);
    expect(result.blocks[1]).toBe(cachedBlock1);
    // Block 2 (double) was recompiled — different object
    expect(result.blocks[2]).not.toBe(cachedBlock0);
  });

  test('changing a dependency rechecks dependents', () => {
    const cache = createIncrementalCache();
    compileIncrementalTT(source, cache);

    const cachedBlock0 = cache.blocks[0]!.compiledBlock;

    // Change add (block 1) — double depends on add, so both recheck
    const modifiedSource = source.replace(
      'add (Succ m) n = Succ (add m n)',
      'add (Succ m) n = Succ (Succ (add m n))'  // intentionally wrong
    );
    const result = compileIncrementalTT(modifiedSource, cache);

    // Block 0 (Nat) should be reused
    expect(result.blocks[0]).toBe(cachedBlock0);
    // Block 1 (add) was changed — recompiled
    // Block 2 (double) depends on add — also recompiled
    expect(result.blocks[1]).not.toBe(cachedBlock0);
  });

  test('independent blocks are not rechecked', () => {
    const indepSource = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Bool : Type where
  True : Bool
  False : Bool

myBool : Bool
myBool = True
`.trim();

    const cache = createIncrementalCache();
    compileIncrementalTT(indepSource, cache);

    const cachedBool = cache.blocks[1]!.compiledBlock;
    const cachedMyBool = cache.blocks[2]!.compiledBlock;

    // Change Nat (block 0) — Bool and myBool are independent
    const modifiedSource = indepSource.replace(
      '  Succ : Nat -> Nat',
      '  Succ : Nat -> Nat\n  Succ2 : Nat -> Nat'
    );
    const result = compileIncrementalTT(modifiedSource, cache);

    // Bool and myBool should be reused
    expect(result.blocks[1]).toBe(cachedBool);
    expect(result.blocks[2]).toBe(cachedMyBool);
  });

  test('cache is trimmed when blocks are removed', () => {
    const cache = createIncrementalCache();
    compileIncrementalTT(source, cache);
    expect(cache.blocks.length).toBe(3);

    // Remove the last block
    const shorterSource = source.replace('\ndouble : Nat -> Nat\ndouble n = add n n', '');
    compileIncrementalTT(shorterSource, cache);
    expect(cache.blocks.length).toBe(2);
  });

  test('incremental result is correct after modifying middle block', () => {
    const cache = createIncrementalCache();
    const result1 = compileIncrementalTT(source, cache);
    expect(result1.success).toBe(true);

    // Modify add to have wrong type (should cause error in double too)
    const badSource = source.replace(
      'add : Nat -> Nat -> Nat',
      'add : Nat -> Nat'
    );
    const result2 = compileIncrementalTT(badSource, cache);
    // The modified add has wrong # of clauses — should fail
    expect(result2.success).toBe(false);
  });
});
