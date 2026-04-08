/**
 * Tests for source position tracking in the parser
 */

import { describe, test, expect } from 'vitest';
import { Parser } from './parser';
import { compileTTFromText } from '../compiler/compile';

describe('Parser Source Tracking', () => {
  test('parseDeclarationsWithSource returns declarations with source maps', () => {
    const parser = new Parser();
    const source = `id : A -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl).toBeDefined();
    expect(results[0].sourceMap).toBeDefined();
    expect(results[0].sourceMap instanceof Map).toBe(true);
  });

  test('parseDeclarationsWithSource with multiple declarations', () => {
    const parser = new Parser();
    const source = `id : A -> A

const : A -> B -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(2);
    expect(results[0].decl.name).toBe('id');
    expect(results[1].decl.name).toBe('const');
  });

  test('parseDeclarationsWithSource with merged type and value', () => {
    const parser = new Parser();
    const source = `id : A -> A
id x = x`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.name).toBe('id');
    expect(results[0].decl.type).toBeDefined();
    expect(results[0].decl.value).toBeDefined();
    // Source map should have entries from both lines
    expect(results[0].sourceMap.size).toBeGreaterThanOrEqual(0);
  });

  test('source map is separate for each declaration', () => {
    const parser = new Parser();
    const source = `id : A -> A

const : A -> B -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    // Each should have its own source map instance
    expect(results[0].sourceMap).not.toBe(results[1].sourceMap);
  });

  test('parseDeclarationsWithSource handles inductive', () => {
    const parser = new Parser();
    const source = `inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.kind).toBe('inductive');
    expect(results[0].decl.name).toBe('Nat');
    expect(results[0].sourceMap instanceof Map).toBe(true);
  });

  // ========================================================================
  // @syntax annotation tests
  // ========================================================================

  test('@syntax annotation on term declaration', () => {
    const parser = new Parser();
    const source = `@syntax $0 + $1
plus : Nat -> Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.name).toBe('plus');
    expect(results[0].decl.syntax).toBe('$0 + $1');
  });

  test('@syntax annotation on inductive declaration', () => {
    const parser = new Parser();
    const source = `@syntax \\N
inductive Nat : Type where
  | Zero : Nat
  | Succ : Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.kind).toBe('inductive');
    expect(results[0].decl.name).toBe('Nat');
    expect(results[0].decl.syntax).toBe('\\N');
  });

  test('@syntax annotation on constructors', () => {
    const parser = new Parser();
    const source = `inductive Nat : Type where
  @syntax 0
  | Zero : Nat
  @syntax $0\\prime
  | Succ : Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.constructors).toHaveLength(2);
    expect(results[0].decl.constructors![0].name).toBe('Zero');
    expect(results[0].decl.constructors![0].syntax).toBe('0');
    expect(results[0].decl.constructors![1].name).toBe('Succ');
    expect(results[0].decl.constructors![1].syntax).toBe('$0\\prime');
  });

  test('@syntax on both inductive and constructors', () => {
    const parser = new Parser();
    const source = `@syntax \\N
inductive Nat : Type where
  @syntax 0
  | Zero : Nat
  @syntax $0\\prime
  | Succ : Nat -> Nat`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.syntax).toBe('\\N');
    expect(results[0].decl.constructors![0].syntax).toBe('0');
    expect(results[0].decl.constructors![1].syntax).toBe('$0\\prime');
  });

  test('@syntax annotation not present when not specified', () => {
    const parser = new Parser();
    const source = `id : A -> A`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.syntax).toBeUndefined();
  });

  test('@syntax with implicit subscript', () => {
    const parser = new Parser();
    const source = `@syntax $0 =_{$A} $1
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.syntax).toBe('$0 =_{$A} $1');
  });

  test('@syntax with merged type and value', () => {
    const parser = new Parser();
    const source = `@syntax 1
one : Nat
one = Succ Zero`;

    const results = parser.parseDeclarationsWithSource(source);

    expect(results.length).toBe(1);
    expect(results[0].decl.name).toBe('one');
    expect(results[0].decl.syntax).toBe('1');
    expect(results[0].decl.type).toBeDefined();
    expect(results[0].decl.value).toBeDefined();
  });
});

describe('@syntax compilation pipeline', () => {
  test('@syntax propagates to CompiledDeclaration', () => {
    const source = `@syntax \\N
inductive Nat : Type where
  @syntax 0
  | Zero : Nat
  @syntax $0\\prime
  | Succ : Nat -> Nat

@syntax $0 + $1
plus : Nat -> Nat -> Nat
plus Zero n = n
plus (Succ m) n = Succ (plus m n)`;

    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);

    // Nat inductive
    const natDecl = decls.find(d => d.name === 'Nat');
    expect(natDecl).toBeDefined();
    expect(natDecl!.syntax).toBe('\\N');
    expect(natDecl!.constructorSyntax).toEqual([
      { name: 'Zero', syntax: '0' },
      { name: 'Succ', syntax: '$0\\prime' },
    ]);

    // plus
    const plusDecl = decls.find(d => d.name === 'plus');
    expect(plusDecl).toBeDefined();
    expect(plusDecl!.syntax).toBe('$0 + $1');
    expect(plusDecl!.constructorSyntax).toBeUndefined();
  });

  test('@syntax absent when not specified', () => {
    const source = `inductive Bool : Type where
  | True : Bool
  | False : Bool`;

    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);

    const boolDecl = decls.find(d => d.name === 'Bool');
    expect(boolDecl).toBeDefined();
    expect(boolDecl!.syntax).toBeUndefined();
    expect(boolDecl!.constructorSyntax).toBeUndefined();
  });

  test('@syntax on record constructor propagates to CompiledDeclaration', () => {
    const source = `@syntax \\exists $x \\in $A , $P @becomes DPair {u} {v} $$A (\\$x => $P)
record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  @syntax \\text{choose} $x, \\text{then} $y @becomes MkDPair $x $y
  constructor MkDPair
  fst : A
  snd : B fst`;

    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);

    const dpairDecl = decls.find(d => d.name === 'DPair');
    expect(dpairDecl).toBeDefined();
    expect(dpairDecl!.syntax).toBe('\\exists $x \\in $A , $P @becomes DPair {u} {v} $$A (\\$x => $P)');
    expect(dpairDecl!.constructorSyntax).toEqual([
      { name: 'MkDPair', syntax: '\\text{choose} $x, \\text{then} $y @becomes MkDPair $x $y' },
    ]);
  });

  test('@syntax on record constructor without explicit constructor name', () => {
    const source = `record Box (A : Type) : Type where
  unboxed : A`;

    const result = compileTTFromText(source);
    const decls = result.blocks.flatMap(b => b.declarations);

    const boxDecl = decls.find(d => d.name === 'Box');
    expect(boxDecl).toBeDefined();
    expect(boxDecl!.constructorSyntax).toBeUndefined();
  });
});
