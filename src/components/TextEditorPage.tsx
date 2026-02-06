/**
 * TextEditorPage - A page for editing code and viewing compilation results
 */
import React, { useRef, useMemo, useState, useCallback, useEffect } from 'react';
import { useSearchParams } from 'react-router-dom';
import Editor, { OnMount, OnChange } from '@monaco-editor/react';
import type { editor as MonacoEditor } from 'monaco-editor';
import { compileTTFromText, CompileResult, CompiledBlock, CompiledDeclaration, extractWildcardInlayHints, WildcardInlayHint, extractSemanticTokens, SemanticToken, extractHoleLocations, CaseTree, TotalityResult } from '../compiler/compile';
import { getTypeAtCursor, getTypeAtSelection, TypeAtCursorResult, CursorQueryResult } from '../compiler/type-info';
import { serializeIndexPath, IndexPath, SourceRange, ElabMap, SourceMap } from '../types/source-position';
import { TTKTerm, prettyPrint as prettyPrintTTK, prettyPrintFormatted, PrettyPrintOptions, NamedArgMap } from '../compiler/kernel';
import { DefinitionsMap, createNamedArgLookup } from '../compiler/term';
import { GoalState } from '../tactics/proof-state';

// Unicode abbreviations map (Lean-style)
// Add new abbreviations here - they will be auto-replaced when followed by space/punctuation
const UNICODE_ABBREVIATIONS: Record<string, string> = {
  // Greek letters
  '\\alpha': 'α',
  '\\beta': 'β',
  '\\gamma': 'γ',
  '\\delta': 'δ',
  '\\epsilon': 'ε',
  '\\zeta': 'ζ',
  '\\eta': 'η',
  '\\theta': 'θ',
  '\\iota': 'ι',
  '\\kappa': 'κ',
  '\\lambda': 'λ',
  '\\mu': 'μ',
  '\\nu': 'ν',
  '\\xi': 'ξ',
  '\\pi': 'π',
  '\\rho': 'ρ',
  '\\sigma': 'σ',
  '\\tau': 'τ',
  '\\upsilon': 'υ',
  '\\phi': 'φ',
  '\\chi': 'χ',
  '\\psi': 'ψ',
  '\\omega': 'ω',
  // Capital Greek
  '\\Gamma': 'Γ',
  '\\Delta': 'Δ',
  '\\Theta': 'Θ',
  '\\Lambda': 'Λ',
  '\\Xi': 'Ξ',
  '\\Pi': 'Π',
  '\\Sigma': 'Σ',
  '\\Phi': 'Φ',
  '\\Psi': 'Ψ',
  '\\Omega': 'Ω',
  // Common math symbols
  '\\to': '→',
  '\\rightarrow': '→',
  '\\leftarrow': '←',
  '\\Rightarrow': '⇒',
  '\\Leftarrow': '⇐',
  '\\forall': '∀',
  '\\exists': '∃',
  '\\neg': '¬',
  '\\and': '∧',
  '\\or': '∨',
  '\\times': '×',
  '\\cdot': '·',
  '\\circ': '∘',
  '\\le': '≤',
  '\\ge': '≥',
  '\\ne': '≠',
  '\\equiv': '≡',
  '\\approx': '≈',
  '\\infty': '∞',
  '\\nat': 'ℕ',
  '\\int': 'ℤ',
  '\\rat': 'ℚ',
  '\\real': 'ℝ',
  '\\complex': 'ℂ',
  // Subscripts and superscripts
  '\\0': '₀',
  '\\1': '₁',
  '\\2': '₂',
  '\\3': '₃',
  '\\4': '₄',
  '\\5': '₅',
  '\\6': '₆',
  '\\7': '₇',
  '\\8': '₈',
  '\\9': '₉',
};

// Build a regex pattern to match any abbreviation at end of text
const ABBREV_PATTERN = new RegExp(
  '(' + Object.keys(UNICODE_ABBREVIATIONS)
    .map(k => k.replace(/\\/g, '\\\\'))
    .sort((a, b) => b.length - a.length) // Match longer abbreviations first
    .join('|') + ')$'
);

// Color palette for syntax highlighting (matches TextEditorPage)
const SYNTAX_COLORS = {
  keyword: '569cd6',        // Blue - for inductive, where, def, etc.
  keywordOperator: '94d0ff', // Light blue - for ->, =>
  typeKeyword: 'cf92cd',    // Light purple/pink - for Type, Prop
  comment: '6a9955',        // Green - for comments (-- and {- -})
  string: 'ce9178',         // Orange
  number: 'b5cea8',         // Light green
  identifier: 'd4d4d4',     // Light gray - default
  constName: '4ec9b0',      // Teal - for types/constructors (Nat, Vec, Zero, Cons)
  termName: 'e5b387',       // Warm yellow/tan - for function names (plus, nth)
  patternVar: '9cdcfe',     // Light blue - for pattern variables (x, n, h)
  delimiter: 'e5c995',      // Light tan/gold - for (, ), etc.
  namedBrace: '6e7681',     // Dark grey - for { } in named arguments/binders
  hole: 'e5c07b',           // Yellow for holes (unfinished code)
  absurd: '4fc1ff',         // Bright cyan - for #absurd marker
  tacticName: 'ffb0d8',     // Pale pink - for tactic names (intro, apply, exact, etc.)
  directive: 'ff79c6',      // Pink - for directives (@test, @name, @assumeK, etc.)
  directiveValue: '8b949e', // Grey - for directive values (true, false, "test name")
};

// Monaco theme matching TextEditorPage
const MONACO_THEME: MonacoEditor.IStandaloneThemeData = {
  base: 'vs-dark',
  inherit: true,
  rules: [
    { token: 'comment', foreground: SYNTAX_COLORS.comment, fontStyle: 'italic' },
    { token: 'keyword', foreground: SYNTAX_COLORS.keyword },
    { token: 'keyword.operator', foreground: SYNTAX_COLORS.keywordOperator },
    { token: 'type.identifier', foreground: SYNTAX_COLORS.typeKeyword },
    { token: 'string', foreground: SYNTAX_COLORS.string },
    { token: 'number', foreground: SYNTAX_COLORS.number },
    { token: 'identifier', foreground: SYNTAX_COLORS.identifier },
    { token: 'identifier.const', foreground: SYNTAX_COLORS.constName },
    { token: 'identifier.term', foreground: SYNTAX_COLORS.termName },
    { token: 'identifier.pattern', foreground: SYNTAX_COLORS.patternVar },
    { token: 'delimiter', foreground: SYNTAX_COLORS.delimiter },
    { token: 'delimiter.bracket', foreground: SYNTAX_COLORS.delimiter },
    { token: 'variable.predefined', foreground: SYNTAX_COLORS.hole },
    { token: 'variable.wildcard', foreground: SYNTAX_COLORS.patternVar },
    // Semantic token rules (override lexical highlighting)
    { token: 'termName', foreground: SYNTAX_COLORS.termName },
    { token: 'constName', foreground: SYNTAX_COLORS.constName },
    { token: 'boundVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'patternVar', foreground: SYNTAX_COLORS.patternVar },
    { token: 'absurd', foreground: SYNTAX_COLORS.absurd },
    { token: 'namedBrace', foreground: SYNTAX_COLORS.namedBrace },
    { token: 'tacticName', foreground: SYNTAX_COLORS.tacticName },
    { token: 'directive', foreground: SYNTAX_COLORS.directive },
    { token: 'directiveValue', foreground: SYNTAX_COLORS.directiveValue },
  ],
  colors: {
    'editor.background': '#161b22',
    'editor.foreground': '#c9d1d9',
    'editor.lineHighlightBackground': '#161b22',
    'editor.selectionBackground': '#264f78',
    'editorCursor.foreground': '#58a6ff',
    'editorLineNumber.foreground': '#6e7681',
    'editorLineNumber.activeForeground': '#c9d1d9',
    'editorIndentGuide.background': '#21262d',
    'editorIndentGuide.activeBackground': '#30363d',
    'editorBracketMatch.background': '#2d333b',
    'editorBracketMatch.border': '#58a6ff',
    // Warning squiggle color matches hole color (yellow)
    'editorWarning.foreground': '#' + SYNTAX_COLORS.hole,
  },
};

/**
 * Walk up a path trying to find a source range, either directly or via a mapper.
 */
function findRangeByWalkingPath(
  path: IndexPath,
  sourceMap: SourceMap,
  mapper?: (pathStr: string) => string | undefined
): SourceRange | null {
  let currentPath = path;
  while (currentPath.length >= 0) {
    const pathStr = serializeIndexPath(currentPath);
    const lookupKey = mapper ? mapper(pathStr) : pathStr;
    if (lookupKey) {
      const range = sourceMap.get(lookupKey);
      if (range) return range;
    }
    if (currentPath.length === 0) break;
    currentPath = currentPath.slice(0, -1);
  }
  return null;
}

/**
 * Walk up a kernel path to find a prefix in the elabMap, then append the
 * remaining suffix to the mapped surface path and look up in sourceMap.
 *
 * This preserves path precision: if the error path is
 *   kernel: type.body.body.body.domain.fn.arg.arg
 * and the elabMap maps:
 *   type.body.body.body.domain.fn → type.body.body.domain.fn
 * we reconstitute:
 *   type.body.body.domain.fn.arg.arg
 * and look that up in the sourceMap, finding the precise source range.
 *
 * Falls back to findRangeByWalkingPath (without suffix preservation) if
 * the reconstituted path doesn't match in the sourceMap.
 */
function findRangeViaElabMapWithSuffix(
  errorPath: IndexPath,
  elabMap: ElabMap,
  sourceMap: SourceMap
): SourceRange | null {
  // Try progressively shorter prefixes of the error path
  for (let prefixLen = errorPath.length; prefixLen >= 0; prefixLen--) {
    const prefix = errorPath.slice(0, prefixLen);
    const suffix = errorPath.slice(prefixLen);
    const prefixStr = serializeIndexPath(prefix);
    const mappedPrefix = elabMap.get(prefixStr);
    if (mappedPrefix !== undefined) {
      // Reconstitute: mapped prefix + remaining suffix
      const suffixStr = serializeIndexPath(suffix);
      const fullSurfacePath = mappedPrefix + (suffixStr ? '.' + suffixStr : '');
      // Try the reconstituted path directly
      const range = sourceMap.get(fullSurfacePath);
      if (range) return range;
      // Also try walking up from the reconstituted path
      // (the sourceMap might have a parent of this path)
    }
  }
  return null;
}

/**
 * Map an error path to a source range using the elab and source maps.
 * Returns null if mapping fails.
 */
function mapErrorPathToSourceRange(
  errorPath: IndexPath,
  elabMap: ElabMap | undefined,
  sourceMap: SourceMap | undefined,
  _blockStartLine: number  // Note: unused - sourceMap already has absolute positions
): SourceRange | null {
  if (!sourceMap) return null;

  // Try elabMap-based lookup FIRST (more precise for kernel errors).
  // The elabMap maps kernel paths to surface paths. By preserving the suffix
  // after the mapped prefix, we get precise source locations even when the
  // kernel has more binder levels than the surface (e.g., {x y : Nat} expands
  // to two kernel binders but is one surface binder).
  if (elabMap) {
    const mappedRange = findRangeViaElabMapWithSuffix(errorPath, elabMap, sourceMap);
    if (mappedRange) return mappedRange;
    // Fallback: elabMap lookup without suffix preservation
    const fallbackRange = findRangeByWalkingPath(errorPath, sourceMap, p => elabMap.get(p));
    if (fallbackRange) return fallbackRange;
  }

  // Try direct lookup in sourceMap (for elaboration errors where path is already a surface path)
  const directRange = findRangeByWalkingPath(errorPath, sourceMap);
  if (directRange) return directRange;

  return null;
}

/**
 * Extract parameter/index info from an inductive type's kernel type.
 * Returns array of { name, type, isIndex } for each position.
 */
function extractParamIndexInfo(
  kernelType: TTKTerm | undefined,
  indexPositions: number[] | undefined
): Array<{ name: string; type: string; isIndex: boolean }> {
  if (!kernelType) return [];

  const indexSet = new Set(indexPositions ?? []);
  const result: Array<{ name: string; type: string; isIndex: boolean }> = [];
  let current = kernelType;
  let position = 0;

  while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
    const name = current.name || '_';
    const type = prettyPrintTTK(current.domain);
    const isIndex = indexSet.has(position);
    result.push({ name, type, isIndex });
    current = current.body;
    position++;
  }

  return result;
}

// Monaco type helpers
type Monaco = typeof import('monaco-editor');
type IStandaloneCodeEditor = MonacoEditor.IStandaloneCodeEditor;

// CSS to ensure Monaco widgets render above everything
const MONACO_WIDGET_STYLES = `
  .monaco-hover,
  .monaco-editor .suggest-widget,
  .monaco-editor .parameter-hints-widget,
  .monaco-editor-overlaymessage,
  .monaco-editor .monaco-hover-content {
    z-index: 10001 !important;
  }
`;

const SAMPLE_CODE = `inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero b = b
plus (Succ a) b = Succ (plus a b)

inductive Vec : Type -> Nat -> Type where
  VNil : {A: Type} -> Vec A Zero
  VCons : {A : Type} -> {n : Nat} -> A -> Vec A n -> Vec A (Succ n)

inductive Fin : Nat -> Type where
  FZero : {n : Nat} -> Fin (Succ n)
  FSucc : {n : Nat} -> Fin n -> Fin (Succ n)

nth : {A : Type} -> {n : Nat} -> Vec A n -> Fin n -> A
nth (VCons h _) FZero = h
nth (VCons h tail) (FSucc f) = nth tail f

inductive Void : Type where

absurd : {A : Type} -> Void -> A

inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a

zeroNeqSucc : {n : Nat} -> Equal Zero (Succ n) -> Void
zeroNeqSucc refl = #absurd

double : Nat -> Nat
double n = ?sorry

right : {A : Type} -> {B : Type} -> B -> A -> B
right {A} b = \\(x: A) => b

qux : Type
qux = Nat

qux' : Nat -> Type
qux' n = Nat

const : {A : Type} -> {B : Type} -> A -> B -> A
const a = \\ _ => a

swap : {A B C : Type} -> (f : A -> B -> C) -> B -> A -> C
swap f = \\ x y => f y x

vecConcat : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat VNil v = v
vecConcat (VCons h tail) v = VCons h (vecConcat tail v)

vecConcat' : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat' VNil v = v
vecConcat' {a := Succ p} (VCons h tail) v = VCons h (vecConcat' {a := p} tail v)

vecConcat'' : {A : Type} -> {a b : Nat} -> Vec A a -> Vec A b -> Vec A (plus a b)
vecConcat'' VNil v = v
vecConcat'' {a:=Succ p} (VCons h tail) v = swap VCons (vecConcat'' {a:=(\\x => x) p} tail v) h

fox : Nat
fox = (\\x => x) Zero

sym : {A : Type} -> {u v : A} -> Equal u v -> Equal v u
sym refl = refl

trans : {A : Type} -> {u v w : A} -> Equal u v -> Equal v w -> Equal u w
trans refl refl = refl

cong : {A B : Type} -> {u v : A} -> {f : A -> B} -> Equal u v -> Equal (f u) (f v)
cong refl = refl

replace : {x y : Type} -> {f : Type -> Type} -> Equal x y -> f x -> f y
replace refl fx = fx

record Pair (A B : Type) : Type where
  constructor MkPair
  fst: A
  snd: B

inductive DPairInd : {u v : ULevel} -> (A : Type u) -> (B : A -> Type v) -> Type (UMax u v) where
  MkDPairInd: {u v : ULevel} -> {A : Type u} -> {B : A -> Type v} -> (a : A) -> B a -> DPairInd A B

record DPair {u v : ULevel} (A : Type u) (B : A -> Type v) : Type (UMax u v) where
  constructor MkDPair
  dfst: A
  dsnd: B dfst

record Semigroup {u : ULevel} (A : Type u) where
  op : A -> A -> A
  assoc : (a b c : A) -> Equal (op (op a b) c) (op a (op b c))

record Monoid {u : ULevel} (A : Type u) : Type u extends Semigroup {u} A where
  e : A
  identLeft : (a : A) -> Equal (op e a) a
  identRight : (a : A) -> Equal (op a e) a

record Group {u : ULevel} (A : Type u) : Type u extends Monoid A where
  inv : A -> A
  invLeft : (a : A) -> Equal (op (inv a) a) e
  invRight : (a : A) -> Equal (op a (inv a)) e

plusZeroRight : {n : Nat} -> Equal n (plus n Zero)
plusZeroRight {n:=Zero} = refl {A:=Nat} {a:=Zero}
plusZeroRight {n:=Succ n} = let rec = plusZeroRight {n} in
  cong rec

plusComm : {a b : Nat} -> Equal (plus a b) (plus b a)
plusComm {a:=Zero}   {b:=Zero}   = refl
plusComm {a:=Succ a} {b:=Zero}   = let tmp = plusZeroRight in ?B
plusComm {a:=Zero}   {b:=Succ b} = ?C
plusComm {a:=Succ a} {b:=Succ b} = ?D

inductive List : Type -> Type where
  Nil : {A : Type} -> List A
  Cons : {A : Type} -> A -> List A -> List A

inductive Bool : Type where
  True : Bool
  False : Bool

filter : {A : Type} -> (A -> Bool) -> List A -> List A
filter f Nil = Nil
filter f (Cons x xs) with f x
  | True => Cons x (filter f xs)
  | False => filter f xs

inductive DecEq : Nat -> Nat -> Type where
  Yes : {m n : Nat} -> Equal m n -> DecEq m n
  No : {m n : Nat} -> (Equal m n -> Void) -> DecEq m n

succInj : {j k : Nat} -> Equal (Succ j) (Succ k) -> Equal j k
succInj refl = refl

compose : {u v w : ULevel} -> {A : Type u} -> {B : Type v} -> {C : Type w} -> (B -> C) -> (A -> B) -> (A -> C)
compose g f = \\a => g (f a)

decEqNat : (x y : Nat) -> DecEq x y
decEqNat Zero Zero = Yes refl
decEqNat Zero (Succ y) = No zeroNeqSucc
decEqNat (Succ x) Zero = No (compose zeroNeqSucc sym)
decEqNat (Succ x) (Succ y) with decEqNat x y
  | Yes eq => Yes (cong eq)
  | No neq => No (compose neq succInj)
`;

const NAT_MATH_CODE = `-- Nat Math: semiring, triangle sum, and ordering proofs by pattern matching
-- Includes all 12 semiring properties, sum(1..n) = n(n+1)/2, and Leq properties

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)

one : Nat
one = Succ Zero

-- Helpers
congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

-- Addition properties
plusZeroLeft : (n : Nat) -> Equal (plus Zero n) n
plusZeroLeft n = refl

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n
plusZeroRight Zero = refl
plusZeroRight (Succ n) = congSucc (plusZeroRight n)

plusSuccRight : (n m : Nat) -> Equal (plus n (Succ m)) (Succ (plus n m))
plusSuccRight Zero m = refl
plusSuccRight (Succ n) m = congSucc (plusSuccRight n m)

plusAssoc : (n m p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p))
plusAssoc Zero m p = refl
plusAssoc (Succ n) m p = congSucc (plusAssoc n m p)

plusComm : (n m : Nat) -> Equal (plus n m) (plus m n)
plusComm Zero m = sym (plusZeroRight m)
plusComm (Succ n) m = trans (congSucc (plusComm n m)) (sym (plusSuccRight m n))

congPlusRight : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)
congPlusRight Zero eq = eq
congPlusRight (Succ p) eq = congSucc (congPlusRight p eq)

congPlusLeft : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus n p) (plus m p)
congPlusLeft p refl = refl

plusLeftComm : (m n p : Nat) -> Equal (plus m (plus n p)) (plus n (plus m p))
plusLeftComm m n p = trans (sym (plusAssoc m n p)) (trans (congPlusLeft p (plusComm m n)) (plusAssoc n m p))

-- Multiplication properties
mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero
mulZeroLeft n = refl

mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero
mulZeroRight Zero = refl
mulZeroRight (Succ n) = mulZeroRight n

mulOneLeft : (n : Nat) -> Equal (mul one n) n
mulOneLeft n = plusZeroRight n

mulOneRight : (n : Nat) -> Equal (mul n one) n
mulOneRight Zero = refl
mulOneRight (Succ n) = congSucc (mulOneRight n)

mulSuccRight : (n m : Nat) -> Equal (mul n (Succ m)) (plus n (mul n m))
mulSuccRight Zero m = refl
mulSuccRight (Succ n) m = congSucc (trans (congPlusRight m (mulSuccRight n m)) (plusLeftComm m n (mul n m)))

mulComm : (n m : Nat) -> Equal (mul n m) (mul m n)
mulComm Zero m = sym (mulZeroRight m)
mulComm (Succ n) m = trans (congPlusRight m (mulComm n m)) (sym (mulSuccRight m n))

mulDistribRight : (n m p : Nat) -> Equal (mul (plus n m) p) (plus (mul n p) (mul m p))
mulDistribRight Zero m p = refl
mulDistribRight (Succ n) m p = trans (congPlusRight p (mulDistribRight n m p)) (sym (plusAssoc p (mul n p) (mul m p)))

mulAssoc : (n m p : Nat) -> Equal (mul (mul n m) p) (mul n (mul m p))
mulAssoc Zero m p = refl
mulAssoc (Succ n) m p = trans (mulDistribRight m (mul n m) p) (congPlusRight (mul m p) (mulAssoc n m p))

mulDistribLeft : (n m p : Nat) -> Equal (mul n (plus m p)) (plus (mul n m) (mul n p))
mulDistribLeft Zero m p = refl
mulDistribLeft (Succ n) m p = trans (congPlusRight (plus m p) (mulDistribLeft n m p)) (trans (plusAssoc m p (plus (mul n m) (mul n p))) (trans (congPlusRight m (plusLeftComm p (mul n m) (mul n p))) (sym (plusAssoc m (mul n m) (plus p (mul n p))))))

-- Semiring record and instance
record Semiring (A : Type) where
  constructor MkSemiring
  add : A -> A -> A
  mul : A -> A -> A
  zero : A
  oneS : A
  addZeroLeft : (a : A) -> Equal (add zero a) a
  addZeroRight : (a : A) -> Equal (add a zero) a
  addComm : (a b : A) -> Equal (add a b) (add b a)
  addAssoc : (a b c : A) -> Equal (add (add a b) c) (add a (add b c))
  mulZeroL : (a : A) -> Equal (mul zero a) zero
  mulZeroR : (a : A) -> Equal (mul a zero) zero
  mulOneL : (a : A) -> Equal (mul oneS a) a
  mulOneR : (a : A) -> Equal (mul a oneS) a
  mulComm : (a b : A) -> Equal (mul a b) (mul b a)
  mulAssoc : (a b c : A) -> Equal (mul (mul a b) c) (mul a (mul b c))
  distribL : (a b c : A) -> Equal (mul a (add b c)) (add (mul a b) (mul a c))
  distribR : (a b c : A) -> Equal (mul (add a b) c) (add (mul a c) (mul b c))

natSemiring : Semiring Nat
natSemiring = MkSemiring plus mul Zero one plusZeroLeft plusZeroRight plusComm plusAssoc mulZeroLeft mulZeroRight mulOneLeft mulOneRight mulComm mulAssoc mulDistribLeft mulDistribRight

------------------------------------------------------------
-- Triangle Sum: 2 * sum(1..n) = n * (n + 1)
------------------------------------------------------------

-- Sum from 0 to n: sum(n) = 0 + 1 + 2 + ... + n
sum : Nat -> Nat
sum Zero = Zero
sum (Succ n) = plus (Succ n) (sum n)

-- Theorem: plus (sum n) (sum n) = mul n (Succ n)
-- i.e. 2 * sum(n) = n * (n + 1)
doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n))
doubleSum Zero = refl
doubleSum (Succ n) = trans (plusAssoc (Succ n) (sum n) (plus (Succ n) (sum n))) (trans (congPlusRight (Succ n) (plusLeftComm (sum n) (Succ n) (sum n))) (trans (congPlusRight (Succ n) (congPlusRight (Succ n) (doubleSum n))) (trans (congSucc (plusSuccRight n (plus n (mul n (Succ n))))) (congPlusRight (Succ (Succ n)) (sym (mulSuccRight n (Succ n)))))))

------------------------------------------------------------
-- Leq: ordering on Nat with reflexivity, transitivity, antisymmetry
------------------------------------------------------------

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

-- Reflexivity: a <= a
leqRefl : (n : Nat) -> Leq n n
leqRefl Zero = LeqZero
leqRefl (Succ n) = LeqSucc (leqRefl n)

-- Transitivity: a <= b /\\ b <= c => a <= c
leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c
leqTrans LeqZero _ = LeqZero
leqTrans (LeqSucc p) (LeqSucc q) = LeqSucc (leqTrans p q)

-- Antisymmetry: a <= b /\\ b <= a => a = b
leqAntisym : {a b : Nat} -> Leq a b -> Leq b a -> Equal a b
leqAntisym LeqZero LeqZero = refl
leqAntisym (LeqSucc p) (LeqSucc q) = congSucc (leqAntisym p q)
`;

const NAT_MATH_TACTICS_CODE = `-- Nat Math (Tactics): same theorems as Nat Math, proven via tactics
-- Showcases induction, multi-tactic branches, intro, exact, and more

inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

mul : Nat -> Nat -> Nat
mul Zero m = Zero
mul (Succ n) m = plus m (mul n m)

one : Nat
one = Succ Zero

-- Utility helpers (pattern matching — 1-line utility proofs)
congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl

congPlusRight : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus p n) (plus p m)
congPlusRight Zero eq = eq
congPlusRight (Succ p) eq = congSucc (congPlusRight p eq)

congPlusLeft : {n m : Nat} -> (p : Nat) -> Equal n m -> Equal (plus n p) (plus m p)
congPlusLeft p refl = refl

------------------------------------------------------------
-- Addition properties via tactics (induction on first arg)
------------------------------------------------------------

plusZeroLeft : (n : Nat) -> Equal (plus Zero n) n := by
  intro n; exact refl

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact (congSucc IH)

plusSuccRight : (n m : Nat) -> Equal (plus n (Succ m)) (Succ (plus n m)) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact refl
  | Succ n' IH =>
    intro m
    exact (congSucc (IH m))

plusAssoc : (n m p : Nat) -> Equal (plus (plus n m) p) (plus n (plus m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (congSucc (IH m p))

plusComm : (n m : Nat) -> Equal (plus n m) (plus m n) := by
  intro n
  induction n with
  | Zero =>
    intro m
    apply sym
    exact (plusZeroRight m)
  | Succ n' IH =>
    intro m
    apply trans
    apply congSucc
    exact (IH m)
    apply sym
    exact (plusSuccRight m n')

plusLeftComm : (m n p : Nat) -> Equal (plus m (plus n p)) (plus n (plus m p)) := by
  intros m n p
  apply trans
  exact (sym (plusAssoc m n p))
  apply trans
  exact (congPlusLeft p (plusComm m n))
  exact (plusAssoc n m p)

------------------------------------------------------------
-- Multiplication properties via tactics
------------------------------------------------------------

mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero := by
  intro n; exact refl

mulZeroRight : (n : Nat) -> Equal (mul n Zero) Zero := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact IH

mulOneLeft : (n : Nat) -> Equal (mul one n) n := by
  intro n; exact (plusZeroRight n)

mulOneRight : (n : Nat) -> Equal (mul n one) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact (congSucc IH)

mulSuccRight : (n m : Nat) -> Equal (mul n (Succ m)) (plus n (mul n m)) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact refl
  | Succ n' IH =>
    intro m
    exact (congSucc (trans (congPlusRight m (IH m)) (plusLeftComm m n' (mul n' m))))

mulComm : (n m : Nat) -> Equal (mul n m) (mul m n) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact (sym (mulZeroRight m))
  | Succ n' IH =>
    intro m
    exact (trans (congPlusRight m (IH m)) (sym (mulSuccRight m n')))

mulDistribRight : (n m p : Nat) -> Equal (mul (plus n m) p) (plus (mul n p) (mul m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (trans (congPlusRight p (IH m p)) (sym (plusAssoc p (mul n' p) (mul m p))))

mulAssoc : (n m p : Nat) -> Equal (mul (mul n m) p) (mul n (mul m p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p
    exact refl
  | Succ n' IH =>
    intros m p
    exact (trans (mulDistribRight m (mul n' m) p) (congPlusRight (mul m p) (IH m p)))

mulDistribLeft : (n m p : Nat) -> Equal (mul n (plus m p)) (plus (mul n m) (mul n p)) := by
  intro n
  induction n with
  | Zero =>
    intros m p; exact refl
  | Succ n' IH =>
    intros m p
    apply trans
    exact (congPlusRight (plus m p) (IH m p))
    apply trans
    exact (plusAssoc m p (plus (mul n' m) (mul n' p)))
    apply trans
    exact (congPlusRight m (plusLeftComm p (mul n' m) (mul n' p)))
    exact (sym (plusAssoc m (mul n' m) (plus p (mul n' p))))

------------------------------------------------------------
-- Triangle Sum: 2 * sum(1..n) = n * (n + 1)
------------------------------------------------------------

sum : Nat -> Nat
sum Zero = Zero
sum (Succ n) = plus (Succ n) (sum n)

-- Triangle sum proof: 2 * sum(1..n) = n * (n + 1)
-- Best-practice: incremental proof with apply/exact, not nested terms
doubleSum : (n : Nat) -> Equal (plus (sum n) (sum n)) (mul n (Succ n)) := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH =>
    -- Goal: (n'+1) + sum(n') + (n'+1) + sum(n') = (n'+1) * (n'+2)
    apply trans
    exact (plusAssoc (Succ n') (sum n') (plus (Succ n') (sum n')))
    apply trans
    apply congPlusRight
    exact (plusLeftComm (sum n') (Succ n') (sum n'))
    apply trans
    apply congPlusRight
    apply congPlusRight
    exact IH
    apply trans
    apply congSucc
    exact (plusSuccRight n' (plus n' (mul n' (Succ n'))))
    apply congPlusRight
    apply sym
    exact (mulSuccRight n' (Succ n'))

------------------------------------------------------------
-- Leq: ordering on Nat
------------------------------------------------------------

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqRefl : (n : Nat) -> Leq n n := by
  intro n
  induction n with
  | Zero => exact LeqZero
  | Succ n' IH => exact (LeqSucc IH)

leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c := by
  intros a b c hab hbc
  cases hab with
  | LeqZero => exact LeqZero
  | LeqSucc p =>
    cases hbc with
    | LeqSucc q => exact (LeqSucc (leqTrans p q))

leqAntisym : {a b : Nat} -> Leq a b -> Leq b a -> Equal a b := by
  intros a b hab hba
  cases hab with
  | LeqZero =>
    cases hba with
    | LeqZero => exact refl
  | LeqSucc p =>
    cases hba with
    | LeqSucc q => exact (congSucc (leqAntisym p q))

record DPair (A : Type) (fn : A -> Type) where
  fst : A
  snd : fn fst

succInj: {u v : Nat} -> Equal (Succ u) (Succ v) -> Equal u v 
succInj refl = refl

succCong: {u v : Nat} -> Equal u v -> Equal (Succ u) (Succ v)
succCong refl = refl

leqImpliesSum : (a b : Nat) -> Leq a b -> DPair Nat (\\n => Equal b (plus a n))
leqImpliesSum Zero b LeqZero = MkDPair b refl
leqImpliesSum (Succ a) (Succ b) (LeqSucc leq) with leqImpliesSum a b leq
  | MkDPair n pf => MkDPair n (succCong pf)

sigmaSumCount : (count : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSumCount Zero _ = Zero
sigmaSumCount (Succ k) fn = plus (sigmaSumCount k fn) (Succ k)

sigmaSumStartCount : (start count : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSumStartCount start count fn = sigmaSumCount count (\\index => fn (plus start index))

sigmaSumStartOrderedRange : (start end : Nat) -> Leq start end -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSumStartOrderedRange start end leq fn with leqImpliesSum start end leq
  | MkDPair count _ => sigmaSumStartCount start count fn

inductive Void : Type where

zeroNeqSucc : {n : Nat} -> (Equal Zero (Succ n) -> Void)

inductive DecEq : {A : Type} -> (a b : A) -> Type where
  Yes : {A : Type} -> {a b : A} -> Equal a b -> DecEq a b
  No : {A : Type} -> {a b : A} -> (Equal a b -> Void) -> DecEq a b

decEqNat : (x y : Nat) -> DecEq x y
decEqNat Zero Zero = Yes refl
decEqNat Zero (Succ y) = No zeroNeqSucc
decEqNat (Succ x) Zero = No (\\eq => zeroNeqSucc (sym eq))
decEqNat (Succ x) (Succ y) with decEqNat x y
  | Yes eq => Yes (succCong eq)
  | No neq => No (\\eq => neq (succInj eq))

LessThan : Nat -> Nat -> Type
LessThan a b = Leq (Succ a) b

inductive Either : Type -> Type -> Type where
  inl : {L R : Type} -> L -> Either L R
  inr : {L R : Type} -> R -> Either L R

decGeq : (a b : Nat) -> Either (Leq a b) (LessThan b a)
decGeq Zero b = inl LeqZero
decGeq (Succ a) Zero = inr (LeqSucc (LeqZero {n:=a}))
decGeq (Succ a) (Succ b) with decGeq a b
  | inl aLeqB => inl (LeqSucc aLeqB)
  | inr bLeA => inr (LeqSucc bLeA)

{-
sigmaSum : (start end : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSum start end fn with decGeq start end
  | inl startLeqEnd => sigmaSumStartOrderedRange start end startLeqEnd fn
  | inr endLeStart => Zero
-}

sigmaSum : (start end : Nat) -> (fn : (index : Nat) -> Nat) -> Nat
sigmaSum start end fn with decGeq start end
  | inl startLeqEnd with leqImpliesSum start end startLeqEnd
    | MkDPair count _ => sigmaSumStartCount start count fn
  | inr endLeStart => Zero
`;

const PRESETS: { name: string; code: string }[] = [
  { name: 'Grab Bag', code: SAMPLE_CODE },
  { name: 'Nat Math', code: NAT_MATH_CODE },
  { name: 'Nat Math (Tactics)', code: NAT_MATH_TACTICS_CODE },
];

// Styles
const styles = {
  container: {
    height: '100vh',
    width: '100%',
    backgroundColor: '#0d1117',
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  header: {
    padding: '16px 20px',
    color: '#c9d1d9',
    borderBottom: '1px solid #30363d',
    flexShrink: 0,
    display: 'flex' as const,
    justifyContent: 'space-between' as const,
    alignItems: 'center' as const,
  },
  title: {
    margin: 0,
    marginBottom: '4px',
    fontSize: '18px',
    fontWeight: 600,
  },
  subtitle: {
    margin: 0,
    fontSize: '13px',
    color: '#8b949e',
  },
  mainContent: {
    flex: 1,
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  editorSection: {
    flex: 1,
    minHeight: 0,
    borderBottom: '1px solid #30363d',
    display: 'flex',
    flexDirection: 'column' as const,
  },
  typeInfoPanel: {
    height: '120px',
    flexShrink: 0,
    borderBottom: '1px solid #30363d',
    backgroundColor: '#161b22',
    padding: '8px 16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '12px',
    color: '#c9d1d9',
    overflow: 'auto',
  },
  typeInfoLabel: {
    color: '#8b949e',
    fontSize: '10px',
    fontWeight: 600 as const,
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    marginBottom: '2px',
  },
  typeInfoValue: {
    color: '#79c0ff',
    marginBottom: '6px',
  },
  typeInfoContext: {
    color: '#c9d1d9',
    marginBottom: '2px',
  },
  typeInfoContextName: {
    color: '#d2a8ff',
  },
  typeInfoContextType: {
    color: '#79c0ff',
  },
  sectionHeader: {
    padding: '8px 16px',
    fontSize: '11px',
    fontWeight: 600,
    color: '#8b949e',
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
    backgroundColor: '#161b22',
    borderBottom: '1px solid #30363d',
  },
  editorWrapper: {
    flex: 1,
    overflow: 'hidden',
  },
  resultsSection: {
    flex: 1,
    minHeight: 0,
    display: 'flex',
    flexDirection: 'column' as const,
    overflow: 'hidden',
  },
  resultsContent: {
    flex: 1,
    overflow: 'auto',
    padding: '16px',
    fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
    fontSize: '13px',
  },
  blockCard: {
    backgroundColor: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    marginBottom: '12px',
    overflow: 'hidden',
  },
  blockHeader: {
    padding: '8px 12px',
    backgroundColor: '#21262d',
    borderBottom: '1px solid #30363d',
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  },
  blockBadge: {
    padding: '2px 8px',
    borderRadius: '4px',
    fontSize: '11px',
    fontWeight: 600,
  },
  blockBadgeInductive: {
    backgroundColor: 'rgba(136, 198, 190, 0.2)',
    color: '#88c6be',
  },
  blockBadgeTerm: {
    backgroundColor: 'rgba(88, 166, 255, 0.2)',
    color: '#58a6ff',
  },
  blockBadgeComment: {
    backgroundColor: 'rgba(110, 118, 129, 0.2)',
    color: '#6e7681',
  },
  blockBadgeError: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  blockBody: {
    padding: '12px',
  },
  declSection: {
    marginBottom: '12px',
  },
  declName: {
    color: '#e6edf3',
    fontWeight: 600,
    marginBottom: '4px',
  },
  typeRow: {
    display: 'flex',
    gap: '8px',
    marginBottom: '4px',
  },
  typeLabel: {
    color: '#8b949e',
    minWidth: '50px',
  },
  typeValue: {
    color: '#7ee787',
  },
  valueValue: {
    color: '#d2a8ff',
    whiteSpace: 'pre-wrap',
  },
  ctorRow: {
    marginLeft: '16px',
    marginBottom: '2px',
  },
  ctorName: {
    color: '#ffa657',
  },
  errorText: {
    color: '#f85149',
  },
  warningText: {
    color: '#d29922',
  },
};

// ============================================================================
// Case Tree Visualization
// ============================================================================

const caseTreeStyles = {
  container: {
    marginTop: '12px',
    padding: '12px',
    backgroundColor: '#0d1117',
    borderRadius: '4px',
    border: '1px solid #30363d',
    fontSize: '12px',
    fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
  },
  header: {
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
    marginBottom: '8px',
    color: '#8b949e',
    fontSize: '11px',
    fontWeight: 600,
    textTransform: 'uppercase' as const,
    letterSpacing: '0.5px',
  },
  exhaustiveBadge: {
    padding: '2px 6px',
    borderRadius: '3px',
    fontSize: '10px',
    fontWeight: 600,
  },
  exhaustiveYes: {
    backgroundColor: 'rgba(63, 185, 80, 0.2)',
    color: '#3fb950',
  },
  exhaustiveNo: {
    backgroundColor: 'rgba(248, 81, 73, 0.2)',
    color: '#f85149',
  },
  treeNode: {
    paddingLeft: '16px',
    //borderLeft: '1px solid #30363d',
    marginLeft: '4px',
  },
  splitLabel: {
    color: '#8b949e',
    marginBottom: '4px',
  },
  branchRow: {
    display: 'flex',
    alignItems: 'flex-start',
    marginBottom: '4px',
  },
  ctorName: {
    color: '#ffa657',
    //minWidth: '80px',
  },
  frozenCtorName: {
    color: '#6e7681',
    fontStyle: 'italic' as const,
  },
  leafClause: {
    color: '#7ee787',
  },
  uncovered: {
    color: '#f85149',
    fontStyle: 'italic' as const,
  },
  absurd: {
    color: '#8b949e',
    fontStyle: 'italic' as const,
  },
  unreachableWarning: {
    marginTop: '8px',
    padding: '8px',
    backgroundColor: 'rgba(248, 81, 73, 0.1)',
    borderRadius: '4px',
    color: '#f85149',
    fontSize: '11px',
  },
};

/**
 * Render a case tree node recursively.
 * @param tree The case tree node
 * @param depth Current nesting depth (for indentation)
 */
function CaseTreeNode({ tree, depth = 0 }: { tree: CaseTree; depth?: number }): JSX.Element {
  if (tree.tag === 'Leaf') {
    return <span style={caseTreeStyles.leafClause}>→ clause {tree.clauseIndex}</span>;
  }

  if (tree.tag === 'Uncovered') {
    return <span style={caseTreeStyles.uncovered}>→ MISSING</span>;
  }

  if (tree.tag === 'Absurd') {
    return <span style={caseTreeStyles.absurd}>→ absurd</span>;
  }

  if (tree.tag === 'NoSplit') {
    return (
      <div style={depth > 0 ? caseTreeStyles.treeNode : undefined}>
        <div style={caseTreeStyles.branchRow}>
          <span style={caseTreeStyles.ctorName}>_</span>
          <CaseTreeNode tree={tree.branch} depth={depth + 1} />
        </div>
      </div>
    )
  }

  // Split node - all constructors are enumerated
  const branches = Array.from(tree.branches.entries());

  return (
    <div style={depth > 0 ? caseTreeStyles.treeNode : undefined}>
      {branches.map(([ctorName, subTree]) => (
        <div key={ctorName} style={caseTreeStyles.branchRow}>
          <span style={caseTreeStyles.ctorName}>{ctorName}</span>
          <CaseTreeNode tree={subTree} depth={depth + 1} />
        </div>
      ))}
    </div>
  );
}

/**
 * Render totality checking results with case tree visualization
 */
function TotalityResultView({ result }: { result: TotalityResult }): JSX.Element | null {
  if (!result.caseTree) {
    return null;
  }

  return (
    <div style={caseTreeStyles.container}>
      <div style={caseTreeStyles.header}>
        <span>Case Tree</span>
        <span style={{
          ...caseTreeStyles.exhaustiveBadge,
          ...(result.isExhaustive ? caseTreeStyles.exhaustiveYes : caseTreeStyles.exhaustiveNo)
        }}>
          {result.isExhaustive ? 'Exhaustive' : 'Non-exhaustive'}
        </span>
      </div>
      <table>
        <tbody>
          {...caseTreeRows(result.caseTree, result.frozenPositionCount ?? 0)}
        </tbody>
      </table>
      {result.unreachableClauses.length > 0 && (
        <div style={caseTreeStyles.unreachableWarning}>
          Warning: Unreachable clause(s): {result.unreachableClauses.map(i => i.clauseIndex + 1).join(', ')}
        </div>
      )}
    </div>
  );
}

// Helper to collect labels from the first N NoSplit nodes, returning [labels, remainingTree]
function collectNoSplitLabels(tree: CaseTree, count: number): [string[], CaseTree] {
  const labels: string[] = [];
  let current = tree;
  for (let i = 0; i < count; i++) {
    if (current.tag === 'NoSplit') {
      labels.push(current.debugLabel);
      current = current.branch;
    } else {
      // If we hit something other than NoSplit, fill remaining with '_'
      labels.push('_');
    }
  }
  return [labels, current];
}

function caseTreeRows(tree: CaseTree, frozenRemaining: number = 0): JSX.Element[] {
  if (tree.tag === 'Split') {
    return Array.from(tree.branches.entries()).map(([ctorName, subTree]) => {
      const arity = tree.ctorArities.get(ctorName) ?? 0;
      // Collect argument labels from child NoSplit nodes
      const [argLabels, remainingTree] = collectNoSplitLabels(subTree, arity);
      // Render constructor with its arguments: (Succ a) for arity 1, (VCons h t) for arity 2, etc.
      const ctorDisplay = arity === 0
        ? ctorName
        : `(${ctorName} ${argLabels.join(' ')})`;
      const childRows = caseTreeRows(remainingTree, frozenRemaining);
      return (
        <tr key={ctorName}>
          <td><span style={caseTreeStyles.ctorName}>{ctorDisplay}</span></td>
          <td>
            {childRows.length > 0 && (
              <table style={{ borderCollapse: 'collapse' }}><tbody>{childRows}</tbody></table>
            )}
          </td>
        </tr>
      );
    });
  } else if (tree.tag === 'NoSplit') {
    const isFrozen = frozenRemaining > 0;
    const childRows = caseTreeRows(tree.branch, frozenRemaining > 0 ? frozenRemaining - 1 : 0);
    const style = isFrozen ? caseTreeStyles.frozenCtorName : caseTreeStyles.ctorName;
    return [
      <tr key={tree.debugLabel}>
        <td><span style={style}>{tree.debugLabel}</span></td>
        <td>
          {childRows.length > 0 && (
            <table style={{ borderCollapse: 'collapse' }}><tbody>{childRows}</tbody></table>
          )}
        </td>
      </tr>
    ];
  } else if (tree.tag === 'Leaf') {
    return [
      <tr key={tree.clauseIndex}>
        <td><span style={caseTreeStyles.leafClause}>→ clause {tree.clauseIndex}</span></td>
      </tr>
    ];
  } else if (tree.tag === 'Uncovered') {
    return [
      <tr key="uncovered">
        <td><span style={caseTreeStyles.uncovered}>⚠ uncovered</span></td>
      </tr>
    ];
  }

  return [];
}

// Block renderer component
interface RenderOptions {
  showNamedArgsWithLabels: boolean;
  showNamedParamsWithBraces: boolean;
  definitions: DefinitionsMap;
}

function BlockRenderer({ block, renderOptions }: { block: CompiledBlock; renderOptions: RenderOptions }) {
  const { showNamedArgsWithLabels, showNamedParamsWithBraces, definitions } = renderOptions;
  const namedArgLookup = useMemo(() => createNamedArgLookup(definitions), [definitions]);

  // Helper to generate pretty type string with options
  const getPrettyType = useCallback((kernelType: TTKTerm | undefined, namedArgMap?: NamedArgMap): string | undefined => {
    if (!kernelType) return undefined;
    const options: PrettyPrintOptions = {
      namedArgLookup,
      showNamedArgsWithLabels,
      signatureNamedArgMap: showNamedParamsWithBraces ? namedArgMap : undefined,
    };
    return prettyPrintFormatted(kernelType, [], undefined, options);
  }, [namedArgLookup, showNamedArgsWithLabels, showNamedParamsWithBraces]);

  // Helper to generate pretty value string with options
  const getPrettyValue = useCallback((kernelValue: TTKTerm | undefined): string | undefined => {
    if (!kernelValue) return undefined;
    const options: PrettyPrintOptions = {
      namedArgLookup,
      showNamedArgsWithLabels,
    };
    return prettyPrintFormatted(kernelValue, [], undefined, options);
  }, [namedArgLookup, showNamedArgsWithLabels]);

  let blockHeaderContent: React.ReactNode = null;
  let blockBodyContent: React.ReactNode = null;

  if (block.isComment) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeComment }}>Comment</span>;
    blockBodyContent = <pre style={{ margin: 0, color: '#6e7681' }}>
      {block.sourceLines.join('\n')}
    </pre>;
  }

  if (!block.parseSuccess) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Parse Error</span>;
    blockBodyContent = block.parseErrors.map((err, i) => (
      <div key={i} style={styles.errorText}>
        Line {err.line}, Col {err.col}: {err.message}
      </div>
    ));
  }

  if (!block.nameResolutionSuccess) {
    blockHeaderContent = <span style={{ ...styles.blockBadge, ...styles.blockBadgeError }}>Name Error</span>;
    blockBodyContent = block.nameResolutionErrors.map((err, i) => (
      <div key={i} style={styles.errorText}>{err.message}</div>
    ));
  }

  if (blockHeaderContent && blockBodyContent) {
    return (
      <BlockCard header={blockHeaderContent} body={blockBodyContent} initiallyExpanded={false} />
    );
  }

  return (
    <div style={styles.blockCard}>
      {block.declarations.map((decl, i) => {
        // Extract param/index info for inductive types
        const paramIndexInfo = decl.kind === 'inductive'
          ? extractParamIndexInfo(decl.kernelType, decl.indexPositions)
          : [];

        return (
          <BlockCard
            key={i}
            initiallyExpanded={decl.checkSuccess === false}
            header={
              <>
                <span style={{
                  ...styles.blockBadge,
                  ...(decl.kind === 'inductive' ? styles.blockBadgeInductive : styles.blockBadgeTerm)
                }}>
                  {decl.kind === 'inductive' ? 'Inductive' : 'Term'}
                </span>
                {decl.name && <span style={styles.declName}>{decl.name}</span>}
                {/* Display param/index info for inductive types */}
                {paramIndexInfo.length > 0 && (
                  <span style={{ marginLeft: '12px', fontSize: '11px', color: '#8b949e' }}>
                    {paramIndexInfo.map((info, j) => (
                      <span key={j} style={{ marginRight: '8px' }}>
                        <span style={{ color: info.isIndex ? '#f0883e' : '#7ee787' }}>
                          [{info.isIndex ? 'index' : 'param'} {info.name} : {info.type}]
                        </span>
                      </span>
                    ))}
                  </span>
                )}
                {decl.checkSuccess ? (
                  <span style={{ marginLeft: 'auto', color: '#3fb950', fontSize: '12px' }}>OK</span>
                ) : decl.checkErrors && decl.checkErrors.length > 0 ? (
                  (() => {
                    const errors = decl.checkErrors.filter(e => e.severity === 'error').length;
                    const warnings = decl.checkErrors.filter(e => e.severity === 'warning').length;
                    return (
                      <span style={{ marginLeft: 'auto', fontSize: '12px' }}>
                        {errors > 0 && <span style={{ color: '#f85149' }}>{errors} error{errors !== 1 ? 's' : ''}</span>}
                        {errors > 0 && warnings > 0 && <span style={{ color: '#8b949e' }}>, </span>}
                        {warnings > 0 && <span style={{ color: '#d29922' }}>{warnings} warning{warnings !== 1 ? 's' : ''}</span>}
                      </span>
                    );
                  })()
                ) : null}
              </>
            }
            body={
              <>
                {decl.kernelType && (
                  <div style={styles.typeRow}>
                    <span style={styles.typeLabel}>Type:</span>
                    <span style={styles.typeValue}>
                      {getPrettyType(decl.kernelType, decl.name ? namedArgLookup(decl.name) : undefined)}
                    </span>
                  </div>
                )}
                {decl.kernelValue && (
                  <div style={styles.typeRow}>
                    <span style={styles.typeLabel}>Value:</span>
                    <span style={styles.valueValue}>{getPrettyValue(decl.kernelValue)}</span>
                  </div>
                )}
                {decl.kernelConstructors && decl.kernelConstructors.length > 0 && (
                  <div>
                    <div style={{ ...styles.typeLabel, marginBottom: '4px' }}>Constructors:</div>
                    {decl.kernelConstructors.map((ctor, j) => (
                      <div key={j} style={styles.ctorRow}>
                        <span style={styles.ctorName}>{ctor.name}</span>
                        <span style={{ color: '#8b949e' }}> : </span>
                        <span style={styles.typeValue}>{getPrettyType(ctor.type, ctor.namedArgMap)}</span>
                      </div>
                    ))}
                  </div>
                )}
                {decl.prettyProjections && decl.prettyProjections.length > 0 && (
                  <div style={{ marginTop: '8px' }}>
                    <div style={{ ...styles.typeLabel, marginBottom: '4px' }}>Projections:</div>
                    {decl.prettyProjections.map((proj, j) => (
                      <div key={j} style={styles.ctorRow}>
                        <span style={{ color: '#58a6ff' }}>{proj.name}</span>
                        <span style={{ color: '#8b949e' }}> : </span>
                        <span style={styles.typeValue}>{proj.prettyType}</span>
                      </div>
                    ))}
                  </div>
                )}
                {decl.checkErrors && decl.checkErrors.length > 0 && (
                  <div style={{ marginTop: '8px' }}>
                    {decl.checkErrors.map((err, j) => (
                      <div key={j} style={err.severity === 'warning' ? styles.warningText : styles.errorText}>
                        {err.message}
                      </div>
                    ))}
                  </div>
                )}
                {decl.withClauseErrors && decl.withClauseErrors.length > 0 && (
                  <div style={{ marginTop: '8px' }}>
                    {decl.withClauseErrors.map((err, j) => (
                      <div key={`with-${j}`} style={styles.errorText}>{err.message}</div>
                    ))}
                  </div>
                )}
                {decl.totalityResult && (
                  <TotalityResultView result={decl.totalityResult} />
                )}</>
            }
          />
        )
      })}
    </div>
  );
}

function BlockCard(props: { header: React.ReactNode, body: React.ReactNode, initiallyExpanded?: boolean }) {
  const [expanded, setExpanded] = useState(props.initiallyExpanded ?? true)

  return (
    <div style={styles.blockCard}>
      <div style={styles.blockHeader} onClick={() => setExpanded(e => !e)}>
        {props.header}
      </div>
      {expanded && <div style={styles.blockBody}>
        {props.body}
      </div>}
    </div>
  )
}

export function TextEditorPage() {
  const [searchParams, setSearchParams] = useSearchParams();
  const editorRef = useRef<IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);
  const [code, setCode] = useState(SAMPLE_CODE);
  const [editorReady, setEditorReady] = useState(false);
  const [presetMenuOpen, setPresetMenuOpen] = useState(false);
  // Rendering options for pretty-printed output
  const [showNamedArgsWithLabels, setShowNamedArgsWithLabels] = useState(true);
  const [showNamedParamsWithBraces, setShowNamedParamsWithBraces] = useState(false);
  // Cursor position for type-at-cursor panel
  // Cursor/selection position for type-at-cursor panel
  const [cursorInfo, setCursorInfo] = useState<{
    lineNumber: number; column: number;
    selStartLine?: number; selStartCol?: number;
    selEndLine?: number; selEndCol?: number;
  } | null>(null);
  // Ref to store current compile result (for hover provider)
  const compileResultRef = useRef<CompileResult | null>(null);
  // Ref to store current wildcard hints (updated from compileResult)
  const wildcardHintsRef = useRef<WildcardInlayHint[]>([]);
  // Ref to store current semantic tokens (updated from compileResult)
  const semanticTokensRef = useRef<SemanticToken[]>([]);
  // Event emitter for semantic tokens changes
  const semanticTokensEventRef = useRef<{
    fire: () => void;
    event: import('monaco-editor').IEvent<void>;
  } | null>(null);

  // Load preset from URL parameter on mount
  useEffect(() => {
    const presetParam = searchParams.get('preset');
    if (presetParam) {
      const preset = PRESETS.find(p => p.name.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '') === presetParam);
      if (preset) {
        setCode(preset.code);
      }
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []); // Only run on mount

  // Helper function to load a preset and update URL
  const loadPreset = useCallback((presetName: string) => {
    const preset = PRESETS.find(p => p.name === presetName);
    if (preset) {
      setCode(preset.code);
      // Convert preset name to URL-friendly format: "Nat Math (Tactics)" -> "nat-math-tactics"
      const urlSafePresetName = preset.name.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');
      setSearchParams({ preset: urlSafePresetName });
      setPresetMenuOpen(false);
    }
  }, [setSearchParams]);

  // Inject Monaco widget z-index styles on mount
  useEffect(() => {
    const styleId = 'monaco-widget-z-index-fix';
    if (!document.getElementById(styleId)) {
      const style = document.createElement('style');
      style.id = styleId;
      style.textContent = MONACO_WIDGET_STYLES;
      document.head.appendChild(style);
    }
    return () => {
      const style = document.getElementById(styleId);
      if (style) {
        style.remove();
      }
    };
  }, []);

  // Compile and type check the source code
  const compileResult = useMemo<CompileResult>(() => {
    return compileTTFromText(code);
  }, [code]);

  // Extract wildcard hints from compile result
  const wildcardHints = useMemo(() => {
    return extractWildcardInlayHints(compileResult);
  }, [compileResult]);

  // Extract semantic tokens from compile result
  const semanticTokens = useMemo(() => {
    return extractSemanticTokens(compileResult, code);
  }, [compileResult, code]);

  // Extract hole locations from compile result for warning markers
  const holeLocations = useMemo(() => {
    return extractHoleLocations(compileResult);
  }, [compileResult]);

  // Compute type info at cursor position or selection
  const typeInfoAtCursor = useMemo<(CursorQueryResult & { expression?: string }) | undefined>(() => {
    if (!cursorInfo) return undefined;

    const hasSelection = cursorInfo.selStartLine !== undefined &&
      cursorInfo.selEndLine !== undefined &&
      (cursorInfo.selStartLine !== cursorInfo.selEndLine || cursorInfo.selStartCol !== cursorInfo.selEndCol);

    // Find which block the cursor is in
    const cursorLine = cursorInfo.lineNumber;
    let targetBlock: CompiledBlock | undefined;
    let targetDecl: CompiledDeclaration | undefined;

    for (const block of compileResult.blocks) {
      const blockEndLine = block.startLine + block.sourceLines.length - 1;
      if (cursorLine >= block.startLine && cursorLine <= blockEndLine) {
        targetBlock = block;
        for (const decl of block.declarations) {
          // Consider declarations with typeInfoMap (for terms) or tacticInfoTree (for tactics)
          if (decl.sourceMap && (decl.typeInfoMap || decl.tacticInfoTree)) {
            targetDecl = decl;
            for (const [, range] of decl.sourceMap) {
              if (range.start.line <= cursorLine && cursorLine <= range.end.line) {
                targetDecl = decl;
                break;
              }
            }
          }
        }
        break;
      }
    }

    // Need either typeInfoMap (for terms) or tacticInfoTree (for tactics)
    if (!targetBlock || !targetDecl || !targetDecl.sourceMap) {
      return undefined;
    }
    if (!targetDecl.typeInfoMap && !targetDecl.tacticInfoTree) {
      return undefined;
    }

    const lines = code.split('\n');

    // Helper: convert file-absolute line/col to file-absolute character offset
    // (sourceMap pos values are file-absolute)
    const toFileOffset = (line: number, col: number) => {
      let offset = 0;
      for (let i = 0; i < line - 1; i++) {
        offset += lines[i].length + 1;
      }
      offset += col - 1;
      return offset;
    };

    let cursorQueryResult: CursorQueryResult | undefined;
    try {
      if (hasSelection) {
        const startOffset = toFileOffset(cursorInfo.selStartLine!, cursorInfo.selStartCol!);
        const endOffset = toFileOffset(cursorInfo.selEndLine!, cursorInfo.selEndCol!);
        cursorQueryResult = getTypeAtSelection(startOffset, endOffset, targetDecl.sourceMap, targetDecl.elabMap, targetDecl.typeInfoMap, targetDecl.tacticInfoTree, compileResult.definitions, code);
      }
      if (!cursorQueryResult) {
        const cursorOffset = toFileOffset(cursorInfo.lineNumber, cursorInfo.column);
        cursorQueryResult = getTypeAtCursor(cursorOffset, targetDecl.sourceMap, targetDecl.elabMap, targetDecl.typeInfoMap, targetDecl.tacticInfoTree, compileResult.definitions, code);
      }

      // Accept both term and tactic results
      if (!cursorQueryResult) return undefined;
    } catch (e) {
      return undefined;
    }

    // Extract source expression text for term results
    let expression = '';
    if (cursorQueryResult.kind === 'term') {
      const result = cursorQueryResult.info;
      if (result.sourceRange) {
        const sr = result.sourceRange;
        if (sr.start.line === sr.end.line) {
          expression = lines[sr.start.line - 1].substring(sr.start.col - 1, sr.end.col - 1);
        } else {
          const parts: string[] = [];
          parts.push(lines[sr.start.line - 1].substring(sr.start.col - 1));
          for (let i = sr.start.line; i < sr.end.line - 1; i++) {
            parts.push(lines[i]);
          }
          parts.push(lines[sr.end.line - 1].substring(0, sr.end.col - 1));
          expression = parts.join(' ');
        }
      }
    }

    return { ...cursorQueryResult, expression };
  }, [cursorInfo, compileResult, code]);

  // Keep the refs in sync with the latest data
  // Monaco's providers will read from these refs when they need to render
  useEffect(() => {
    compileResultRef.current = compileResult;
  }, [compileResult]);

  useEffect(() => {
    wildcardHintsRef.current = wildcardHints;
  }, [wildcardHints]);

  useEffect(() => {
    semanticTokensRef.current = semanticTokens;
    // Signal Monaco to refresh semantic tokens
    if (semanticTokensEventRef.current) {
      semanticTokensEventRef.current.fire();
    }
  }, [semanticTokens]);

  const handleEditorChange: OnChange = useCallback((value) => {
    setCode(value || '');
  }, []);

  // Update Monaco markers with compile errors
  useEffect(() => {
    const monaco = monacoRef.current;
    const editor = editorRef.current;
    if (!monaco || !editor) return;

    const model = editor.getModel();
    if (!model) return;

    const markers: MonacoEditor.IMarkerData[] = [];

    // Add markers for all block errors
    for (const block of compileResult.blocks) {
      // Parse errors
      for (const error of block.parseErrors) {
        const lineContent = model.getLineContent(error.line);
        const endCol = Math.max(error.col + 1, lineContent.length + 1);

        markers.push({
          severity: monaco.MarkerSeverity.Error,
          message: (error.message || 'Parse error').replace(/^Parse error at line \d+, col \d+: /, ''),
          startLineNumber: error.line,
          startColumn: error.col,
          endLineNumber: error.line,
          endColumn: endCol,
          source: 'TT Parser',
        });
      }

      // Name resolution errors
      for (const err of block.nameResolutionErrors) {
        let sourceRange: SourceRange | null = null;

        // Try to look up the source range using the path and declaration's sourceMap
        if (err.path && err.declarationIndex !== undefined) {
          const decl = block.declarations[err.declarationIndex];
          if (decl?.sourceMap) {
            // Name resolution path is already a surface path, look it up directly
            sourceRange = decl.sourceMap.get(err.path) ?? null;
          }
        }

        if (sourceRange) {
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: err.message,
            startLineNumber: sourceRange.start.line,
            startColumn: sourceRange.start.col,
            endLineNumber: sourceRange.end.line,
            endColumn: sourceRange.end.col,
            source: 'TT Name Resolution',
          });
        } else {
          // Fallback: mark the first line of the block
          const firstLine = block.startLine;
          markers.push({
            severity: monaco.MarkerSeverity.Error,
            message: err.message,
            startLineNumber: firstLine,
            startColumn: 1,
            endLineNumber: firstLine,
            endColumn: model.getLineContent(firstLine).length + 1,
            source: 'TT Name Resolution',
          });
        }
      }

      // Type check errors from declarations
      for (const decl of block.declarations) {
        // Skip auxiliary declarations — their errors are promoted to the main declaration
        if (decl.isWithAuxiliary) continue;

        if (decl.checkErrors && decl.checkErrors.length > 0) {
          for (const err of decl.checkErrors) {
            // Try to map error path to precise source location
            const sourceRange = mapErrorPathToSourceRange(
              err.env.indexPath,
              decl.elabMap,
              decl.sourceMap,
              block.startLine
            );

            if (sourceRange) {
              // Use the mapped source range
              markers.push({
                severity: err.severity === 'warning'
                  ? monaco.MarkerSeverity.Warning
                  : monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: sourceRange.start.line,
                startColumn: sourceRange.start.col,
                endLineNumber: sourceRange.end.line,
                endColumn: sourceRange.end.col,
                source: 'TT Type Checker',
              });
            } else {
              // Fallback: mark the first line of the block
              const firstLine = block.startLine;
              markers.push({
                severity: err.severity === 'warning'
                  ? monaco.MarkerSeverity.Warning
                  : monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: firstLine,
                startColumn: 1,
                endLineNumber: firstLine,
                endColumn: model.getLineContent(firstLine).length + 1,
                source: 'TT Type Checker',
              });
            }
          }
        }

        // Also create markers for promoted with-clause errors
        if (decl.withClauseErrors && decl.withClauseErrors.length > 0) {
          for (const err of decl.withClauseErrors) {
            // With-clause error paths are in auxiliary kernel space — must map through
            // withClauseElabMap first. Skip direct sourceMap lookup (it would match wrong
            // entries since the auxiliary's clause indices differ from the main declaration's).
            const sourceRange = (decl.withClauseElabMap && decl.sourceMap)
              ? findRangeByWalkingPath(err.env.indexPath, decl.sourceMap, p => decl.withClauseElabMap!.get(p))
              : null;

            if (sourceRange) {
              markers.push({
                severity: monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: sourceRange.start.line,
                startColumn: sourceRange.start.col,
                endLineNumber: sourceRange.end.line,
                endColumn: sourceRange.end.col,
                source: 'TT Type Checker',
              });
            } else {
              // Fallback: mark the first line of the block
              const firstLine = block.startLine;
              markers.push({
                severity: monaco.MarkerSeverity.Error,
                message: err.message,
                startLineNumber: firstLine,
                startColumn: 1,
                endLineNumber: firstLine,
                endColumn: model.getLineContent(firstLine).length + 1,
                source: 'TT Type Checker',
              });
            }
          }
        }
      }
    }

    // Add warning markers for holes (user-created holes are unsound)
    for (const hole of holeLocations) {
      markers.push({
        severity: monaco.MarkerSeverity.Warning,
        message: `Holes are unsound.`,
        startLineNumber: hole.line,
        startColumn: hole.column,
        endLineNumber: hole.line,
        endColumn: hole.endColumn,
        source: 'TT Holes',
      });
    }

    monaco.editor.setModelMarkers(model, 'tt-compiler', markers);
  }, [compileResult, editorReady, holeLocations]);

  const handleEditorDidMount: OnMount = (editor, monaco) => {
    editorRef.current = editor;
    monacoRef.current = monaco;
    setEditorReady(true);

    // Register TT language
    monaco.languages.register({ id: 'tt' });

    // Language configuration for editing behaviors (comment toggling, brackets, etc.)
    monaco.languages.setLanguageConfiguration('tt', {
      comments: {
        lineComment: '--',
        blockComment: ['{-', '-}'],
      },
      brackets: [
        ['{', '}'],
        ['[', ']'],
        ['(', ')'],
      ],
      autoClosingPairs: [
        { open: '{', close: '}' },
        { open: '[', close: ']' },
        { open: '(', close: ')' },
        { open: '"', close: '"', notIn: ['string'] },
        { open: '{-', close: '-}' },
      ],
      surroundingPairs: [
        { open: '{', close: '}' },
        { open: '[', close: ']' },
        { open: '(', close: ')' },
        { open: '"', close: '"' },
      ],
    });

    // Simplified tokenizer - semantic tokens from parse tree handle identifier classification
    monaco.languages.setMonarchTokensProvider('tt', {
      tokenizer: {
        root: [
          // Comments - multiline {- -} must come FIRST
          [/\{-/, 'comment', '@comment'],
          [/--.*$/, 'comment'],

          // Type keywords (Type, Prop, ULevel, USucc, UMax, UIMax)
          [/\b(Type|Prop|ULevel|USucc|UMax|UIMax)\b/, 'type.identifier'],

          // Keywords
          [/\b(inductive|record|constructor|extends|where|let|in|fun|with|by)\b/, 'keyword'],

          // Absurd marker
          [/#absurd\b/, 'keyword'],

          // Ellipsis (with-clause parent pattern repetition)
          [/\.\.\./, 'keyword.operator'],

          // Holes (unfinished code that needs attention)
          [/\?[a-zA-Z_][a-zA-Z0-9_']*/, 'variable.predefined'],

          // Wildcards (will be solved during elaboration)
          [/_/, 'variable.wildcard'],

          // Numbers (including ω for universe levels)
          [/\d+/, 'number'],
          [/ω/, 'number'],

          // Identifiers - semantic tokens will override with proper classification
          [/[a-zA-Z_][a-zA-Z0-9_']*/, 'identifier'],

          // Operators
          [/->|=>/, 'keyword.operator'],
          [/[=:+\-*/\\<>!|]+/, 'delimiter'],  // Includes := which gets same color as =

          // Brackets and delimiters
          [/[()[\]{}]/, 'delimiter.bracket'],
          [/[,.]/, 'delimiter'],

          // Whitespace
          [/\s+/, 'white'],
        ],

        comment: [
          [/[^{-]+/, 'comment'],
          [/-\}/, 'comment', '@pop'],
          [/[{-]/, 'comment'],
        ],
      }
    });

    // Define and apply custom theme
    monaco.editor.defineTheme('tt-dark', MONACO_THEME);
    monaco.editor.setTheme('tt-dark');

    // Set the model language
    const model = editor.getModel();
    if (model) {
      monaco.editor.setModelLanguage(model, 'tt');
    }

    // Register inlay hints provider for wildcard names
    monaco.languages.registerInlayHintsProvider('tt', {
      provideInlayHints: (_model: MonacoEditor.ITextModel, range: { startLineNumber: number; endLineNumber: number }) => {
        const hints = wildcardHintsRef.current;
        const inlayHints: import('monaco-editor').languages.InlayHint[] = [];

        for (const hint of hints) {
          // Check if hint is within the requested range
          if (hint.line >= range.startLineNumber && hint.line <= range.endLineNumber) {
            inlayHints.push({
              kind: monaco.languages.InlayHintKind.Parameter,
              position: { lineNumber: hint.line, column: hint.column },
              label: hint.name,
              paddingLeft: false,
              paddingRight: false,
            });
          }
        }

        return { hints: inlayHints, dispose: () => { } };
      }
    });

    // Track cursor position and selection for the type info panel (debounced via rAF)
    let cursorRafId: number | null = null;
    editor.onDidChangeCursorSelection((e) => {
      if (cursorRafId !== null) cancelAnimationFrame(cursorRafId);
      cursorRafId = requestAnimationFrame(() => {
        cursorRafId = null;
        const sel = e.selection;
        setCursorInfo({
          lineNumber: sel.positionLineNumber,
          column: sel.positionColumn,
          selStartLine: sel.startLineNumber,
          selStartCol: sel.startColumn,
          selEndLine: sel.endLineNumber,
          selEndCol: sel.endColumn,
        });
      });
    });

    // Register semantic tokens provider for precise highlighting
    // This overrides lexical highlighting with semantic information from the compiler
    const tokenTypes = ['termName', 'constName', 'boundVar', 'patternVar', 'absurd', 'namedBrace', 'tacticName', 'directive', 'directiveValue'];
    const tokenModifiers: string[] = [];

    // Create an event emitter for signaling token changes
    const emitter = new monaco.Emitter<void>();
    semanticTokensEventRef.current = {
      fire: () => emitter.fire(),
      event: emitter.event
    };

    monaco.languages.registerDocumentSemanticTokensProvider('tt', {
      getLegend: () => ({
        tokenTypes,
        tokenModifiers
      }),
      onDidChange: emitter.event,
      provideDocumentSemanticTokens: (model: MonacoEditor.ITextModel) => {
        const tokens = semanticTokensRef.current;

        // Monaco expects delta-encoded tokens:
        // [deltaLine, deltaStartChar, length, tokenType, tokenModifiers]
        // Tokens must be sorted by line, then column
        const sortedTokens = [...tokens].sort((a, b) => {
          if (a.line !== b.line) return a.line - b.line;
          return a.column - b.column;
        });

        const data: number[] = [];
        let prevLine = 0;
        let prevCol = 0;

        for (const token of sortedTokens) {
          const tokenTypeIndex = tokenTypes.indexOf(token.type);
          if (tokenTypeIndex === -1) continue;

          // Validate and clamp token bounds: Monaco rejects tokens where end character exceeds line length
          const monacoLine = token.line;  // 1-indexed
          if (monacoLine < 1 || monacoLine > model.getLineCount()) continue;
          const lineLength = model.getLineLength(monacoLine);
          const startCol0 = token.column - 1;  // Convert to 0-indexed
          if (startCol0 < 0 || startCol0 >= lineLength) continue;
          // Clamp length to line boundary (source map ranges can be slightly over due to
          // how prefixSourceMapPaths adjusts ranges during application parsing)
          const clampedLength = Math.min(token.length, lineLength - startCol0);

          const deltaLine = token.line - 1 - prevLine;  // Monaco is 0-indexed
          const deltaCol = deltaLine === 0 ? token.column - 1 - prevCol : token.column - 1;

          data.push(deltaLine, deltaCol, clampedLength, tokenTypeIndex, 0);

          prevLine = token.line - 1;
          prevCol = token.column - 1;
        }

        return {
          data: new Uint32Array(data),
          resultId: undefined
        };
      },
      releaseDocumentSemanticTokens: () => { }
    });

    // Unicode abbreviation replacement (Lean-style)
    // Replace abbreviations immediately when typed (no space required)
    // Undo restores the abbreviation without re-converting (so you can type \omega literally if needed)
    editor.onDidChangeModelContent((e) => {
      // Skip if this is an undo/redo operation - allows escaping via undo
      if (e.isUndoing || e.isRedoing) return;

      // Only process single-character insertions (typing)
      if (e.changes.length !== 1) return;
      const change = e.changes[0];
      if (change.text.length !== 1) return;

      const model = editor.getModel();
      if (!model) return;

      const position = editor.getPosition();
      if (!position) return;

      // Get the text up to and including the cursor
      const lineContent = model.getLineContent(position.lineNumber);
      const textUpToCursor = lineContent.substring(0, position.column - 1);

      // Check if the text ends with an abbreviation
      const match = textUpToCursor.match(ABBREV_PATTERN);
      if (!match) return;

      const abbrev = match[1];
      const replacement = UNICODE_ABBREVIATIONS[abbrev];
      if (!replacement) return;

      // Calculate the range to replace
      const abbrevStartCol = position.column - abbrev.length;
      const abbrevEndCol = position.column;

      const range = {
        startLineNumber: position.lineNumber,
        startColumn: abbrevStartCol,
        endLineNumber: position.lineNumber,
        endColumn: abbrevEndCol
      };

      // Use a timeout to avoid recursion and ensure the edit happens after current processing
      setTimeout(() => {
        // Push an undo stop so the replacement is a separate undo operation
        // This way: undo goes ω → \omega, not ω → \ome
        editor.pushUndoStop();
        editor.executeEdits('unicode-abbrev', [{
          range,
          text: replacement,
          forceMoveMarkers: true
        }]);
      }, 0);
    });
  };

  return (
    <div style={styles.container}>
      <div style={styles.header}>
        <div>
          <h2 style={styles.title}>Text Editor</h2>
          <p style={styles.subtitle}>Edit code and view compilation results</p>
        </div>
        <div style={{ position: 'relative' as const }}>
          <button
            onClick={() => setPresetMenuOpen(!presetMenuOpen)}
            style={{
              background: '#21262d',
              color: '#c9d1d9',
              border: '1px solid #30363d',
              borderRadius: '6px',
              padding: '6px 12px',
              fontSize: '13px',
              cursor: 'pointer',
              whiteSpace: 'nowrap' as const,
            }}
          >
            Load Preset ▾
          </button>
          {presetMenuOpen && (
            <div style={{
              position: 'absolute' as const,
              right: 0,
              top: '100%',
              marginTop: '4px',
              background: '#161b22',
              border: '1px solid #30363d',
              borderRadius: '6px',
              overflow: 'hidden',
              zIndex: 100,
              minWidth: '180px',
              boxShadow: '0 8px 24px rgba(0,0,0,0.4)',
            }}>
              {PRESETS.map((preset) => (
                <div
                  key={preset.name}
                  onClick={() => loadPreset(preset.name)}
                  style={{
                    padding: '8px 16px',
                    cursor: 'pointer',
                    fontSize: '13px',
                    color: '#c9d1d9',
                    borderBottom: '1px solid #21262d',
                  }}
                  onMouseEnter={(e) => { (e.target as HTMLElement).style.background = '#30363d'; }}
                  onMouseLeave={(e) => { (e.target as HTMLElement).style.background = 'transparent'; }}
                >
                  {preset.name}
                </div>
              ))}
            </div>
          )}
        </div>
      </div>

      <div style={styles.mainContent}>
        {/* Source Code Editor - Top Half */}
        <div style={styles.editorSection}>
          <div style={styles.sectionHeader}>Source Code</div>
          <div style={styles.editorWrapper}>
            <Editor
              height="100%"
              defaultLanguage="tt"
              value={code}
              onChange={handleEditorChange}
              onMount={handleEditorDidMount}
              options={{
                minimap: { enabled: false },
                fontSize: 13,
                lineNumbers: 'on',
                scrollBeyondLastLine: false,
                automaticLayout: true,
                wordWrap: 'off',
                folding: true,
                renderWhitespace: 'selection',
                fixedOverflowWidgets: true,
                'semanticHighlighting.enabled': true,
              }}
            />
          </div>
        </div>

        {/* Type Info Panel */}
        <div style={styles.typeInfoPanel}>
          {typeInfoAtCursor ? (
            <>
              {/* Case 1: Term type info */}
              {typeInfoAtCursor.kind === 'term' && (
                <>
                  <div>
                    <span style={styles.typeInfoValue}>
                      {typeInfoAtCursor.expression
                        ? `${typeInfoAtCursor.expression} : ${typeInfoAtCursor.info.prettyType}`
                        : typeInfoAtCursor.info.prettyType}
                    </span>
                  </div>
                  {typeInfoAtCursor.info.expectedType &&
                    typeInfoAtCursor.info.surfacePath.includes('clauses[') && (
                      <div>
                        <span style={styles.typeInfoLabel}>Expected </span>
                        <span style={styles.typeInfoValue}>{typeInfoAtCursor.info.expectedType}</span>
                      </div>
                    )}
                  {typeInfoAtCursor.info.context.length > 0 && (
                    <div>
                      <div style={styles.typeInfoLabel}>Context</div>
                      {typeInfoAtCursor.info.context.map((entry: { name: string; type: string }, i: number) => (
                        <div key={i} style={styles.typeInfoContext}>
                          <span style={styles.typeInfoContextName}>{entry.name}</span>
                          <span style={{ color: '#8b949e' }}> : </span>
                          <span style={styles.typeInfoContextType}>{entry.type}</span>
                        </div>
                      ))}
                    </div>
                  )}
                </>
              )}

              {/* Case 2: Tactic goal states */}
              {typeInfoAtCursor.kind === 'tactic' && (
                <>
                  {typeInfoAtCursor.goalStates.length === 0 ? (
                    <div style={styles.typeInfoValue}>No goals (proof complete)</div>
                  ) : (
                    typeInfoAtCursor.goalStates.map((goal: GoalState, idx: number) => {
                      // Extract context names for better pretty printing
                      const contextNames = goal.hypotheses.map(h => h.name);

                      return (
                        <div key={goal.id} style={{ marginBottom: idx < typeInfoAtCursor.goalStates.length - 1 ? '12px' : '0' }}>
                          {/* Goal header */}
                          {(typeInfoAtCursor.goalStates.length > 1 || goal.caseTag) && (
                            <div style={styles.typeInfoLabel}>
                              {typeInfoAtCursor.goalStates.length > 1 && `Goal ${idx + 1}/${typeInfoAtCursor.goalStates.length}`}
                              {typeInfoAtCursor.goalStates.length > 1 && goal.caseTag && ' '}
                              {goal.caseTag && `(${goal.caseTag})`}
                            </div>
                          )}

                          {/* Hypotheses (what's in scope) */}
                          {goal.hypotheses.length > 0 && (
                            <div style={{ marginTop: (typeInfoAtCursor.goalStates.length > 1 || goal.caseTag) ? '8px' : '0' }}>
                              <div style={styles.typeInfoLabel}>Hypotheses</div>
                              {goal.hypotheses.map((hyp, i) => (
                                <div key={i} style={styles.typeInfoContext}>
                                  <span style={styles.typeInfoContextName}>{hyp.name}</span>
                                  <span style={{ color: '#8b949e' }}> : </span>
                                  <span style={styles.typeInfoContextType}>
                                    {prettyPrintTTK(hyp.type, contextNames.slice(0, i), new Map())}
                                  </span>
                                </div>
                              ))}
                            </div>
                          )}

                          {/* Target (goal to prove) */}
                          <div style={{ marginTop: '8px' }}>
                            <div style={styles.typeInfoLabel}>Goal</div>
                            <span style={styles.typeInfoValue}>
                              {prettyPrintTTK(goal.target, contextNames, new Map())}
                            </span>
                          </div>
                        </div>
                      );
                    })
                  )}
                </>
              )}
            </>
          ) : (
            <span style={{ color: '#484f58' }}>Move cursor over an expression or tactic to see info</span>
          )}
        </div>

        {/* Compile Results - Bottom Half */}
        <div style={styles.resultsSection}>
          <div style={styles.sectionHeader}>
            <span>
              Compile Results
              {!compileResult.success && (
                <span style={{ marginLeft: '8px', color: '#f85149' }}>
                  ({compileResult.totalParseErrors + compileResult.totalNameErrors + compileResult.totalCheckErrors} errors)
                </span>
              )}
            </span>
            <span style={{ marginLeft: 'auto', display: 'flex', gap: '16px', fontSize: '11px', color: '#8b949e' }}>
              <label style={{ display: 'flex', alignItems: 'center', gap: '4px', cursor: 'pointer' }}>
                <input
                  type="checkbox"
                  checked={showNamedArgsWithLabels}
                  onChange={(e) => setShowNamedArgsWithLabels(e.target.checked)}
                  style={{ cursor: 'pointer' }}
                />
                Show named args as {'{A:=...}'}
              </label>
              <label style={{ display: 'flex', alignItems: 'center', gap: '4px', cursor: 'pointer' }}>
                <input
                  type="checkbox"
                  checked={showNamedParamsWithBraces}
                  onChange={(e) => setShowNamedParamsWithBraces(e.target.checked)}
                  style={{ cursor: 'pointer' }}
                />
                Show named params as {'{A : Type}'}
              </label>
            </span>
          </div>
          <div style={styles.resultsContent}>
            {compileResult.blocks.map((block, i) => (
              <BlockRenderer
                key={i}
                block={block}
                renderOptions={{
                  showNamedArgsWithLabels,
                  showNamedParamsWithBraces,
                  definitions: compileResult.definitions,
                }}
              />
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}
