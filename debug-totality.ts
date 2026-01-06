import { checkSourceBlocks } from './src/parser/block-checker';
import { checkFunctionTotality, prettyPrintSplitTree, analyzeTotality, formatMissingCase } from './src/types/ttk-totality-check';
import { mkConst, mkType, mkPi } from './src/types/tt-kernel';

// Test manually with the exact patterns
const natType = mkConst('Nat', mkType(1));

// Test 1: plus : Nat -> Nat -> Nat
// plus Zero b = b           -- clause 0: [Zero, PVar]
// plus (Succ a) Zero = a    -- clause 1: [Succ(PVar), Zero]

console.log("=== Test 1: plus ===");
const clauses1 = [
  {
    patterns: [
      { tag: 'PCtor' as const, name: 'Zero', args: [] },
      { tag: 'PVar' as const, name: 'b' }
    ],
    rhs: { tag: 'Var' as const, index: 0, type: natType }
  },
  {
    patterns: [
      { tag: 'PCtor' as const, name: 'Succ', args: [{ tag: 'PVar' as const, name: 'a' }] },
      { tag: 'PCtor' as const, name: 'Zero', args: [] }
    ],
    rhs: { tag: 'Var' as const, index: 1, type: natType }
  }
];

// Context with Nat and its constructors
const ctx = [
  { name: 'Nat', type: mkType(1) },
  { name: 'Zero', type: natType },
  { name: 'Succ', type: mkPi(natType, natType, 'n') }
];

const analysis1 = analyzeTotality(clauses1, [natType, natType], ctx);
console.log("  exhaustive:", analysis1.exhaustive);
console.log("  missingCases:");
for (const mc of analysis1.missingCases) {
  console.log("    ", formatMissingCase("plus", mc));
}

// Test 2: p : Nat -> Nat -> Nat with deeper nesting
// p Zero b = b
// p (Succ a) Zero = Succ (p a a)
// p (Succ a) (Succ (Succ b)) = Succ (p a a)
// Missing: p (Succ a) (Succ Zero)

console.log("\n=== Test 2: p with nested Succ ===");
const clauses2 = [
  {
    patterns: [
      { tag: 'PCtor' as const, name: 'Zero', args: [] },
      { tag: 'PVar' as const, name: 'b' }
    ],
    rhs: { tag: 'Var' as const, index: 0, type: natType }
  },
  {
    patterns: [
      { tag: 'PCtor' as const, name: 'Succ', args: [{ tag: 'PVar' as const, name: 'a' }] },
      { tag: 'PCtor' as const, name: 'Zero', args: [] }
    ],
    rhs: { tag: 'Var' as const, index: 1, type: natType }
  },
  {
    patterns: [
      { tag: 'PCtor' as const, name: 'Succ', args: [{ tag: 'PVar' as const, name: 'a' }] },
      { tag: 'PCtor' as const, name: 'Succ', args: [
        { tag: 'PCtor' as const, name: 'Succ', args: [{ tag: 'PVar' as const, name: 'b' }] }
      ] }
    ],
    rhs: { tag: 'Var' as const, index: 1, type: natType }
  }
];

const analysis2 = analyzeTotality(clauses2, [natType, natType], ctx);
console.log("  exhaustive:", analysis2.exhaustive);
console.log("  missingCases:");
for (const mc of analysis2.missingCases) {
  console.log("    ", formatMissingCase("p", mc));
}
