import { checkSourceBlocks } from './src/parser/block-checker';
import { checkFunctionTotality, prettyPrintSplitTree, analyzeTotality } from './src/types/ttk-totality-check';
import { mkConst, mkType, mkPi } from './src/types/tt-kernel';

// Test manually with the exact patterns
const natType = mkConst('Nat', mkType(1));

// plus : Nat -> Nat -> Nat
// plus Zero b = b           -- clause 0: [Zero, PVar]
// plus (Succ a) Zero = a    -- clause 1: [Succ(PVar), Zero]

const clauses = [
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

console.log("=== Clauses ===");
for (const c of clauses) {
  console.log("  patterns:", JSON.stringify(c.patterns));
}

console.log("\n=== analyzeTotality ===");
const analysis = analyzeTotality(clauses, [natType, natType], ctx);
console.log("  exhaustive:", analysis.exhaustive);
console.log("  missingCases:", analysis.missingCases);
console.log("\n=== Split Tree ===");
console.log(prettyPrintSplitTree(analysis.splitTree));
