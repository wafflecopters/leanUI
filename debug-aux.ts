import { compileTTFromText } from './src/compiler/compile';
import { extractNamedArgMap, countParameters, reorderPatterns } from './src/compiler/elab';

const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

inductive Leq : Nat -> Nat -> Type where
  LeqZero : {n : Nat} -> Leq Zero n
  LeqSucc : {n m : Nat} -> Leq n m -> Leq (Succ n) (Succ m)

leqCanonical : {a b : Nat} -> (p q : Leq a b) -> Equal p q
leqCanonical LeqZero LeqZero = refl
leqCanonical (LeqSucc pleq) (LeqSucc qleq) with leqCanonical pleq qleq
  | refl => refl
`;

const result = compileTTFromText(source);
for (const block of result.blocks) {
  for (const decl of block.declarations) {
    if (decl.name && decl.name.includes('with')) {
      console.log('=== Auxiliary:', decl.name, '===');

      // Get the surface type
      const surfType = decl.surfaceType;
      if (surfType) {
        const namedArgMap = extractNamedArgMap(surfType);
        const totalArity = countParameters(surfType);
        console.log('namedArgMap:', Array.from(namedArgMap.entries()));
        console.log('totalArity:', totalArity);

        // Get surface clause patterns
        if (decl.surfaceValue && decl.surfaceValue.tag === 'Match') {
          for (let ci = 0; ci < decl.surfaceValue.clauses.length; ci++) {
            const clause = decl.surfaceValue.clauses[ci];
            console.log(`clause ${ci} patterns:`, clause.patterns.map((p: any) =>
              p.tag === 'PVar' ? `PVar(${p.name})` :
              p.tag === 'PWild' ? 'PWild' :
              p.tag === 'PCtor' ? `PCtor(${p.name})` : p.tag
            ));
            console.log(`clause ${ci} namedPatterns:`, clause.namedPatterns);

            // Try reorderPatterns
            const reorderResult = reorderPatterns(clause.patterns, namedArgMap, clause.namedPatterns, totalArity);
            if (reorderResult.error) {
              console.log('reorder ERROR:', reorderResult.error);
            } else {
              console.log('reordered:', reorderResult.ordered!.map((p: any) =>
                p.tag === 'PVar' ? `PVar(${p.name})` :
                p.tag === 'PWild' ? 'PWild' :
                p.tag === 'PCtor' ? `PCtor(${p.name})` : p.tag
              ));
              console.log('varIndexPermutation:', reorderResult.varIndexPermutation);
              console.log('sourceIndexMap:', reorderResult.sourceIndexMap);
            }
          }
        }
      }
    }
  }
}
