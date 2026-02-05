/**
 * Test that simulates EXACTLY what the browser does
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { getTypeAtCursor } from './type-info';

describe('Browser scenario simulation', () => {
  test('simulate user putting cursor on intro line', () => {
    const source = `
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

mulZeroLeft : (n : Nat) -> Equal (mul Zero n) Zero := by
  intro n
  exact refl
`;

    console.log('=== COMPILING ===');
    const result = compileTTFromText(source);
    console.log('Compile success:', result.success);
    console.log('Num blocks:', result.blocks.length);

    if (!result.success) {
      console.log('ERRORS:', result.blocks.flatMap(b => b.declarations).flatMap(d => d.checkErrors));
      return;
    }

    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'mulZeroLeft');
    console.log('\n=== DECLARATION ===');
    console.log('Found mulZeroLeft:', !!decl);
    console.log('Has sourceMap:', !!decl?.sourceMap);
    console.log('Has typeInfoMap:', !!decl?.typeInfoMap);
    console.log('Has tacticInfoTree:', !!decl?.tacticInfoTree);

    if (decl?.tacticInfoTree) {
      const nodes = decl.tacticInfoTree.getAllNodes();
      console.log('\n=== TACTIC INFO TREE ===');
      console.log('Num nodes:', nodes.length);
      nodes.forEach((node, i) => {
        console.log(`Node ${i}:`, {
          position: node.position,
          tactic: node.tactic.tag,
          goalsBefore: node.goalsBefore.length,
          goalsAfter: node.goalsAfter.length
        });
      });
    }

    // Find the line with "intro n"
    const lines = source.split('\n');
    const introLineIdx = lines.findIndex(l => l.trim().startsWith('intro n'));
    console.log('\n=== LINE SEARCH ===');
    console.log('intro n line index:', introLineIdx);
    console.log('Line content:', JSON.stringify(lines[introLineIdx]));

    // Calculate offset to column 3 (on the 'i' of intro)
    let offset = 0;
    for (let i = 0; i < introLineIdx; i++) {
      offset += lines[i].length + 1;
    }
    offset += 2; // Skip two spaces to column 3

    console.log('\n=== CURSOR QUERY ===');
    console.log(`Clicking at line ${introLineIdx + 1}, col 3 (intro n)`);
    console.log('Offset:', offset);
    console.log('Character at offset:', source[offset], source.substring(offset, offset + 5));

    const queryResult = getTypeAtCursor(
      offset,
      decl!.sourceMap ?? new Map(),
      decl!.elabMap ?? new Map(),
      decl!.typeInfoMap,
      decl!.tacticInfoTree,
      result.definitions,
      source
    );

    console.log('\n=== QUERY RESULT ===');
    if (!queryResult) {
      console.log('Result: UNDEFINED - THIS IS THE BUG!');
    } else {
      console.log('Result kind:', queryResult.kind);
      if (queryResult.kind === 'tactic') {
        console.log('Goal states:', queryResult.goalStates.length);
        queryResult.goalStates.forEach((goal, i) => {
          console.log(`  Goal ${i}:`, {
            hypotheses: goal.hypotheses.map(h => `${h.name}: ${h.type.tag}`),
            target: goal.target.tag
          });
        });
      } else {
        console.log('Term info:', queryResult.info.prettyType);
      }
    }

    expect(queryResult).toBeDefined();
    expect(queryResult!.kind).toBe('tactic');
  });
});
