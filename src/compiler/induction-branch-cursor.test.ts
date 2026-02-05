/**
 * Test cursor on tactics inside induction branches
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { getTypeAtCursor } from './type-info';

describe('Cursor on tactics in induction branches', () => {
  test('cursor on intro inside Zero branch', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

plusSuccRight : (n m : Nat) -> Equal (plus n (Succ m)) (Succ (plus n m)) := by
  intro n
  induction n with
  | Zero =>
    intro m
    exact refl
  | Succ n' IH =>
    intro m
    exact (congSucc (IH m))
`;

    console.log('=== COMPILING ===');
    const result = compileTTFromText(source);
    console.log('Compile success:', result.success);

    if (!result.success) {
      console.log('ERRORS:', result.blocks.flatMap(b => b.declarations.flatMap(d => d.checkErrors)));
      return;
    }

    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'plusSuccRight');
    console.log('\n=== DECLARATION ===');
    console.log('Found plusSuccRight:', !!decl);
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

    // Find the "intro m" line inside Zero branch
    const lines = source.split('\n');
    const zeroIntroLineIdx = lines.findIndex((l, idx) => {
      // Look for "intro m" after "| Zero =>"
      return idx > 0 && l.trim() === 'intro m' && lines[idx - 1].includes('| Zero =>');
    });

    console.log('\n=== LINE SEARCH ===');
    console.log('Zero intro m line index:', zeroIntroLineIdx);
    if (zeroIntroLineIdx >= 0) {
      console.log('Line content:', JSON.stringify(lines[zeroIntroLineIdx]));
    }

    // Calculate offset to "intro" keyword
    let offset = 0;
    for (let i = 0; i < zeroIntroLineIdx; i++) {
      offset += lines[i].length + 1;
    }
    // Skip leading spaces to get to 'i' in intro
    const leadingSpaces = lines[zeroIntroLineIdx].length - lines[zeroIntroLineIdx].trimStart().length;
    offset += leadingSpaces;

    console.log('\n=== CURSOR QUERY ===');
    console.log(`Clicking at line ${zeroIntroLineIdx + 1}, on "intro m"`);
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
      console.log('Result: UNDEFINED');
    } else {
      console.log('Result kind:', queryResult.kind);
      if (queryResult.kind === 'tactic') {
        console.log('Goal states:', queryResult.goalStates.length);
        queryResult.goalStates.forEach((goal, i) => {
          console.log(`  Goal ${i}:`, {
            hypotheses: goal.hypotheses.map(h => h.name),
            caseTag: goal.caseTag
          });
        });
      }
    }

    // The test expectation - we should get tactic info
    expect(queryResult).toBeDefined();
    if (queryResult) {
      expect(queryResult.kind).toBe('tactic');
    }
  });
});
