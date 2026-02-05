/**
 * Test what getTypeAtCursor returns when cursor is on a tactic
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { getTypeAtCursor } from './type-info';

describe('Cursor position in tactic blocks', () => {
  test('returns tactic info when cursor on intro keyword', () => {
    const source = `
id : {A : Type} -> A -> A := by
  intro A
  intro a
  exact a
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const decl = result.blocks[0].declarations[0];
    console.log('\n=== Declaration ===');
    console.log('Name:', decl.name);
    console.log('Has tacticInfoTree:', !!decl.tacticInfoTree);

    if (decl.tacticInfoTree) {
      const nodes = decl.tacticInfoTree.getAllNodes();
      console.log('\n=== InfoTree Nodes ===');
      nodes.forEach((node, i) => {
        console.log(`Node ${i}:`, {
          position: node.position,
          goalsBefore: node.goalsBefore.length,
          goalsAfter: node.goalsAfter.length,
          tactic: node.tactic.tag
        });
      });
    }

    // Find position of "intro A" in source
    const lines = source.split('\n');
    console.log('\n=== Source Lines ===');
    lines.forEach((line, i) => {
      console.log(`Line ${i}:`, JSON.stringify(line));
    });

    // Line 2 is "  intro A" - let's find its character position
    let pos = 0;
    for (let i = 0; i < 2; i++) {
      pos += lines[i].length + 1; // +1 for newline
    }
    pos += 2; // Skip the two spaces

    console.log('\n=== Query at "intro A" ===');
    console.log('Position:', pos, '(line 2, col 2)');

    const cursorResult = getTypeAtCursor(
      pos,
      decl.sourceMap ?? new Map(),
      decl.elabMap ?? new Map(),
      decl.typeInfoMap,
      decl.tacticInfoTree,
      result.definitions
    );

    console.log('\n=== Cursor Result ===');
    if (cursorResult) {
      console.log('Kind:', cursorResult.kind);
      if (cursorResult.kind === 'tactic') {
        console.log('Goal states:', cursorResult.goalStates.length);
        cursorResult.goalStates.forEach((goal, i) => {
          console.log(`Goal ${i}:`, {
            hypotheses: goal.hypotheses.length,
            target: goal.target.tag
          });
        });
      } else {
        console.log('Term info:', cursorResult.info.prettyType);
      }
    } else {
      console.log('Result: undefined');
    }

    expect(cursorResult).toBeDefined();
  });
});
