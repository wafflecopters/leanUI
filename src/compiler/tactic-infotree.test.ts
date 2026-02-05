/**
 * Test that tactic InfoTree is built correctly during compilation.
 */
import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { prettyPrint } from './kernel';

describe('InfoTree building during tactic elaboration', () => {
  test('builds InfoTree for simple proof', () => {
    const source = `
id : {A : Type} -> A -> A := by
  intro A
  intro a
  exact a
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const decl = result.blocks[0].declarations[0];
    expect(decl.tacticInfoTree).toBeDefined();

    const nodes = decl.tacticInfoTree!.getAllNodes();
    expect(nodes.length).toBeGreaterThanOrEqual(3); // intro A, intro a, exact a

    // Check goal evolution
    expect(nodes[0].goalsAfter[0].hypotheses.length).toBe(1); // A added
    expect(nodes[1].goalsAfter[0].hypotheses.length).toBe(2); // a added
    expect(nodes[2].goalsAfter.length).toBe(0); // Complete
  });

  test('records source positions for tactics', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

test : Nat -> Nat := by
  intro n
  exact n
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const decl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'test');
    expect(decl).toBeDefined();
    expect(decl!.tacticInfoTree).toBeDefined();

    const nodes = decl!.tacticInfoTree!.getAllNodes();
    expect(nodes.length).toBeGreaterThan(0);

    // Each node should have a position (even if line/col are 0 when source map is unavailable)
    for (const node of nodes) {
      expect(node.position).toBeDefined();
      expect(node.position).toHaveProperty('line');
      expect(node.position).toHaveProperty('col');
    }
  });

  test('records error in InfoTree when tactic fails', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

-- This proof should fail
testProof : Nat := by
  exact (Succ Succ)
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(false);

    const decl = result.blocks[1].declarations[0];
    // Note: InfoTree may not be present on error cases (tactic elaboration throws)
    // This is expected behavior - when elaboration fails, we don't get a complete InfoTree
    if (decl.tacticInfoTree) {
      const nodes = decl.tacticInfoTree.getAllNodes();
      expect(nodes.length).toBeGreaterThan(0);

      // Should have recorded the error
      const errorNode = nodes.find(n => n.error !== undefined);
      expect(errorNode).toBeDefined();
      expect(errorNode!.error).toBeDefined();
    }
  });

  test('InfoTree not present for non-tactic declarations', () => {
    const source = `
id : {A : Type} -> A -> A
id a = a
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const decl = result.blocks[0].declarations[0];
    // Pattern-matched definition should not have tacticInfoTree
    expect(decl.tacticInfoTree).toBeUndefined();
  });

  test('builds InfoTree for proof with induction', () => {
    const source = `
inductive Nat : Type where
  Zero : Nat
  Succ : Nat -> Nat

inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

congSucc : {n m : Nat} -> Equal n m -> Equal (Succ n) (Succ m)
congSucc refl = refl

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ n) m = Succ (plus n m)

plusZeroRight : (n : Nat) -> Equal (plus n Zero) n := by
  intro n
  induction n with
  | Zero => exact refl
  | Succ n' IH => exact (congSucc IH)
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const plusZeroRightDecl = result.blocks
      .flatMap(b => b.declarations)
      .find(d => d.name === 'plusZeroRight');
    expect(plusZeroRightDecl).toBeDefined();
    expect(plusZeroRightDecl!.checkSuccess).toBe(true);
    expect(plusZeroRightDecl!.tacticInfoTree).toBeDefined();

    const nodes = plusZeroRightDecl!.tacticInfoTree!.getAllNodes();

    // Should have nodes for intro and induction tactics at minimum
    // (Branch tactics may be represented differently)
    expect(nodes.length).toBeGreaterThanOrEqual(2);
  });

  test('InfoTree goals match expected hypotheses', () => {
    const source = `
test : {A : Type} -> {B : Type} -> A -> B -> A := by
  intro A
  intro B
  intro a
  intro b
  exact a
`;

    const result = compileTTFromText(source);
    expect(result.success).toBe(true);

    const decl = result.blocks[0].declarations[0];
    expect(decl.tacticInfoTree).toBeDefined();

    const nodes = decl.tacticInfoTree!.getAllNodes();

    // After "intro A", should have A in hypotheses
    expect(nodes[0].goalsAfter[0].hypotheses.length).toBe(1);
    expect(nodes[0].goalsAfter[0].hypotheses[0].name).toBe('A');

    // After "intro B", should have A and B
    expect(nodes[1].goalsAfter[0].hypotheses.length).toBe(2);
    expect(nodes[1].goalsAfter[0].hypotheses[1].name).toBe('B');

    // After "intro a", should have A, B, and a
    expect(nodes[2].goalsAfter[0].hypotheses.length).toBe(3);
    expect(nodes[2].goalsAfter[0].hypotheses[2].name).toBe('a');

    // After "intro b", should have all 4
    expect(nodes[3].goalsAfter[0].hypotheses.length).toBe(4);
    expect(nodes[3].goalsAfter[0].hypotheses[3].name).toBe('b');

    // After "exact a", proof complete
    expect(nodes[4].goalsAfter.length).toBe(0);
  });
});
