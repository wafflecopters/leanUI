import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

describe('Record extends with universe levels', () => {
  test('simple record with ULevel param needs explicit result sort', () => {
    // Records with ULevel params need explicit result sort annotation
    // Without it, the result defaults to Type 0 which causes universe violations
    const source = `
record Pair {u : ULevel} (A : Type u) : Type u where
  fst : A
  snd : A
`;
    const result = compileTTFromText(source);
    const allDecls = result.blocks.flatMap(b => (b as any).declarations ?? []);

    const pairDecl = allDecls.find((d: any) => d?.name === 'Pair');
    expect(pairDecl?.checkSuccess).toBe(true);
    // Verify the type is universe polymorphic (Type #0 or Type #1 means it references a level variable)
    expect(pairDecl?.prettyType).toMatch(/Type #\d/);
  });
});
