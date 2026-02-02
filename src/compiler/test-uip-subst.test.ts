import { describe, test } from 'vitest';
import { compileTTFromText } from './compile';
import { setPatternLoggingEnabled } from './patterns';

describe('Debug UIP substitutions', () => {
  test('UIP without K - should fail', () => {
    setPatternLoggingEnabled(true);

    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    try {
      const result = compileTTFromText(source);
      const uipDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'uip');

      console.log('\n=== UIP WITHOUT K ===');
      console.log('checkSuccess:', uipDecl?.checkSuccess);
      console.log('EXPECTED: false (should fail without K)');
      if (uipDecl?.checkSuccess) {
        console.log('❌ BUG: UIP succeeded without K!');
      }
    } finally {
      setPatternLoggingEnabled(false);
    }
  });
});
