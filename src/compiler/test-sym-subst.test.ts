import { describe, test } from 'vitest';
import { compileTTFromText } from './compile';
import { setPatternLoggingEnabled } from './patterns';

describe('Debug sym substitutions', () => {
  test('sym substitutions', () => {
    setPatternLoggingEnabled(true);

    const source = `
inductive Equal : {A : Type} -> A -> A -> Type where
  refl : {A : Type} -> {a : A} -> Equal a a

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl
`;

    try {
      const result = compileTTFromText(source);
      const symDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'sym');

      console.log('\n=== RESULT ===');
      console.log('checkSuccess:', symDecl?.checkSuccess);
    } finally {
      setPatternLoggingEnabled(false);
    }
  });
});
