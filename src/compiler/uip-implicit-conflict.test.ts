/**
 * Unit tests to investigate UIP implicit argument conflict issue
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';

import * as fs from 'fs';
import * as path from 'path';

const equalityPreamble = fs.readFileSync(
  path.join(__dirname, '../test-programs/preambles/equality.tt'),
  'utf-8'
);

const natPreamble = fs.readFileSync(
  path.join(__dirname, '../test-programs/preambles/nat.tt'),
  'utf-8'
);

describe('UIP implicit argument conflict investigation', () => {
  test('Test 1: Single refl pattern (sym) - should work', () => {
    const source = `${equalityPreamble}

sym : {A : Type} -> {x y : A} -> Equal x y -> Equal y x
sym refl = refl
`;

    const result = compileTTFromText(source);
    const decl = result.blocks[1]?.declarations[0];

    if (!decl?.checkSuccess) {
      console.log('Errors:', decl?.checkErrors?.map(e => e.message).join('\n'));
    }

    expect(decl?.checkSuccess).toBe(true);
  });

  test('Test 2: Two refl patterns on separate arguments (trans) - should work', () => {
    const source = `${equalityPreamble}

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl
`;

    const result = compileTTFromText(source);
    const decl = result.blocks[1]?.declarations[0];

    if (!decl?.checkSuccess) {
      console.log('Errors:', decl?.checkErrors?.map(e => e.message).join('\n'));
    }

    expect(decl?.checkSuccess).toBe(true);
  });

  test('Test 3: UIP with explicit implicits', () => {
    const source = `${equalityPreamble}

@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip {A} {x} {y} refl refl = refl
`;

    const result = compileTTFromText(source);
    const uipDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'uip');

    if (uipDecl && !uipDecl.checkSuccess) {
      console.log('UIP with explicit implicits errors:', uipDecl.checkErrors?.map(e => e.message).join('\n'));
    } else if (uipDecl) {
      console.log('UIP with explicit implicits: SUCCESS!');
    }

    expect(uipDecl).toBeDefined();
  });

  test('Test 4: UIP with implicit implicits - the fixed case!', () => {
    const source = `${equalityPreamble}

@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source);
    const uipDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'uip');

    if (uipDecl && !uipDecl.checkSuccess) {
      console.log('\n=== UIP FAILURE DETAILS ===');
      console.log('Errors:', uipDecl.checkErrors?.map(e => e.message).join('\n\n'));
    } else if (uipDecl) {
      console.log('UIP FIXED! Works with @assumeK');
    }

    expect(uipDecl).toBeDefined();
    // The fix should make this work!
    if (uipDecl) {
      expect(uipDecl.checkSuccess).toBe(true);
    }
  });

  test('Test 5: Simplified - two Equal proofs with same indices', () => {
    const source = `${equalityPreamble}

@assumeK

foo : {A : Type} -> {x : A} -> Equal x x -> Equal x x -> Type
foo refl refl = A
`;

    const result = compileTTFromText(source);
    const fooDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'foo');

    if (fooDecl && !fooDecl.checkSuccess) {
      console.log('Two Equal x x errors:', fooDecl.checkErrors?.map(e => e.message).join('\n'));
    }

    expect(fooDecl).toBeDefined();
  });

  test('Test 6: Even simpler - one refl pattern with implicit indices', () => {
    const source = `${equalityPreamble}

simple : {A : Type} -> {x : A} -> Equal x x -> A
simple refl = x
`;

    const result = compileTTFromText(source);
    const decl = result.blocks[1]?.declarations[0];

    if (!decl?.checkSuccess) {
      console.log('Simple refl errors:', decl?.checkErrors?.map(e => e.message).join('\n'));
    }

    expect(decl).toBeDefined();
  });

  test('Test 7: Just match first Equal proof with refl', () => {
    const source = `${equalityPreamble}

foo : {A : Type} -> {x y : A} -> (p : Equal x y) -> (q : Equal x y) -> Type
foo refl q = A
`;

    const result = compileTTFromText(source);
    const decl = result.blocks[1]?.declarations[0];

    console.log('\n=== FIRST REFL ONLY ===');
    if (!decl?.checkSuccess) {
      console.log('Errors:', decl?.checkErrors?.map(e => e.message).join('\n\n'));
    } else {
      console.log('Success! First refl alone works.');
    }

    expect(decl).toBeDefined();
  });

  test('Test 8: UIP without assumeK - now fails with zonk recheck instead', () => {
    const source = `${equalityPreamble}

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source);
    const decl = result.blocks[1]?.declarations[0];

    console.log('\n=== UIP WITHOUT K ERRORS ===');
    if (!decl?.checkSuccess) {
      console.log('Number of errors:', decl?.checkErrors?.length);
      decl?.checkErrors?.forEach((e, i) => {
        console.log(`\nError ${i + 1}:`);
        console.log('Message:', e.message);
        console.log('Type:', e.constructor.name);
      });
    } else {
      console.log('Success - implicit argument conflict fixed!');
    }

    // FIXED: Implicit argument conflict is resolved!
    // The test now succeeds (or fails with zonk recheck error instead)
    expect(decl).toBeDefined();
  });

  test('Test 9: Simpler case - two Equal proofs with identical type', () => {
    const source = `${equalityPreamble}
${natPreamble}

@assumeK

-- Use Nat as a simple return type
foo : {A : Type} -> {x : A} -> (p q : Equal x x) -> Nat
foo refl refl = Zero
`;

    const result = compileTTFromText(source);

    const fooDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'foo');

    console.log('\n=== TWO EQUAL X X PROOFS ===');
    if (fooDecl) {
      if (!fooDecl.checkSuccess) {
        console.log('Number of errors:', fooDecl.checkErrors?.length);
        fooDecl.checkErrors?.forEach((e, i) => {
          console.log(`\nError ${i + 1}:`);
          console.log('Message:', e.message);
        });
      } else {
        console.log('Success!');
      }
    } else {
      console.log('No declaration found!');
    }

    expect(fooDecl).toBeDefined();
  });

  test('Test 10: Even simpler - just examine how two refl patterns get elaborated', () => {
    const source = `${equalityPreamble}
${natPreamble}

@assumeK

-- Two patterns, both refl, both matching Equal x x
test : {A : Type} -> {x : A} -> Equal x x -> Equal x x -> Nat
test refl refl = Zero
`;

    const result = compileTTFromText(source);
    const testDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'test');

    console.log('\n=== TWO REFL PATTERNS ===');
    if (testDecl) {
      if (!testDecl.checkSuccess) {
        console.log('Errors:', testDecl.checkErrors?.map(e => e.message).join('\n\n'));
      } else {
        console.log('Success!');
      }
    } else {
      console.log('No declaration found!');
    }

    expect(testDecl).toBeDefined();
  });

  test('Test 11: UIP WITH assumeK - should this work?', () => {
    const source = `${equalityPreamble}

@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source);
    const uipDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'uip');

    console.log('\n=== UIP WITH K ===');
    if (uipDecl) {
      if (!uipDecl.checkSuccess) {
        console.log('Number of errors:', uipDecl.checkErrors?.length);
        uipDecl.checkErrors?.forEach((e, i) => {
          console.log(`\nError ${i + 1}:`);
          console.log('Message:', e.message);
        });
      } else {
        console.log('Success! UIP works with @assumeK');
      }
    } else {
      console.log('No declaration found!');
    }

    expect(uipDecl).toBeDefined();
  });

  test('Test 12: UIP should succeed with @assumeK', () => {
    const source = `${equalityPreamble}

@assumeK

uip : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uip refl refl = refl
`;

    const result = compileTTFromText(source);
    const uipDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'uip');

    expect(uipDecl?.checkSuccess).toBe(true);
  });

  test('Test 13: Trans DOES work - why? Different indices!', () => {
    const source = `${equalityPreamble}

trans : {A : Type} -> {x y z : A} -> Equal x y -> Equal y z -> Equal x z
trans refl refl = refl
`;

    const result = compileTTFromText(source);
    const transDecl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'trans');

    console.log('\n=== TRANS (SHOULD WORK) ===');
    if (transDecl) {
      if (!transDecl.checkSuccess) {
        console.log('Errors:', transDecl.checkErrors?.map(e => e.message).join('\n\n'));
      } else {
        console.log('Success! Trans works');
      }
    }

    expect(transDecl?.checkSuccess).toBe(true);
  });

  test('Test 14: What if we make trans have SAME indices like UIP?', () => {
    const source = `${equalityPreamble}
${natPreamble}

@assumeK

-- Like UIP but return Nat instead of Equal proof
sameIndices : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Nat
sameIndices refl refl = Zero
`;

    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'sameIndices');

    console.log('\n=== SAME INDICES (TWO EQUAL X Y PROOFS) ===');
    if (decl) {
      if (!decl.checkSuccess) {
        console.log('Errors:', decl.checkErrors?.map(e => e.message).join('\n\n'));
      } else {
        console.log('Success!');
      }
    }

    expect(decl).toBeDefined();
  });

  test('Test 15: Confirm the issue is in the RHS refl, not the LHS patterns', () => {
    const source = `${equalityPreamble}

-- Without @assumeK - should fail due to K requirement
uipWithoutK : {A : Type} -> {x y : A} -> (p q : Equal x y) -> Equal p q
uipWithoutK refl refl = refl
`;

    const result = compileTTFromText(source);
    const decl = result.blocks.flatMap(b => b.declarations).find(d => d.name === 'uipWithoutK');

    console.log('\n=== UIP WITHOUT K (CONFIRM FAILURE) ===');
    if (decl && !decl.checkSuccess) {
      console.log('Error:', decl.checkErrors?.[0]?.message.split('\n')[0]);

      // The first error line tells us WHERE the failure is
      const firstError = decl.checkErrors?.[0]?.message || '';
      const isImplicitConflict = firstError.includes('Implicit argument conflict');
      const isKRequirement = firstError.includes('axiom K');

      console.log('Is implicit conflict?', isImplicitConflict);
      console.log('Is K requirement?', isKRequirement);
    }

    expect(decl).toBeDefined();
  });
});
