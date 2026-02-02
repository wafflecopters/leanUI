import { describe, test } from 'vitest';
import { compileTTFromText } from './compile';

describe('replace0 universe level checking', () => {
  test('replace0 with explicit Type argument', () => {
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

-- Version 1: Explicit {A := Type}
replace0explicit : {x y : Type} -> {f : Type -> Type} -> Equal0 {A := Type} x y -> f x -> f y
replace0explicit refl0 fx = fx
`;

    const result = compileTTFromText(source);
    
    console.log('\n=== EXPLICIT TYPE ARG ===');
    
    const decl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'replace0explicit');
    console.log('checkSuccess:', decl?.checkSuccess);
    if (decl?.checkErrors && decl.checkErrors.length > 0) {
      console.log('Errors:', decl.checkErrors.map((e: any) => e.message));
    }
  });
  
  test('replace0 WITHOUT explicit arg (original)', () => {
    const source = `
inductive Equal0 : {A : Type} -> A -> A -> Type where
  refl0 : {A : Type} -> {x : A} -> Equal0 x x

-- Version 2: Let inference figure it out
replace0 : {x y : Type} -> {f : Type -> Type} -> Equal0 x y -> f x -> f y
replace0 refl0 fx = fx
`;

    const result = compileTTFromText(source);
    
    console.log('\n=== IMPLICIT TYPE ARG ===');
    
    const decl = result.blocks.flatMap(b => (b as any).declarations || []).find((d: any) => d?.name === 'replace0');
    console.log('checkSuccess:', decl?.checkSuccess);
    if (decl?.checkErrors && decl.checkErrors.length > 0) {
      console.log('Errors:', decl.checkErrors.map((e: any) => e.message));
    }
  });
});
