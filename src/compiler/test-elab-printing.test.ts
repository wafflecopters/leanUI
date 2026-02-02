import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { prettyPrint, prettyPrintFormatted } from './kernel';

describe('Elaboration printing', () => {
  test('Universe level variables should be printed correctly', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;

    const result = compileTTFromText(source);
    const equalDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'Equal');

    expect(equalDecl?.checkSuccess).toBe(true);

    // Get the elaborated kernel terms (not strings!)
    const kernelType = equalDecl?.kernelType;
    const reflCtor = equalDecl?.kernelConstructors?.find((c: any) => c.name === 'refl');
    const reflKernelType = reflCtor?.type;

    console.log('\n=== ELABORATION PRINTING TEST ===');
    console.log('kernelType:', JSON.stringify(kernelType, null, 2).slice(0, 500));
    console.log('reflKernelType:', JSON.stringify(reflKernelType, null, 2).slice(0, 500));

    // Now get the pretty-printed strings using prettyPrintFormatted (what the UI uses)
    const elabTypeStr = kernelType ? prettyPrintFormatted(kernelType, []) : '';
    const reflTypeStr = reflKernelType ? prettyPrintFormatted(reflKernelType, []) : '';

    console.log('Type:', elabTypeStr);
    console.log('refl:', reflTypeStr);

    // The type should contain "Type u", not "Type #0"
    expect(elabTypeStr).toContain('Type u');
    expect(elabTypeStr).not.toContain('Type #0');

    // The constructor type should also contain "Type u", not "Type #0"
    expect(reflTypeStr).toContain('Type u');
    expect(reflTypeStr).not.toContain('Type #0');
  });

  test('prettyPrintFormatted should print universe level variables by name', () => {
    const source = `
inductive Equal : {u : ULevel} -> {A : Type u} -> A -> A -> Type where
  refl : {u : ULevel} -> {A : Type u} -> {a : A} -> Equal a a
`;

    const result = compileTTFromText(source);
    const equalDecl = result.blocks.flatMap(b => (b as any).declarations).find((d: any) => d?.name === 'Equal');
    const reflCtor = equalDecl?.kernelConstructors?.find((c: any) => c.name === 'refl');

    // Get the kernel terms
    const kernelType = equalDecl?.kernelType;
    const reflKernelType = reflCtor?.type;

    // Pretty-print using prettyPrintFormatted (what the UI uses)
    const elabTypeStr = kernelType ? prettyPrintFormatted(kernelType, []) : '';
    const reflTypeStr = reflKernelType ? prettyPrintFormatted(reflKernelType, []) : '';

    console.log('\n=== FORMATTED PRINTING TEST ===');
    console.log('Type:', elabTypeStr);
    console.log('refl:', reflTypeStr);

    // Should contain "Type u", not "Type #0" (THIS IS THE BUG)
    expect(elabTypeStr).toContain('Type u');
    expect(elabTypeStr).not.toContain('Type #0');

    expect(reflTypeStr).toContain('Type u');
    expect(reflTypeStr).not.toContain('Type #0');
  });
});
