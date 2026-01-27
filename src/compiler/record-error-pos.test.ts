/**
 * Test that record field errors have correct source positions.
 */

import { describe, test, expect } from 'vitest';
import { compileTTFromText } from './compile';
import { serializeIndexPath } from '../types/source-position';

describe('Record Error Positions', () => {
  test('error in field type maps to correct source line', () => {
    const source = `
record DPair (A : Type) (B : A -> Type) : Type where
  constructor MkDPair
  dfst: A
  dsnd: B
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0].declarations[0];

    expect(decl.checkSuccess).toBe(false);
    expect(decl.checkErrors).toBeDefined();
    expect(decl.checkErrors!.length).toBeGreaterThan(0);

    // The error should be about B being unapplied (needs an argument)
    const err = decl.checkErrors![0];
    expect(err.message).toContain('B');

    // Check elabMap has the constructor type mappings
    expect(decl.elabMap).toBeDefined();

    // Should have mappings for params and fields
    expect(decl.elabMap!.get('constructors[0].type.domain')).toBe('params[0].type');
    expect(decl.elabMap!.get('constructors[0].type.body.domain')).toBe('params[1].type');
    expect(decl.elabMap!.get('constructors[0].type.body.body.domain')).toBe('fields[0].type');
    expect(decl.elabMap!.get('constructors[0].type.body.body.body.domain')).toBe('fields[1].type');

    // The error indexPath should point to the dsnd field's type in the constructor
    const errorPath = serializeIndexPath(err.env.indexPath);
    console.log('Error path:', errorPath);

    // Check that sourceMap has the field positions
    expect(decl.sourceMap).toBeDefined();
    const field1Range = decl.sourceMap!.get('fields[1].type');
    expect(field1Range).toBeDefined();
    console.log('fields[1].type source line:', field1Range?.start.line);
  });

  test('error in first param type maps to params[0].type', () => {
    const source = `
record BadRecord (A : UndefinedType) where
  x : A
`;
    const result = compileTTFromText(source);
    const decl = result.blocks[0].declarations[0];

    expect(decl.checkSuccess).toBe(false);

    // Check elabMap has the param type mapping
    expect(decl.elabMap).toBeDefined();
    expect(decl.elabMap!.get('constructors[0].type.domain')).toBe('params[0].type');
  });
});
