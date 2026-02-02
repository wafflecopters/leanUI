/**
 * Test runner for .tt files.
 *
 * Discovers all .tt files under src/test-programs/ (excluding preambles/),
 * parses header directives, resolves imports, compiles, and asserts.
 *
 * Header directives (must appear at the top of the file as -- comments):
 *   -- @test success|failure       Required. What to assert.
 *   -- @name "descriptive name"    Required. Test name shown in vitest output.
 *   -- @import preambles/nat.tt    Optional. Prepend contents of another .tt file.
 *   -- @error "substring"          Optional. Assert an error message contains this.
 */

import { describe, test, expect } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { compileSource, TestBlockResult } from '../test-utils';

const TEST_PROGRAMS_DIR = path.resolve(__dirname);

// ---------------------------------------------------------------------------
// Directive parsing
// ---------------------------------------------------------------------------

export interface TTDirectives {
  test: 'success' | 'failure';
  name: string;
  imports: string[];
  errors: string[];
}

export function parseDirectives(source: string): TTDirectives {
  const lines = source.split('\n');
  let testDirective: 'success' | 'failure' | undefined;
  let name: string | undefined;
  const imports: string[] = [];
  const errors: string[] = [];

  for (const line of lines) {
    const trimmed = line.trim();
    // Stop parsing directives when we hit a non-comment, non-directive, non-empty line
    if (trimmed !== '' && !trimmed.startsWith('--') && !trimmed.startsWith('@')) break;

    // Match directives with or without -- prefix: @directive value or -- @directive value
    const directiveMatch = trimmed.match(/^(?:--\s*)?@(\w+)(?:\s+(.*))?/);
    if (!directiveMatch) continue;

    const [, directive, value] = directiveMatch;

    switch (directive) {
      case 'test':
        if (!value) {
          throw new Error(`@test requires a value. Must be "success" or "failure".`);
        }
        if (value === 'success' || value === 'failure') {
          testDirective = value;
        } else {
          throw new Error(`Invalid @test value: "${value}". Must be "success" or "failure".`);
        }
        break;
      case 'name': {
        if (!value) {
          throw new Error(`@name requires a quoted string value.`);
        }
        const nameMatch = value.match(/^"(.+)"$/);
        if (!nameMatch) throw new Error(`@name value must be quoted: ${value}`);
        name = nameMatch[1];
        break;
      }
      case 'import':
        if (!value) {
          throw new Error(`@import requires a file path.`);
        }
        imports.push(value.trim());
        break;
      case 'error': {
        if (!value) {
          throw new Error(`@error requires a quoted string value.`);
        }
        const errorMatch = value.match(/^"(.+)"$/);
        if (!errorMatch) throw new Error(`@error value must be quoted: ${value}`);
        errors.push(errorMatch[1]);
        break;
      }
      default:
        // Ignore unknown directives (they may be compiler directives like @assumeK)
        break;
    }
  }

  if (!testDirective) throw new Error('Missing required @test directive');
  if (!name) throw new Error('Missing required @name directive');

  return { test: testDirective, name, imports, errors };
}

// ---------------------------------------------------------------------------
// Import resolution
// ---------------------------------------------------------------------------

export function resolveImports(imports: string[], basePath: string): string {
  return imports.map(importPath => {
    const fullPath = path.resolve(basePath, importPath);
    if (!fs.existsSync(fullPath)) {
      throw new Error(`Import not found: ${importPath} (resolved to ${fullPath})`);
    }
    return fs.readFileSync(fullPath, 'utf-8');
  }).join('\n');
}

// ---------------------------------------------------------------------------
// Extract body (everything after directives)
// ---------------------------------------------------------------------------

export function extractBody(source: string): string {
  const lines = source.split('\n');
  let bodyStart = 0;

  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].trim();
    // Skip empty lines and test directives (not compiler directives)
    if (trimmed === '' || trimmed.startsWith('--') || trimmed.startsWith('@')) {
      // Keep compiler directives like @assumeK in the source (with or without --)
      if (trimmed.match(/^(?:--\s*)?@assumeK/)) {
        break; // Start body from here
      }
      bodyStart = i + 1;
      continue;
    }
    break;
  }

  return lines.slice(bodyStart).join('\n');
}

// ---------------------------------------------------------------------------
// File discovery
// ---------------------------------------------------------------------------

function discoverTTFiles(dir: string): string[] {
  const files: string[] = [];

  function walk(d: string) {
    for (const entry of fs.readdirSync(d, { withFileTypes: true })) {
      const fullPath = path.join(d, entry.name);
      if (entry.isDirectory()) {
        // Skip preambles directory
        if (entry.name === 'preambles') continue;
        walk(fullPath);
      } else if (entry.name.endsWith('.tt')) {
        files.push(fullPath);
      }
    }
  }

  walk(dir);
  return files.sort();
}

// ---------------------------------------------------------------------------
// Compile and assert
// ---------------------------------------------------------------------------

function compileAndAssert(
  directives: TTDirectives,
  fullSource: string,
  filePath: string
) {
  const results = compileSource(fullSource, { recheckZonkedTerms: true });

  // Filter out comment blocks
  const meaningful = results.filter(r => !r.isComment);

  if (directives.test === 'success') {
    // Every non-comment block should succeed
    for (const block of meaningful) {
      if (!block.checkSuccess) {
        const errors = block.checkErrors.map(e => e.message).join('\n  ');
        throw new Error(
          `Expected success but got errors in block "${block.name}" ` +
          `(${path.relative(TEST_PROGRAMS_DIR, filePath)}):\n  ${errors}`
        );
      }
    }
  } else {
    // At least one block should fail
    const anyFailure = meaningful.some(r => !r.checkSuccess);
    expect(anyFailure).toBe(true);

    // Check error message substrings if specified
    if (directives.errors.length > 0) {
      const allErrors = meaningful.flatMap(r => r.checkErrors.map(e => e.message));
      for (const expectedSubstring of directives.errors) {
        const found = allErrors.some(msg => msg.includes(expectedSubstring));
        if (!found) {
          throw new Error(
            `Expected error containing "${expectedSubstring}" but got:\n  ${allErrors.join('\n  ')}`
          );
        }
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Dynamic test generation
// ---------------------------------------------------------------------------

const ttFiles = discoverTTFiles(TEST_PROGRAMS_DIR);

// Group by subdirectory
const groups = new Map<string, string[]>();
for (const file of ttFiles) {
  const rel = path.relative(TEST_PROGRAMS_DIR, file);
  const dir = path.dirname(rel);
  if (!groups.has(dir)) groups.set(dir, []);
  groups.get(dir)!.push(file);
}

for (const [dir, files] of groups) {
  describe(`tt-programs/${dir}`, () => {
    for (const file of files) {
      const source = fs.readFileSync(file, 'utf-8');
      let directives: TTDirectives;
      try {
        directives = parseDirectives(source);
      } catch (e: any) {
        // Register a failing test if directives are invalid
        test(`INVALID DIRECTIVES: ${path.relative(TEST_PROGRAMS_DIR, file)}`, () => {
          throw e;
        });
        continue;
      }

      test(directives.name, () => {
        const importedSource = resolveImports(directives.imports, TEST_PROGRAMS_DIR);
        const body = extractBody(source);
        const fullSource = importedSource + '\n' + body;
        compileAndAssert(directives, fullSource, file);
      });
    }
  });
}

// ---------------------------------------------------------------------------
// Self-tests for the runner infrastructure
// ---------------------------------------------------------------------------

describe('tt-runner infrastructure', () => {
  test('parseDirectives: parses all directive types', () => {
    const source = `-- @test success
-- @name "my test"
-- @import preambles/nat.tt
-- @import preambles/bool.tt

inductive Foo : Type where`;
    const d = parseDirectives(source);
    expect(d.test).toBe('success');
    expect(d.name).toBe('my test');
    expect(d.imports).toEqual(['preambles/nat.tt', 'preambles/bool.tt']);
    expect(d.errors).toEqual([]);
  });

  test('parseDirectives: failure with error', () => {
    const source = `-- @test failure
-- @name "bad thing"
-- @error "some error"

broken code`;
    const d = parseDirectives(source);
    expect(d.test).toBe('failure');
    expect(d.errors).toEqual(['some error']);
  });

  test('parseDirectives: throws on missing @test', () => {
    expect(() => parseDirectives('-- @name "x"\ncode')).toThrow('Missing required @test');
  });

  test('parseDirectives: throws on missing @name', () => {
    expect(() => parseDirectives('-- @test success\ncode')).toThrow('Missing required @name');
  });

  test('parseDirectives: ignores unknown directives (e.g., compiler directives)', () => {
    // Unknown directives like @bogus or compiler directives like @assumeK are ignored
    const result = parseDirectives('-- @test success\n-- @name "x"\n-- @bogus y\ncode');
    expect(result.test).toBe('success');
    expect(result.name).toBe('x');
  });

  test('extractBody: strips directive lines', () => {
    const source = `-- @test success
-- @name "my test"
-- @import preambles/nat.tt

inductive Foo : Type where
  MkFoo : Foo`;
    const body = extractBody(source);
    expect(body.trim()).toBe('inductive Foo : Type where\n  MkFoo : Foo');
  });

  test('resolveImports: reads and concatenates files', () => {
    const result = resolveImports(['preambles/nat.tt', 'preambles/bool.tt'], TEST_PROGRAMS_DIR);
    expect(result).toContain('Nat');
    expect(result).toContain('Bool');
  });

  test('resolveImports: throws on missing file', () => {
    expect(() => resolveImports(['preambles/nonexistent.tt'], TEST_PROGRAMS_DIR))
      .toThrow('Import not found');
  });

  test('import works: file importing nat.tt can reference Nat', () => {
    const imported = resolveImports(['preambles/nat.tt'], TEST_PROGRAMS_DIR);
    const body = `
id : Nat -> Nat
id x = x
`;
    const results = compileSource(imported + '\n' + body);
    const idResult = results.find(r => r.name === 'id');
    expect(idResult?.checkSuccess).toBe(true);
  });

  test('import works: multiple imports compose correctly', () => {
    const imported = resolveImports(
      ['preambles/nat.tt', 'preambles/bool.tt'],
      TEST_PROGRAMS_DIR
    );
    const body = `
isZero : Nat -> Bool
isZero Zero = True
isZero (Succ _) = False
`;
    const results = compileSource(imported + '\n' + body);
    const result = results.find(r => r.name === 'isZero');
    expect(result?.checkSuccess).toBe(true);
  });
});
