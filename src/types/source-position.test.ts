/**
 * Tests for source position tracking infrastructure
 */

import {
  serializeIndexPath,
  deserializeIndexPath,
  appendPath,
  fieldSeg,
  arraySeg,
  createSourcePos,
  createSourceRange,
  type IndexPath,
  type SourcePos,
  type SourceRange
} from './source-position';

function test(description: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${description}`);
  } catch (error) {
    console.error(`✗ ${description}`);
    throw error;
  }
}

function assertEqual<T>(actual: T, expected: T, message?: string): void {
  const actualStr = JSON.stringify(actual);
  const expectedStr = JSON.stringify(expected);
  if (actualStr !== expectedStr) {
    throw new Error(`${message || 'Assertion failed'}\n  Expected: ${expectedStr}\n  Actual: ${actualStr}`);
  }
}

console.log('\n' + '='.repeat(80));
console.log('SOURCE POSITION TESTS');
console.log('='.repeat(80) + '\n');

// ============================================================================
// Path Serialization Tests
// ============================================================================

test('Serialize empty path', () => {
  const path: IndexPath = [];
  assertEqual(serializeIndexPath(path), "");
});

test('Serialize single field segment', () => {
  const path: IndexPath = [{ kind: 'field', name: 'type' }];
  assertEqual(serializeIndexPath(path), "type");
});

test('Serialize single array segment', () => {
  const path: IndexPath = [{ kind: 'array', index: 0 }];
  assertEqual(serializeIndexPath(path), "[0]");
});

test('Serialize field then field', () => {
  const path: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'body' }
  ];
  assertEqual(serializeIndexPath(path), "value.body");
});

test('Serialize field then array', () => {
  const path: IndexPath = [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 0 }
  ];
  assertEqual(serializeIndexPath(path), "constructors[0]");
});

test('Serialize array then field', () => {
  const path: IndexPath = [
    { kind: 'array', index: 1 },
    { kind: 'field', name: 'type' }
  ];
  assertEqual(serializeIndexPath(path), "[1].type");
});

test('Serialize complex nested path', () => {
  const path: IndexPath = [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 0 },
    { kind: 'field', name: 'type' },
    { kind: 'field', name: 'domain' }
  ];
  assertEqual(serializeIndexPath(path), "constructors[0].type.domain");
});

test('Serialize multiple array indices', () => {
  const path: IndexPath = [
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: 2 },
    { kind: 'field', name: 'patterns' },
    { kind: 'array', index: 1 }
  ];
  assertEqual(serializeIndexPath(path), "clauses[2].patterns[1]");
});

// ============================================================================
// Path Deserialization Tests
// ============================================================================

test('Deserialize empty string', () => {
  const path = deserializeIndexPath("");
  assertEqual(path, []);
});

test('Deserialize single field', () => {
  const path = deserializeIndexPath("type");
  assertEqual(path, [{ kind: 'field', name: 'type' }]);
});

test('Deserialize single array index', () => {
  const path = deserializeIndexPath("[0]");
  assertEqual(path, [{ kind: 'array', index: 0 }]);
});

test('Deserialize field.field', () => {
  const path = deserializeIndexPath("value.body");
  assertEqual(path, [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'body' }
  ]);
});

test('Deserialize field[array]', () => {
  const path = deserializeIndexPath("constructors[0]");
  assertEqual(path, [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 0 }
  ]);
});

test('Deserialize [array].field', () => {
  const path = deserializeIndexPath("[1].type");
  assertEqual(path, [
    { kind: 'array', index: 1 },
    { kind: 'field', name: 'type' }
  ]);
});

test('Deserialize complex nested path', () => {
  const path = deserializeIndexPath("constructors[0].type.domain");
  assertEqual(path, [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 0 },
    { kind: 'field', name: 'type' },
    { kind: 'field', name: 'domain' }
  ]);
});

test('Deserialize path with multiple arrays', () => {
  const path = deserializeIndexPath("clauses[2].patterns[1]");
  assertEqual(path, [
    { kind: 'field', name: 'clauses' },
    { kind: 'array', index: 2 },
    { kind: 'field', name: 'patterns' },
    { kind: 'array', index: 1 }
  ]);
});

// ============================================================================
// Round-Trip Tests
// ============================================================================

test('Round-trip: serialize then deserialize (empty)', () => {
  const original: IndexPath = [];
  const serialized = serializeIndexPath(original);
  const deserialized = deserializeIndexPath(serialized);
  assertEqual(deserialized, original);
});

test('Round-trip: serialize then deserialize (simple)', () => {
  const original: IndexPath = [{ kind: 'field', name: 'type' }];
  const serialized = serializeIndexPath(original);
  const deserialized = deserializeIndexPath(serialized);
  assertEqual(deserialized, original);
});

test('Round-trip: serialize then deserialize (complex)', () => {
  const original: IndexPath = [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 3 },
    { kind: 'field', name: 'type' },
    { kind: 'field', name: 'body' }
  ];
  const serialized = serializeIndexPath(original);
  const deserialized = deserializeIndexPath(serialized);
  assertEqual(deserialized, original);
});

// ============================================================================
// Path Construction Tests
// ============================================================================

test('fieldSeg creates correct segment', () => {
  const seg = fieldSeg('domain');
  assertEqual(seg, { kind: 'field', name: 'domain' });
});

test('arraySeg creates correct segment', () => {
  const seg = arraySeg(5);
  assertEqual(seg, { kind: 'array', index: 5 });
});

test('appendPath with single segment', () => {
  const base: IndexPath = [{ kind: 'field', name: 'value' }];
  const result = appendPath(base, fieldSeg('body'));
  assertEqual(result, [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'body' }
  ]);
});

test('appendPath with multiple segments', () => {
  const base: IndexPath = [{ kind: 'field', name: 'constructors' }];
  const result = appendPath(base, arraySeg(0), fieldSeg('type'));
  assertEqual(result, [
    { kind: 'field', name: 'constructors' },
    { kind: 'array', index: 0 },
    { kind: 'field', name: 'type' }
  ]);
});

test('appendPath to empty path', () => {
  const base: IndexPath = [];
  const result = appendPath(base, fieldSeg('type'));
  assertEqual(result, [{ kind: 'field', name: 'type' }]);
});

test('appendPath does not mutate original', () => {
  const base: IndexPath = [{ kind: 'field', name: 'value' }];
  const result = appendPath(base, fieldSeg('body'));

  assertEqual(base, [{ kind: 'field', name: 'value' }]); // Original unchanged
  assertEqual(result, [
    { kind: 'field', name: 'value' },
    { kind: 'field', name: 'body' }
  ]);
});

// ============================================================================
// Helper Function Tests
// ============================================================================

test('createSourcePos creates correct position', () => {
  const pos = createSourcePos(10, 5, 123);
  assertEqual(pos, { line: 10, col: 5, pos: 123 });
});

test('createSourceRange creates correct range', () => {
  const start: SourcePos = { line: 1, col: 1, pos: 0 };
  const end: SourcePos = { line: 1, col: 10, pos: 9 };
  const range = createSourceRange(start, end);
  assertEqual(range, { start, end });
});

// ============================================================================
// Edge Cases
// ============================================================================

test('Deserialize handles missing dots gracefully', () => {
  // This should work even though serialization would add dots
  const path = deserializeIndexPath("valueBody");
  // Should parse as single field "valueBody" (not ideal but consistent)
  assertEqual(path, [{ kind: 'field', name: 'valueBody' }]);
});

test('Deserialize handles large array indices', () => {
  const path = deserializeIndexPath("items[999]");
  assertEqual(path, [
    { kind: 'field', name: 'items' },
    { kind: 'array', index: 999 }
  ]);
});

test('Serialize handles underscores in field names', () => {
  const path: IndexPath = [{ kind: 'field', name: 'my_field' }];
  assertEqual(serializeIndexPath(path), "my_field");
});

test('Round-trip with underscores and numbers', () => {
  const original: IndexPath = [
    { kind: 'field', name: 'field_1' },
    { kind: 'array', index: 42 },
    { kind: 'field', name: 'sub_field_2' }
  ];
  const serialized = serializeIndexPath(original);
  const deserialized = deserializeIndexPath(serialized);
  assertEqual(deserialized, original);
});

console.log('\n' + '='.repeat(80));
console.log('ALL SOURCE POSITION TESTS PASSED! ✓');
console.log('='.repeat(80) + '\n');
