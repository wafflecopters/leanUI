/**
 * Tests for source position tracking infrastructure
 */

import { describe, test, expect } from 'vitest';
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
} from './source-position';

describe('Source Position', () => {
  describe('Path Serialization', () => {
    test('serialize empty path', () => {
      const path: IndexPath = [];
      expect(serializeIndexPath(path)).toBe("");
    });

    test('serialize single field segment', () => {
      const path: IndexPath = [{ kind: 'field', name: 'type' }];
      expect(serializeIndexPath(path)).toBe("type");
    });

    test('serialize single array segment', () => {
      const path: IndexPath = [{ kind: 'array', index: 0 }];
      expect(serializeIndexPath(path)).toBe("[0]");
    });

    test('serialize field then field', () => {
      const path: IndexPath = [
        { kind: 'field', name: 'value' },
        { kind: 'field', name: 'body' }
      ];
      expect(serializeIndexPath(path)).toBe("value.body");
    });

    test('serialize field then array', () => {
      const path: IndexPath = [
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 0 }
      ];
      expect(serializeIndexPath(path)).toBe("constructors[0]");
    });

    test('serialize array then field', () => {
      const path: IndexPath = [
        { kind: 'array', index: 1 },
        { kind: 'field', name: 'type' }
      ];
      expect(serializeIndexPath(path)).toBe("[1].type");
    });

    test('serialize complex nested path', () => {
      const path: IndexPath = [
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 0 },
        { kind: 'field', name: 'type' },
        { kind: 'field', name: 'domain' }
      ];
      expect(serializeIndexPath(path)).toBe("constructors[0].type.domain");
    });

    test('serialize multiple array indices', () => {
      const path: IndexPath = [
        { kind: 'field', name: 'clauses' },
        { kind: 'array', index: 2 },
        { kind: 'field', name: 'patterns' },
        { kind: 'array', index: 1 }
      ];
      expect(serializeIndexPath(path)).toBe("clauses[2].patterns[1]");
    });
  });

  describe('Path Deserialization', () => {
    test('deserialize empty string', () => {
      const path = deserializeIndexPath("");
      expect(path).toEqual([]);
    });

    test('deserialize single field', () => {
      const path = deserializeIndexPath("type");
      expect(path).toEqual([{ kind: 'field', name: 'type' }]);
    });

    test('deserialize single array index', () => {
      const path = deserializeIndexPath("[0]");
      expect(path).toEqual([{ kind: 'array', index: 0 }]);
    });

    test('deserialize field.field', () => {
      const path = deserializeIndexPath("value.body");
      expect(path).toEqual([
        { kind: 'field', name: 'value' },
        { kind: 'field', name: 'body' }
      ]);
    });

    test('deserialize field[array]', () => {
      const path = deserializeIndexPath("constructors[0]");
      expect(path).toEqual([
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 0 }
      ]);
    });

    test('deserialize [array].field', () => {
      const path = deserializeIndexPath("[1].type");
      expect(path).toEqual([
        { kind: 'array', index: 1 },
        { kind: 'field', name: 'type' }
      ]);
    });

    test('deserialize complex nested path', () => {
      const path = deserializeIndexPath("constructors[0].type.domain");
      expect(path).toEqual([
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 0 },
        { kind: 'field', name: 'type' },
        { kind: 'field', name: 'domain' }
      ]);
    });

    test('deserialize path with multiple arrays', () => {
      const path = deserializeIndexPath("clauses[2].patterns[1]");
      expect(path).toEqual([
        { kind: 'field', name: 'clauses' },
        { kind: 'array', index: 2 },
        { kind: 'field', name: 'patterns' },
        { kind: 'array', index: 1 }
      ]);
    });
  });

  describe('Round-Trip Tests', () => {
    test('round-trip empty', () => {
      const original: IndexPath = [];
      const serialized = serializeIndexPath(original);
      const deserialized = deserializeIndexPath(serialized);
      expect(deserialized).toEqual(original);
    });

    test('round-trip simple', () => {
      const original: IndexPath = [{ kind: 'field', name: 'type' }];
      const serialized = serializeIndexPath(original);
      const deserialized = deserializeIndexPath(serialized);
      expect(deserialized).toEqual(original);
    });

    test('round-trip complex', () => {
      const original: IndexPath = [
        { kind: 'field', name: 'value' },
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 3 },
        { kind: 'field', name: 'type' },
        { kind: 'field', name: 'body' }
      ];
      const serialized = serializeIndexPath(original);
      const deserialized = deserializeIndexPath(serialized);
      expect(deserialized).toEqual(original);
    });
  });

  describe('Path Construction', () => {
    test('fieldSeg creates correct segment', () => {
      const seg = fieldSeg('domain');
      expect(seg).toEqual({ kind: 'field', name: 'domain' });
    });

    test('arraySeg creates correct segment', () => {
      const seg = arraySeg(5);
      expect(seg).toEqual({ kind: 'array', index: 5 });
    });

    test('appendPath with single segment', () => {
      const base: IndexPath = [{ kind: 'field', name: 'value' }];
      const result = appendPath(base, fieldSeg('body'));
      expect(result).toEqual([
        { kind: 'field', name: 'value' },
        { kind: 'field', name: 'body' }
      ]);
    });

    test('appendPath with multiple segments', () => {
      const base: IndexPath = [{ kind: 'field', name: 'constructors' }];
      const result = appendPath(base, arraySeg(0), fieldSeg('type'));
      expect(result).toEqual([
        { kind: 'field', name: 'constructors' },
        { kind: 'array', index: 0 },
        { kind: 'field', name: 'type' }
      ]);
    });

    test('appendPath to empty path', () => {
      const base: IndexPath = [];
      const result = appendPath(base, fieldSeg('type'));
      expect(result).toEqual([{ kind: 'field', name: 'type' }]);
    });

    test('appendPath does not mutate original', () => {
      const base: IndexPath = [{ kind: 'field', name: 'value' }];
      const result = appendPath(base, fieldSeg('body'));

      expect(base).toEqual([{ kind: 'field', name: 'value' }]); // Original unchanged
      expect(result).toEqual([
        { kind: 'field', name: 'value' },
        { kind: 'field', name: 'body' }
      ]);
    });
  });

  describe('Helper Functions', () => {
    test('createSourcePos creates correct position', () => {
      const pos = createSourcePos(10, 5, 123);
      expect(pos).toEqual({ line: 10, col: 5, pos: 123 });
    });

    test('createSourceRange creates correct range', () => {
      const start: SourcePos = { line: 1, col: 1, pos: 0 };
      const end: SourcePos = { line: 1, col: 10, pos: 9 };
      const range = createSourceRange(start, end);
      expect(range).toEqual({ start, end });
    });
  });

  describe('Edge Cases', () => {
    test('deserialize handles missing dots gracefully', () => {
      // This should work even though serialization would add dots
      const path = deserializeIndexPath("valueBody");
      // Should parse as single field "valueBody" (not ideal but consistent)
      expect(path).toEqual([{ kind: 'field', name: 'valueBody' }]);
    });

    test('deserialize handles large array indices', () => {
      const path = deserializeIndexPath("items[999]");
      expect(path).toEqual([
        { kind: 'field', name: 'items' },
        { kind: 'array', index: 999 }
      ]);
    });

    test('serialize handles underscores in field names', () => {
      const path: IndexPath = [{ kind: 'field', name: 'my_field' }];
      expect(serializeIndexPath(path)).toBe("my_field");
    });

    test('round-trip with underscores and numbers', () => {
      const original: IndexPath = [
        { kind: 'field', name: 'field_1' },
        { kind: 'array', index: 42 },
        { kind: 'field', name: 'sub_field_2' }
      ];
      const serialized = serializeIndexPath(original);
      const deserialized = deserializeIndexPath(serialized);
      expect(deserialized).toEqual(original);
    });
  });
});
