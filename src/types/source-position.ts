/**
 * Source Position Tracking Infrastructure
 *
 * This module provides types and utilities for tracking source code positions
 * throughout the parsing, elaboration, and type checking pipeline.
 *
 * Key Design:
 * - ASTs remain pure (no embedded source positions)
 * - Separate maps track positions: Parser → SourceMap, Elaborator → ElabMap
 * - Index paths use hybrid semantic+positional segments for robustness
 */

// ============================================================================
// Position Types
// ============================================================================

/**
 * A position in source code (line, column, character offset).
 */
export interface SourcePos {
  line: number;   // 1-based line number
  col: number;    // 1-based column number
  pos: number;    // 0-based character offset from start of file
}

/**
 * A range in source code from start to end position.
 */
export interface SourceRange {
  start: SourcePos;  // Inclusive start position
  end: SourcePos;    // Exclusive end position
}

// ============================================================================
// Index Path Types
// ============================================================================

/**
 * A segment in an index path through a tree structure.
 *
 * - 'field' segments identify named children (e.g., 'type', 'domain', 'body')
 * - 'array' segments identify indexed children (e.g., constructors[0], clauses[1])
 */
export type IndexPathSegment =
  | { kind: 'field'; name: string }      // Named field accessor
  | { kind: 'array'; index: number };    // Array index accessor

/**
 * A path through a tree structure, identifying a specific node.
 *
 * Examples:
 *   []                                          → root
 *   [{ kind: 'field', name: 'type' }]          → the 'type' field
 *   [{ kind: 'field', name: 'constructors' },
 *    { kind: 'array', index: 0 },
 *    { kind: 'field', name: 'type' }]          → type of first constructor
 */
export type IndexPath = IndexPathSegment[];

// ============================================================================
// Map Types
// ============================================================================

/**
 * Maps serialized index paths to source ranges.
 *
 * Built by the parser to track where each AST node came from in the source text.
 *
 * Key format examples:
 *   ""                      → root declaration
 *   "type"                  → type field
 *   "constructors[0].type"  → type of first constructor
 *   "value.body"            → body of lambda in value
 */
export type SourceMap = Map<string, SourceRange>;

/**
 * Maps elaborated (kernel) paths to unelaborated (surface) paths.
 *
 * Built by the elaborator to track correspondence between kernel and surface ASTs.
 *
 * This enables mapping type errors (which occur on kernel terms) back to
 * source positions via: kernel path → surface path → source range.
 */
export type ElabMap = Map<string, string>;

// ============================================================================
// Path Serialization
// ============================================================================

/**
 * Serialize an IndexPath to a string key for use in maps.
 *
 * Format:
 *   - Empty path: ""
 *   - Field segments: "name" or ".name" (dot prefix for non-first)
 *   - Array segments: "[index]"
 *
 * Examples:
 *   [] → ""
 *   [{kind: 'field', name: 'type'}] → "type"
 *   [{kind: 'field', name: 'constructors'}, {kind: 'array', index: 0}]
 *     → "constructors[0]"
 *   [{kind: 'field', name: 'value'}, {kind: 'field', name: 'body'}]
 *     → "value.body"
 */
export function serializeIndexPath(path: IndexPath): string {
  if (path.length === 0) return "";

  return path.map((seg, i) => {
    if (seg.kind === 'field') {
      // First segment: no dot prefix. Subsequent segments: dot prefix.
      return i === 0 ? seg.name : `.${seg.name}`;
    } else {
      // Array segment: always [index] format
      return `[${seg.index}]`;
    }
  }).join('');
}

/**
 * Deserialize a string key back to an IndexPath.
 *
 * Inverse of serializeIndexPath.
 */
export function deserializeIndexPath(key: string): IndexPath {
  if (key === "") return [];

  const path: IndexPath = [];

  // Regex matches:
  // - (\w+): field name (word characters)
  // - \[(\d+)\]: array index in brackets
  const regex = /(\w+)|\[(\d+)\]/g;
  let match: RegExpExecArray | null;

  while ((match = regex.exec(key)) !== null) {
    if (match[1]) {
      // Field segment
      path.push({ kind: 'field', name: match[1] });
    } else if (match[2]) {
      // Array segment
      path.push({ kind: 'array', index: parseInt(match[2], 10) });
    }
  }

  return path;
}

// ============================================================================
// Path Construction Utilities
// ============================================================================

/**
 * Append segments to a path, creating a new path.
 *
 * Example:
 *   appendPath([{ kind: 'field', name: 'value' }],
 *              { kind: 'field', name: 'body' })
 *   → [{ kind: 'field', name: 'value' }, { kind: 'field', name: 'body' }]
 */
export function appendPath(path: IndexPath, ...segments: IndexPathSegment[]): IndexPath {
  return [...path, ...segments];
}

/**
 * Create a field segment.
 *
 * Example: fieldSeg('type') → { kind: 'field', name: 'type' }
 */
export function fieldSeg(name: string): IndexPathSegment {
  return { kind: 'field', name };
}

/**
 * Create an array segment.
 *
 * Example: arraySeg(0) → { kind: 'array', index: 0 }
 */
export function arraySeg(index: number): IndexPathSegment {
  return { kind: 'array', index };
}

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Create a SourcePos from Token-like object.
 */
export function createSourcePos(line: number, col: number, pos: number): SourcePos {
  return { line, col, pos };
}

/**
 * Create a SourceRange from two positions.
 */
export function createSourceRange(start: SourcePos, end: SourcePos): SourceRange {
  return { start, end };
}
