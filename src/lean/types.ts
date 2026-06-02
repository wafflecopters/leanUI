/** Shared types for the Lean backend client (mirrors server/lean-bridge.ts). */

export type LeanSeverity = 'error' | 'warning' | 'information' | 'hint';

export interface LeanMessage {
  severity: LeanSeverity;
  /** 1-based line. */
  startLine: number;
  /** 0-based column. */
  startCol: number;
  endLine: number;
  endCol: number;
  text: string;
}

export interface LeanGoal {
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  /** One pretty-printed goal state per open goal. */
  goals: string[];
}

/**
 * Tagged pretty-printed Lean expression (`CodeWithInfos`). Mirrors the bridge's
 * `TaggedText` and the converter's `TaggedJson`. See `codeWithInfos.ts`.
 */
export type TaggedText =
  | { t: 'text'; s: string }
  | { t: 'append'; kids: TaggedText[] }
  | { t: 'tag'; pos: string; child: TaggedText };

/** A top-level declaration the user wrote. */
export interface LeanDeclaration {
  name: string;
  kind: 'def' | 'theorem' | 'inductive' | 'axiom' | 'opaque';
  prettyType: string;
  /** Tagged pretty-print of the type, for the WYSIWYG math editor. */
  typeTagged?: TaggedText;
  /** Present for plain `def`s only. */
  prettyValue?: string;
  /** Tagged pretty-print of the value (defs only). */
  valueTagged?: TaggedText;
  /** 1-based line, 0-based column of the declaration's start. */
  line: number;
  col: number;
}

export interface AnalyzeResult {
  success: boolean;
  messages: LeanMessage[];
  goals: LeanGoal[];
  declarations: LeanDeclaration[];
  bridgeError?: string;
  durationMs: number;
}
