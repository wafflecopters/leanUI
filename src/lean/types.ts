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

export interface AnalyzeResult {
  success: boolean;
  messages: LeanMessage[];
  goals: LeanGoal[];
  bridgeError?: string;
  durationMs: number;
}
