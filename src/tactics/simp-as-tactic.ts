/**
 * SimpTactic: source/shared tactic wrapper around runSimp.
 *
 * This lets text-source tactic blocks use the same simplification engine that
 * the structured proof tree already uses, instead of keeping simp as a
 * structured-editor-only action.
 */

import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';
import { runSimp } from './simp-tactic';

export class SimpTactic implements Tactic {
  name = 'simp';

  constructor(
    public readonly lemmaNames: readonly string[],
  ) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    try {
      const lemmas = this.lemmaNames.length > 0
        ? [...this.lemmaNames]
        : [...(engine.definitions.simpLemmas ?? [])];
      const result = runSimp(engine, lemmas);
      if (!result.success) {
        return {
          success: false,
          error: result.error ?? 'simp: failed',
        };
      }
      return {
        success: true,
        newEngine: result.engine,
      };
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);
      return {
        success: false,
        error: `simp: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined,
      };
    }
  }
}
