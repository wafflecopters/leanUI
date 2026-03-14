/**
 * Fold Tactic: Replace definition bodies in the goal with their constant names
 *
 * The inverse of unfold. Given `fold f`, finds occurrences of f's definition
 * body in the goal type and replaces them with Const("f").
 *
 * When `occurrence` is set, only folds the Nth (1-based) match.
 *
 * Proof term: Meta(newGoalId) where newGoalId has the folded type.
 * This works because the folded type is definitionally equal to the original.
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar, getTermDefinition, createDefinitionsMap, DefinitionsMap } from '../compiler/term';
import { fullNormalize } from '../compiler/whnf';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';

/**
 * Structural equality check for TTK terms.
 * Compares terms by structure (de Bruijn indices, names, tags).
 */
export function ttkTermsEqual(a: TTKTerm, b: TTKTerm): boolean {
  if (a === b) return true;
  if (a.tag !== b.tag) return false;

  switch (a.tag) {
    case 'Var':
      return b.tag === 'Var' && a.index === b.index;
    case 'Const':
      return b.tag === 'Const' && a.name === b.name;
    case 'Sort':
      return b.tag === 'Sort' && ttkTermsEqual(a.level, b.level);
    case 'Hole':
      return b.tag === 'Hole' && a.id === b.id;
    case 'Meta':
      return b.tag === 'Meta' && a.id === b.id;
    case 'ULit':
      return b.tag === 'ULit' && a.n === b.n;
    case 'ULevel':
      return b.tag === 'ULevel';
    case 'UOmega':
      return b.tag === 'UOmega';
    case 'App':
      return b.tag === 'App' && ttkTermsEqual(a.fn, b.fn) && ttkTermsEqual(a.arg, b.arg);
    case 'Binder':
      return b.tag === 'Binder'
        && a.binderKind.tag === b.binderKind.tag
        && ttkTermsEqual(a.domain, b.domain)
        && ttkTermsEqual(a.body, b.body);
    case 'Match':
      if (b.tag !== 'Match') return false;
      if (!ttkTermsEqual(a.scrutinee, b.scrutinee)) return false;
      if (a.clauses.length !== b.clauses.length) return false;
      return a.clauses.every((c, i) => {
        const bc = b.tag === 'Match' ? b.clauses[i] : undefined;
        if (!bc) return false;
        if (c.patterns.length !== bc.patterns.length) return false;
        return ttkTermsEqual(c.rhs, bc.rhs);
      });
    default:
      return false;
  }
}

/**
 * Count the "size" of a term (number of nodes).
 * Used to avoid expensive matching against large definition bodies.
 */
function termSize(term: TTKTerm): number {
  switch (term.tag) {
    case 'Var': case 'Const': case 'Hole': case 'Meta':
    case 'Sort': case 'ULit': case 'ULevel': case 'UOmega':
      return 1;
    case 'App':
      return 1 + termSize(term.fn) + termSize(term.arg);
    case 'Binder':
      return 1 + termSize(term.domain) + termSize(term.body);
    case 'Match':
      return 1 + termSize(term.scrutinee) + term.clauses.reduce((s, c) => s + termSize(c.rhs), 0);
    default:
      return 1;
  }
}

export class FoldTactic implements Tactic {
  name = 'fold';

  constructor(
    public readonly names: string[],
    /** When set, only fold the Nth (1-based) matching occurrence. */
    public readonly occurrence?: number,
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      let currentType = goal.type;
      let changed = false;

      for (const name of this.names) {
        const def = getTermDefinition(engine.definitions, name);
        if (!def || !def.value) {
          return {
            success: false,
            error: `fold: '${name}' has no definition to fold`
          };
        }

        // Normalize the definition body to canonical form (beta/iota only)
        const normalizedBody = fullNormalize(def.value, createDefinitionsMap());
        const replacement: TTKTerm = { tag: 'Const', name };

        if (this.occurrence !== undefined) {
          const result = this.replaceSubtermAtOccurrence(currentType, normalizedBody, replacement, this.occurrence);
          if (result.replaced) {
            changed = true;
            currentType = result.term;
          }
        } else {
          const newType = this.replaceSubterm(currentType, normalizedBody, replacement);
          if (newType !== currentType) {
            changed = true;
            currentType = newType;
          }
        }
      }

      if (!changed) {
        return {
          success: false,
          error: `fold: no occurrences of ${this.names.map(n => `'${n}'`).join(', ')} body found in goal`
        };
      }

      // Create new goal with folded type
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: currentType,
        solution: undefined
      };

      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: { tag: 'Meta', id: newMetaId } });
      newMetaVars.set(newMetaId, newMeta);

      const newGoals = engine.goals.map(g => g === goalId ? newMetaId : g);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error
        ? e.message
        : (e && typeof e === 'object' && 'message' in e)
          ? String((e as any).message)
          : String(e);
      return {
        success: false,
        error: `fold: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Replace all occurrences of `pattern` in `term` with `replacement`.
   * Checks structural equality at each subterm.
   * Returns the same reference if nothing changed.
   */
  private replaceSubterm(term: TTKTerm, pattern: TTKTerm, replacement: TTKTerm): TTKTerm {
    // Check if this entire subterm matches the pattern
    if (ttkTermsEqual(term, pattern)) {
      return replacement;
    }

    switch (term.tag) {
      case 'App': {
        const fn = this.replaceSubterm(term.fn, pattern, replacement);
        const arg = this.replaceSubterm(term.arg, pattern, replacement);
        if (fn === term.fn && arg === term.arg) return term;
        return { tag: 'App', fn, arg };
      }

      case 'Binder': {
        const domain = this.replaceSubterm(term.domain, pattern, replacement);
        const body = this.replaceSubterm(term.body, pattern, replacement);
        if (domain === term.domain && body === term.body) return term;
        return { tag: 'Binder', binderKind: term.binderKind, name: term.name, domain, body };
      }

      case 'Match': {
        const scrutinee = this.replaceSubterm(term.scrutinee, pattern, replacement);
        let clausesChanged = false;
        const clauses = term.clauses.map(c => {
          const rhs = this.replaceSubterm(c.rhs, pattern, replacement);
          if (rhs !== c.rhs) clausesChanged = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        if (scrutinee === term.scrutinee && !clausesChanged) return term;
        return { tag: 'Match', scrutinee, clauses };
      }

      // Leaf nodes
      default:
        return term;
    }
  }

  /**
   * Replace only the Nth occurrence (1-based) of `pattern` in `term`.
   * Uses post-order traversal to match surface annotator's counting.
   */
  private replaceSubtermAtOccurrence(
    term: TTKTerm,
    pattern: TTKTerm,
    replacement: TTKTerm,
    targetOcc: number,
  ): { term: TTKTerm; replaced: boolean } {
    const counter = { count: 0 };
    const result = this.replaceSubtermAtOccurrenceImpl(term, pattern, replacement, targetOcc, counter);
    return { term: result, replaced: result !== term };
  }

  private replaceSubtermAtOccurrenceImpl(
    term: TTKTerm,
    pattern: TTKTerm,
    replacement: TTKTerm,
    targetOcc: number,
    counter: { count: number },
  ): TTKTerm {
    // Post-order: recurse into children first
    let recursed: TTKTerm;

    switch (term.tag) {
      case 'App': {
        const fn = this.replaceSubtermAtOccurrenceImpl(term.fn, pattern, replacement, targetOcc, counter);
        const arg = this.replaceSubtermAtOccurrenceImpl(term.arg, pattern, replacement, targetOcc, counter);
        recursed = (fn === term.fn && arg === term.arg) ? term : { tag: 'App', fn, arg };
        break;
      }

      case 'Binder': {
        const domain = this.replaceSubtermAtOccurrenceImpl(term.domain, pattern, replacement, targetOcc, counter);
        const body = this.replaceSubtermAtOccurrenceImpl(term.body, pattern, replacement, targetOcc, counter);
        recursed = (domain === term.domain && body === term.body) ? term
          : { tag: 'Binder', binderKind: term.binderKind, name: term.name, domain, body };
        break;
      }

      case 'Match': {
        const scrutinee = this.replaceSubtermAtOccurrenceImpl(term.scrutinee, pattern, replacement, targetOcc, counter);
        let clausesChanged = false;
        const clauses = term.clauses.map(c => {
          const rhs = this.replaceSubtermAtOccurrenceImpl(c.rhs, pattern, replacement, targetOcc, counter);
          if (rhs !== c.rhs) clausesChanged = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        recursed = (scrutinee === term.scrutinee && !clausesChanged) ? term
          : { tag: 'Match', scrutinee, clauses };
        break;
      }

      default:
        recursed = term;
        break;
    }

    // Now check if this node (original) matches the pattern
    if (ttkTermsEqual(term, pattern)) {
      counter.count++;
      if (counter.count === targetOcc) {
        return replacement;
      }
    }

    return recursed;
  }
}
