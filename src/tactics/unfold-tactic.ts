/**
 * Unfold Tactic: Expand named definitions in the goal type
 *
 * Given `unfold f`, replaces occurrences of Const("f") in the goal type
 * with f's definition body. Multiple names: `unfold f, g` unfolds both.
 *
 * When `occurrence` is set, only unfolds the Nth (0-based) application of f.
 *
 * Proof term: Meta(newGoalId) where newGoalId has the unfolded type.
 * This works because the unfolded type is definitionally equal to the original,
 * so the type checker accepts Meta(newGoalId) : originalGoalType.
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar, getTermDefinition, createDefinitionsMap, DefinitionsMap } from '../compiler/term';
import { fullNormalize } from '../compiler/whnf';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult, freshMetaName } from './tactic';

export class UnfoldTactic implements Tactic {
  name = 'unfold';

  constructor(
    public readonly names: string[],
    /** When set, only unfold the Nth (1-based) application of the head constant. */
    public readonly occurrence?: number,
  ) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      let currentType = goal.type;
      let changed = false;

      for (const name of this.names) {
        // Look up definition
        const def = getTermDefinition(engine.definitions, name);
        if (!def || !def.value) {
          return {
            success: false,
            error: `unfold: '${name}' has no definition to unfold`
          };
        }

        if (this.occurrence !== undefined) {
          // Targeted: only replace the Nth occurrence of Const(name) as App head.
          // Pass definitions so occurrence counting skips implicit arg subtrees,
          // matching the surface annotator's counting (which strips implicit args).
          const result = this.replaceConstAtOccurrence(currentType, name, def.value, this.occurrence, engine.definitions);
          if (result.replaced) {
            changed = true;
            currentType = result.term;
          }
        } else {
          // Untargeted: replace all occurrences
          const newType = this.replaceConst(currentType, name, def.value);
          if (newType !== currentType) {
            changed = true;
            currentType = newType;
          }
        }
      }

      if (!changed) {
        return {
          success: false,
          error: `unfold: no occurrences of ${this.names.map(n => `'${n}'`).join(', ')} found in goal`
        };
      }

      // Deep beta/iota-normalize the unfolded type to reduce redexes
      // (e.g., (\x => body)(arg) from definition substitution, Match on known args).
      // Uses empty definitions so we only do beta/iota, not delta-reduction.
      currentType = fullNormalize(currentType, createDefinitionsMap());

      // Create new goal with unfolded type
      const newMetaId = freshMetaName();
      const newMeta: MetaVar = {
        ctx: goal.ctx,
        type: currentType,
        solution: undefined
      };

      // Proof term: just Meta(newMetaId)
      // Since unfolded type is definitionally equal to original,
      // the type checker accepts this.
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
        error: `unfold: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Replace all occurrences of Const(name) with replacement in term.
   * Returns the same reference if nothing changed (for fast equality check).
   * The App spine naturally handles argument application after replacement.
   */
  private replaceConst(term: TTKTerm, name: string, replacement: TTKTerm): TTKTerm {
    switch (term.tag) {
      case 'Const':
        return term.name === name ? replacement : term;

      case 'App': {
        const fn = this.replaceConst(term.fn, name, replacement);
        const arg = this.replaceConst(term.arg, name, replacement);
        if (fn === term.fn && arg === term.arg) return term;
        return { tag: 'App', fn, arg };
      }

      case 'Binder': {
        const domain = this.replaceConst(term.domain, name, replacement);
        const body = this.replaceConst(term.body, name, replacement);
        if (domain === term.domain && body === term.body) return term;
        return {
          tag: 'Binder',
          binderKind: term.binderKind,
          name: term.name,
          domain,
          body
        };
      }

      case 'Match': {
        const scrutinee = this.replaceConst(term.scrutinee, name, replacement);
        let clausesChanged = false;
        const clauses = term.clauses.map(c => {
          const rhs = this.replaceConst(c.rhs, name, replacement);
          if (rhs !== c.rhs) clausesChanged = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        if (scrutinee === term.scrutinee && !clausesChanged) return term;
        return { tag: 'Match', scrutinee, clauses };
      }

      // Leaf nodes — no Const inside
      case 'Var':
      case 'Hole':
      case 'Meta':
      case 'Sort':
      case 'ULevel':
      case 'ULit':
      case 'UOmega':
        return term;

      default:
        return term;
    }
  }

  /**
   * Get the head constant name of an App chain.
   */
  private getAppHead(term: TTKTerm): string | null {
    let current = term;
    while (current.tag === 'App') current = current.fn;
    return current.tag === 'Const' ? current.name : null;
  }

  /** Collect an App chain into head + args array. */
  private collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
    const args: TTKTerm[] = [];
    let head = term;
    while (head.tag === 'App') {
      args.unshift(head.arg);
      head = head.fn;
    }
    return { head, args };
  }

  /** Look up implicit arg positions for a constant (from namedArgMap). */
  private getImplicitPositions(headName: string, definitions?: DefinitionsMap): Set<number> | null {
    if (!definitions) return null;
    const termDef = definitions.terms.get(headName);
    if (termDef?.namedArgMap && termDef.namedArgMap.size > 0) {
      return new Set(termDef.namedArgMap.values());
    }
    const indDef = definitions.inductiveTypes.get(headName);
    if (indDef?.namedArgMap && indDef.namedArgMap.size > 0) {
      return new Set(indDef.namedArgMap.values());
    }
    const indName = definitions.inductiveNameOfConstructor.get(headName);
    if (indName) {
      const parentInd = definitions.inductiveTypes.get(indName);
      if (parentInd) {
        const ctor = parentInd.constructors.find(c => c.name === headName);
        if (ctor?.namedArgMap && ctor.namedArgMap.size > 0) {
          return new Set(ctor.namedArgMap.values());
        }
      }
    }
    return null;
  }

  /**
   * Replace only the Nth occurrence (1-based) of Const(name) as App head.
   * When definitions are provided, skips implicit arg subtrees so that
   * occurrence counting matches the surface view (which strips implicit args).
   */
  private replaceConstAtOccurrence(
    term: TTKTerm,
    name: string,
    replacement: TTKTerm,
    targetOcc: number,
    definitions?: DefinitionsMap,
  ): { term: TTKTerm; replaced: boolean } {
    const counter = { count: 0 };
    const result = this.replaceConstAtOccurrenceImpl(term, name, replacement, targetOcc, counter, definitions);
    return { term: result, replaced: result !== term };
  }

  private replaceConstAtOccurrenceImpl(
    term: TTKTerm,
    name: string,
    replacement: TTKTerm,
    targetOcc: number,
    counter: { count: number },
    definitions?: DefinitionsMap,
  ): TTKTerm {
    // Check if this is an App chain headed by Const(name)
    //
    // IMPORTANT: Uses POST-ORDER counting (children before parent) to match the
    // surface annotator, which assigns occurrence indices bottom-up during rendering
    // (children are rendered/annotated before parents in ttermToMathNodes).
    if (term.tag === 'App' && this.getAppHead(term) === name) {
      // Post-order: first recurse into args (they might contain nested occurrences)
      const recursedTerm = this.replaceConstInArgs(term, name, replacement, targetOcc, counter, definitions);
      // Then count this node
      counter.count++;
      if (counter.count === targetOcc) {
        // Replace just the Const at the head of this App chain (original term, not recursed)
        return this.replaceAppHead(term, replacement);
      }
      return recursedTerm;
    }

    switch (term.tag) {
      case 'Const':
        // Bare Const (not in App position) — don't count as an "application occurrence"
        return term;

      case 'App': {
        // App whose head is NOT Const(name).
        // If the head has implicit args, skip those subtrees for occurrence counting
        // to match the surface annotator (which strips implicit args).
        if (definitions) {
          const { head, args } = this.collectAppSpine(term);
          if (head.tag === 'Const') {
            const implicitPositions = this.getImplicitPositions(head.name, definitions);
            if (implicitPositions && implicitPositions.size > 0) {
              let changed = false;
              const newArgs = args.map((arg, i) => {
                if (implicitPositions.has(i)) return arg; // skip implicit subtrees
                const newArg = this.replaceConstAtOccurrenceImpl(arg, name, replacement, targetOcc, counter, definitions);
                if (newArg !== arg) changed = true;
                return newArg;
              });
              if (!changed) return term;
              let result: TTKTerm = head;
              for (const arg of newArgs) {
                result = { tag: 'App', fn: result, arg };
              }
              return result;
            }
          }
        }
        // No implicit positions — use original recursive descent
        const fn = this.replaceConstAtOccurrenceImpl(term.fn, name, replacement, targetOcc, counter, definitions);
        const arg = this.replaceConstAtOccurrenceImpl(term.arg, name, replacement, targetOcc, counter, definitions);
        if (fn === term.fn && arg === term.arg) return term;
        return { tag: 'App', fn, arg };
      }

      case 'Binder': {
        const domain = this.replaceConstAtOccurrenceImpl(term.domain, name, replacement, targetOcc, counter, definitions);
        const body = this.replaceConstAtOccurrenceImpl(term.body, name, replacement, targetOcc, counter, definitions);
        if (domain === term.domain && body === term.body) return term;
        return { tag: 'Binder', binderKind: term.binderKind, name: term.name, domain, body };
      }

      case 'Match': {
        const scrutinee = this.replaceConstAtOccurrenceImpl(term.scrutinee, name, replacement, targetOcc, counter, definitions);
        let clausesChanged = false;
        const clauses = term.clauses.map(c => {
          const rhs = this.replaceConstAtOccurrenceImpl(c.rhs, name, replacement, targetOcc, counter, definitions);
          if (rhs !== c.rhs) clausesChanged = true;
          return rhs === c.rhs ? c : { ...c, rhs };
        });
        if (scrutinee === term.scrutinee && !clausesChanged) return term;
        return { tag: 'Match', scrutinee, clauses };
      }

      default:
        return term;
    }
  }

  /**
   * Replace the head Const of an App chain with a replacement term.
   * E.g., App(App(Const("f"), a), b) → App(App(replacement, a), b)
   */
  private replaceAppHead(term: TTKTerm, replacement: TTKTerm): TTKTerm {
    if (term.tag === 'Const') return replacement;
    if (term.tag === 'App') {
      const fn = this.replaceAppHead(term.fn, replacement);
      return { tag: 'App', fn, arg: term.arg };
    }
    return term;
  }

  /**
   * Recurse into the arguments of an App chain (not the head) to find
   * other occurrences of name in nested positions.
   * Skips implicit arg positions to match surface counting.
   */
  private replaceConstInArgs(
    term: TTKTerm,
    name: string,
    replacement: TTKTerm,
    targetOcc: number,
    counter: { count: number },
    definitions?: DefinitionsMap,
  ): TTKTerm {
    if (term.tag !== 'App') return term;

    // If the target function has implicit args, skip those subtrees
    if (definitions) {
      const { head, args } = this.collectAppSpine(term);
      if (head.tag === 'Const') {
        const implicitPositions = this.getImplicitPositions(head.name, definitions);
        if (implicitPositions && implicitPositions.size > 0) {
          let changed = false;
          const newArgs = args.map((arg, i) => {
            if (implicitPositions.has(i)) return arg; // skip implicit
            const newArg = this.replaceConstAtOccurrenceImpl(arg, name, replacement, targetOcc, counter, definitions);
            if (newArg !== arg) changed = true;
            return newArg;
          });
          if (!changed) return term;
          let result: TTKTerm = head;
          for (const arg of newArgs) {
            result = { tag: 'App', fn: result, arg };
          }
          return result;
        }
      }
    }

    // Fallback: original recursive behavior
    const fn = this.replaceConstInArgs(term.fn, name, replacement, targetOcc, counter, definitions);
    const arg = this.replaceConstAtOccurrenceImpl(term.arg, name, replacement, targetOcc, counter, definitions);
    if (fn === term.fn && arg === term.arg) return term;
    return { tag: 'App', fn, arg };
  }
}
