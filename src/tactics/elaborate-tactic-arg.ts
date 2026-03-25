/**
 * Shared tactic argument elaboration — converts surface terms to kernel terms
 * in the context of a tactic goal.
 *
 * Extracted from compile.ts's `surfaceToKernel` closure inside
 * `elaborateTacticBlock()` so both compilation and the UI can use the
 * same elaboration logic.
 */

import { TTerm } from '../compiler/surface';
import { TTKTerm, TTKBinderKind } from '../compiler/kernel';
import { TTKContext, DefinitionsMap, NamedArgMap, createNamedArgLookup } from '../compiler/term';
import { elabToKernelWithMap } from '../compiler/elab';
import { ExactTactic, AssumptionTactic, IntroTactic, IntrosTactic, ApplyTactic, TacticSequence, Tactic } from './tactic';
import { CasesTactic } from './cases-tactic';
import { ReflexivityTactic } from './reflexivity-tactic';
import { InductionTactic } from './induction-tactic';
import { RewriteTactic } from './rewrite-tactic';
import { SymmetryTactic } from './symmetry-tactic';
import { TransitivityTactic } from './transitivity-tactic';
import { CongTactic } from './cong-tactic';
import { SubstTactic } from './subst-tactic';
import { HaveTactic } from './have-tactic';
import { ObtainTactic } from './obtain-tactic';
import { SufficesTactic } from './suffices-tactic';
import { UnfoldTactic } from './unfold-tactic';
import { ConstructorTactic } from './constructor-tactic';
import { FocusTactic } from './focus-tactic';

// ============================================================================
// Argument elaboration
// ============================================================================

/**
 * Convert a surface term (TTerm) to a kernel term (TTKTerm) using the
 * current goal context for name resolution.
 *
 * - Const names found in goalCtx become Var (de Bruijn indexed)
 * - Const names not in goalCtx stay as Const (global definitions)
 * - Implicit args are inserted for Const heads with namedArgMaps
 * - Binder/MultiBinder bodies are elaborated with extended name context
 */
/**
 * @param paramNameMap — optional remapping for case branch pattern names
 *   (e.g., user writes `n` but context has `n0`). Maps user name → context name.
 */
export function elaborateTacticArg(
  term: TTerm,
  goalCtx: TTKContext,
  definitions: DefinitionsMap,
  depth: number = 0,
  paramNameMap?: Map<string, string>,
): TTKTerm {
  const nameContext: string[] = goalCtx.map(binding => binding.name);
  const namedArgLookup = createNamedArgLookup(definitions);

  function convert(term: TTerm, depth: number): TTKTerm {
    switch (term.tag) {
      case 'Var':
        return { tag: 'Var', index: term.index };

      case 'Const': {
        // Remap pattern param names if in a case branch
        const lookupName = paramNameMap?.get(term.name) ?? term.name;
        for (let i = nameContext.length - 1; i >= 0; i--) {
          if (nameContext[i] === lookupName) {
            return { tag: 'Var', index: nameContext.length - 1 - i + depth };
          }
        }
        return { tag: 'Const', name: term.name };
      }

      case 'App':
        return insertImplicitHolesForApp(term, convert, depth, namedArgLookup);

      case 'Sort':
        return { tag: 'Sort', level: convert(term.level, depth) as any };

      case 'Hole':
        return { tag: 'Hole', id: term.id };

      case 'ULevel':
        return { tag: 'ULevel' };

      case 'ULit':
        return { tag: 'ULit', n: term.n };

      case 'UOmega':
        return { tag: 'UOmega' };

      case 'Binder': {
        const domain = term.domain ? convert(term.domain, depth) : undefined;
        let binderKind: TTKBinderKind;
        if (term.binderKind.tag === 'BLetTT') {
          binderKind = { tag: 'BLet', defVal: convert(term.binderKind.defVal, depth) };
        } else if (term.binderKind.tag === 'BLamTT') {
          binderKind = { tag: 'BLam' };
        } else {
          binderKind = { tag: 'BPi' };
        }
        nameContext.push(term.name);
        const body = convert(term.body, depth);
        nameContext.pop();
        return {
          tag: 'Binder',
          binderKind,
          name: term.name,
          domain: domain ?? { tag: 'Hole', id: '_' },
          body,
        };
      }

      case 'MultiBinder': {
        const domain = convert(term.domain, depth);
        const binderKind: TTKBinderKind = term.binderKind.tag === 'BLamTT'
          ? { tag: 'BLam' }
          : term.binderKind.tag === 'BPiTT'
          ? { tag: 'BPi' }
          : { tag: 'BLet', defVal: convert((term.binderKind as any).defVal, depth) };
        for (const name of term.names) {
          nameContext.push(name);
        }
        let result: TTKTerm = convert(term.body, depth);
        for (let i = term.names.length - 1; i >= 0; i--) {
          nameContext.pop();
          result = { tag: 'Binder', binderKind, name: term.names[i], domain, body: result };
        }
        return result;
      }

      case 'Annot': {
        const annotTerm = convert(term.term, depth);
        const annotType = convert(term.type, depth);
        return { tag: 'Annot' as any, term: annotTerm, type: annotType };
      }

      default:
        return elabToKernelWithMap(term, new Map(), [], []);
    }
  }

  return convert(term, depth);
}

/**
 * Insert Holes for implicit params when the head of an App chain is a Const
 * with a namedArgMap.
 */
function insertImplicitHolesForApp(
  term: TTerm,
  convertTerm: (t: TTerm, depth: number) => TTKTerm,
  depth: number,
  namedArgLookup: (name: string) => NamedArgMap | undefined,
): TTKTerm {
  const args: TTerm[] = [];
  let head: TTerm = term;
  while (head.tag === 'App') {
    args.unshift(head.arg);
    head = head.fn;
  }

  let kernelHead = convertTerm(head, depth);

  if (kernelHead.tag === 'Const') {
    const namedArgs = namedArgLookup(kernelHead.name);
    if (namedArgs) {
      for (const [paramName] of namedArgs) {
        kernelHead = { tag: 'App', fn: kernelHead, arg: { tag: 'Hole', id: '_implicit_' + paramName } };
      }
    }
  }

  let result = kernelHead;
  for (const arg of args) {
    result = { tag: 'App', fn: result, arg: convertTerm(arg, depth) };
  }
  return result;
}

// ============================================================================
// Whether an arg should be kept as a name (not elaborated)
// ============================================================================

/**
 * Some tactic args are names/identifiers that shouldn't be elaborated to
 * kernel terms (e.g., intro names, unfold targets, have hypothesis names).
 */
export function shouldKeepArgAsName(tacticName: string, argIndex: number, totalArgs: number): boolean {
  if (['sorry', 'intro', 'intros', 'unfold', 'fold'].includes(tacticName)) return true;
  if (tacticName === 'have' && argIndex === 0) return true;
  if (tacticName === 'obtain' && argIndex < totalArgs - 1) return true;
  if (tacticName === 'suffices' && argIndex === 0) return true;
  return false;
}

// ============================================================================
// Tactic command → Tactic instance
// ============================================================================

/**
 * Convert a tactic command (with already-elaborated args) to a Tactic instance.
 * Args should be TTKTerm where elaboration was needed, or TTerm/Const for names.
 */
export function tacticCommandToTactic(
  cmd: { name: string; args: Array<TTerm | TTKTerm>; focusedTactics?: Tactic[] }
): Tactic | 'sorry' {
  switch (cmd.name) {
    case 'sorry':
      return 'sorry';

    case 'focus':
      if (!cmd.focusedTactics || cmd.focusedTactics.length === 0) {
        throw new Error(`'focus' tactic requires nested tactics`);
      }
      return new FocusTactic(cmd.focusedTactics);

    case 'exact':
      if (cmd.args.length !== 1) {
        throw new Error(`'exact' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new ExactTactic(cmd.args[0] as TTKTerm);

    case 'assumption':
      if (cmd.args.length !== 0) {
        throw new Error(`'assumption' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new AssumptionTactic();

    case 'intro': {
      if (cmd.args.length > 1) {
        throw new Error(`'intro' tactic requires 0 or 1 arguments, got ${cmd.args.length}`);
      }
      const introName = cmd.args.length === 1 && cmd.args[0].tag === 'Const'
        ? (cmd.args[0] as any).name
        : undefined;
      return new IntroTactic(introName);
    }

    case 'intros': {
      const names = cmd.args.map(arg => {
        if (arg.tag !== 'Const') {
          throw new Error(`'intros' tactic arguments must be identifiers, got ${arg.tag}`);
        }
        return (arg as any).name;
      });
      return new IntrosTactic(names.length > 0 ? names : undefined);
    }

    case 'apply':
      if (cmd.args.length !== 1) {
        throw new Error(`'apply' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new ApplyTactic(cmd.args[0] as TTKTerm);

    case 'cases':
      if (cmd.args.length !== 1) {
        throw new Error(`'cases' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new CasesTactic(cmd.args[0] as TTKTerm);

    case 'induction':
      if (cmd.args.length !== 1) {
        throw new Error(`'induction' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new InductionTactic(cmd.args[0] as TTKTerm);

    case 'reflexivity':
      if (cmd.args.length !== 0) {
        throw new Error(`'reflexivity' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new ReflexivityTactic();

    case 'rewrite':
      if (cmd.args.length !== 1) {
        throw new Error(`'rewrite' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new RewriteTactic(cmd.args[0] as TTKTerm);

    case 'symmetry':
      if (cmd.args.length !== 0) {
        throw new Error(`'symmetry' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new SymmetryTactic();

    case 'transitivity':
      if (cmd.args.length !== 1) {
        throw new Error(`'transitivity' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new TransitivityTactic(cmd.args[0] as TTKTerm);

    case 'cong':
      if (cmd.args.length !== 1) {
        throw new Error(`'cong' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new CongTactic(cmd.args[0] as TTKTerm);

    case 'subst':
      if (cmd.args.length !== 1) {
        throw new Error(`'subst' tactic requires exactly 1 argument, got ${cmd.args.length}`);
      }
      return new SubstTactic(cmd.args[0] as TTKTerm);

    case 'rw': {
      if (cmd.args.length === 0) {
        throw new Error(`'rw' tactic requires at least 1 argument`);
      }
      const rewrites = cmd.args.map(arg => new RewriteTactic(arg as TTKTerm));
      return new TacticSequence('rw', [...rewrites, new ReflexivityTactic()]);
    }

    case 'erw': {
      if (cmd.args.length === 0) {
        throw new Error(`'erw' tactic requires at least 1 argument`);
      }
      const enhancedRewrites = cmd.args.map(arg => new RewriteTactic(arg as TTKTerm, { enhanced: true }));
      return new TacticSequence('erw', [...enhancedRewrites, new ReflexivityTactic()]);
    }

    case 'constructor':
      if (cmd.args.length !== 0) {
        throw new Error(`'constructor' tactic requires no arguments, got ${cmd.args.length}`);
      }
      return new ConstructorTactic();

    case 'unfold': {
      if (cmd.args.length === 0) {
        throw new Error(`'unfold' tactic requires at least 1 argument`);
      }
      const unfoldNames = cmd.args.map(arg => {
        if (arg.tag !== 'Const') {
          throw new Error(`'unfold' tactic arguments must be identifiers, got ${arg.tag}`);
        }
        return (arg as any).name;
      });
      return new UnfoldTactic(unfoldNames);
    }

    case 'have': {
      if (cmd.args.length !== 3) {
        throw new Error(`'have' tactic requires name, type, and proof (got ${cmd.args.length} args)`);
      }
      const haveName = cmd.args[0].tag === 'Const' ? (cmd.args[0] as any).name : '_';
      return new HaveTactic(haveName, cmd.args[1] as TTKTerm, cmd.args[2] as TTKTerm);
    }

    case 'obtain': {
      if (cmd.args.length < 2) {
        throw new Error(`'obtain' tactic requires at least one name and a proof expression`);
      }
      const obtainNames: string[] = [];
      for (let i = 0; i < cmd.args.length - 1; i++) {
        const arg = cmd.args[i];
        obtainNames.push(arg.tag === 'Const' ? (arg as any).name : '_');
      }
      const obtainProof = cmd.args[cmd.args.length - 1] as TTKTerm;
      return new ObtainTactic(obtainNames, obtainProof);
    }

    case 'suffices': {
      if (cmd.args.length !== 2) {
        throw new Error(`'suffices' tactic requires name and type (got ${cmd.args.length} args)`);
      }
      const suffName = cmd.args[0].tag === 'Const' ? (cmd.args[0] as any).name : '_';
      const closingTactics = cmd.focusedTactics ?? [];
      if (closingTactics.length === 0) {
        throw new Error(`'suffices' tactic requires closing tactics after 'by'`);
      }
      return new SufficesTactic(suffName, cmd.args[1] as TTKTerm, closingTactics);
    }

    default:
      throw new Error(`Unknown tactic: ${cmd.name}`);
  }
}
