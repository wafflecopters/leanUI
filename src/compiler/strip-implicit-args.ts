import type { TTKClause, TTKTerm } from './kernel';
import { countKernelClauseBindings } from './pattern-binders';
import { createNamedArgLookup, type DefinitionsMap } from './term';

function collectAppSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let current = term;
  while (current.tag === 'App') {
    args.unshift(current.arg);
    current = current.fn;
  }
  return { head: current, args };
}

function rebuildApp(head: TTKTerm, args: TTKTerm[]): TTKTerm {
  return args.reduce<TTKTerm>((fn, arg) => ({ tag: 'App', fn, arg }), head);
}

function stripClause(clause: TTKClause, definitions: DefinitionsMap): TTKClause {
  return {
    ...clause,
    rhs: stripImplicitArgs(clause.rhs, definitions, countKernelClauseBindings(clause)),
  };
}

export function stripImplicitArgs(
  term: TTKTerm,
  definitions: DefinitionsMap,
  depth: number = 0,
  inTypePosition: boolean = false,
): TTKTerm {
  switch (term.tag) {
    case 'App': {
      const { head, args } = collectAppSpine(term);
      const strippedHead = stripImplicitArgs(head, definitions, depth, inTypePosition);
      const strippedArgs = args.map(arg => stripImplicitArgs(arg, definitions, depth, inTypePosition));

      if (inTypePosition || strippedHead.tag !== 'Const') {
        return rebuildApp(strippedHead, strippedArgs);
      }

      const namedArgMap = createNamedArgLookup(definitions)(strippedHead.name);
      if (!namedArgMap || namedArgMap.size === 0) {
        return rebuildApp(strippedHead, strippedArgs);
      }

      const implicitPositions = new Set(namedArgMap.values());
      const explicitArgs = strippedArgs.filter((_, index) => !implicitPositions.has(index));
      return rebuildApp(strippedHead, explicitArgs);
    }
    case 'Binder': {
      const binderKind = term.binderKind.tag === 'BLet'
        ? {
            tag: 'BLet' as const,
            defVal: stripImplicitArgs(term.binderKind.defVal, definitions, depth, false),
          }
        : term.binderKind;
      return {
        tag: 'Binder',
        name: term.name,
        binderKind,
        domain: stripImplicitArgs(term.domain, definitions, depth, true),
        body: stripImplicitArgs(
          term.body,
          definitions,
          depth + 1,
          term.binderKind.tag === 'BPi',
        ),
      };
    }
    case 'Sort':
      return { tag: 'Sort', level: stripImplicitArgs(term.level, definitions, depth, false) };
    case 'Annot':
      return {
        tag: 'Annot',
        term: stripImplicitArgs(term.term, definitions, depth, false),
        type: stripImplicitArgs(term.type, definitions, depth, true),
      };
    case 'Match':
      return {
        tag: 'Match',
        scrutinee: stripImplicitArgs(term.scrutinee, definitions, depth, false),
        clauses: term.clauses.map(clause => stripClause(clause, definitions)),
      };
    default:
      return term;
  }
}
