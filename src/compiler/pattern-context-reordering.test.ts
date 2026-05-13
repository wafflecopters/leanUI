import { describe, expect, test } from 'vitest';

import { mkApp, mkConst, mkVar, prettyPrint, type TTKContext, type TTKTerm } from './kernel';
import { recomputeRefinedClauseContext, type AppliedSubstitution } from './patterns';
import { enumerateAppliedSubstitutions } from './subst';

function leq(lhs: TTKTerm, rhs: TTKTerm): TTKTerm {
  return mkApp(mkApp(mkConst('Leq'), lhs), rhs);
}

function succ(term: TTKTerm): TTKTerm {
  return mkApp(mkConst('Succ'), term);
}

function assertNoNegativeVars(term: TTKTerm): void {
  switch (term.tag) {
    case 'Var':
      expect(term.index).toBeGreaterThanOrEqual(0);
      return;
    case 'App':
      assertNoNegativeVars(term.fn);
      assertNoNegativeVars(term.arg);
      return;
    case 'Binder':
      assertNoNegativeVars(term.domain);
      assertNoNegativeVars(term.body);
      if (term.binderKind.tag === 'BLet') {
        assertNoNegativeVars(term.binderKind.defVal);
      }
      return;
    case 'Annot':
      assertNoNegativeVars(term.term);
      assertNoNegativeVars(term.type);
      return;
    case 'Match':
      assertNoNegativeVars(term.scrutinee);
      for (const clause of term.clauses) {
        assertNoNegativeVars(clause.rhs);
      }
      return;
    default:
      return;
  }
}

describe('recomputeRefinedClauseContext', () => {
  test('moves refined ambient hypotheses behind constructor binders instead of creating negative indices', () => {
    const Nat = mkConst('Nat');
    const originalContext: TTKContext = [
      { name: 'a', type: Nat },
      { name: 'b', type: Nat },
      { name: 'c', type: Nat },
      { name: 'hab', type: leq(mkVar(2), mkVar(1)) },
      { name: 'hbc', type: leq(mkVar(2), mkVar(1)) },
      { name: 'n', type: Nat },
      { name: 'm', type: Nat },
      { name: 'p', type: leq(mkVar(1), mkVar(0)) },
    ];

    const appliedSubstitutions: AppliedSubstitution[] = [...enumerateAppliedSubstitutions([
      [7, succ(mkVar(2))],
      [6, succ(mkVar(1))],
    ])];

    const reordered = recomputeRefinedClauseContext(originalContext, appliedSubstitutions, 3);

    expect(reordered.context.map(entry => entry.name)).toEqual(['n', 'm', 'p', 'c', 'hab', 'hbc']);

    for (const entry of reordered.context) {
      assertNoNegativeVars(entry.type);
    }

    expect(prettyPrint(reordered.context[2]!.type, reordered.context.slice(0, 2).map(entry => entry.name).reverse())).toBe('(Leq n m)');
    expect(prettyPrint(reordered.context[4]!.type, reordered.context.slice(0, 4).map(entry => entry.name).reverse())).toBe('(Leq (Succ n) (Succ m))');
    expect(prettyPrint(reordered.context[5]!.type, reordered.context.slice(0, 5).map(entry => entry.name).reverse())).toBe('(Leq (Succ m) c)');
  });

  test('inner indexed constructor refinement keeps the recursive proof argument at Leq m m\'', () => {
    const Nat = mkConst('Nat');
    const originalContext: TTKContext = [
      { name: 'c', type: Nat },
      { name: 'n', type: Nat },
      { name: 'm', type: Nat },
      { name: 'p', type: leq(mkVar(1), mkVar(0)) },
      { name: 'hab', type: leq(succ(mkVar(2)), succ(mkVar(1))) },
      { name: 'hbc', type: leq(succ(mkVar(2)), mkVar(4)) },
      { name: '_pad0', type: Nat },
      { name: "m'", type: Nat },
      { name: 'q', type: leq(mkVar(1), mkVar(0)) },
    ];

    const reordered = recomputeRefinedClauseContext(
      originalContext,
      [
        { varIndex: 2, value: mkVar(6) },
        { varIndex: 7, value: succ(mkVar(1)) },
      ],
      3,
    );

    expect(reordered.context.map(entry => entry.name).slice(0, 5)).toEqual(['m', "m'", 'q', 'n', 'p']);
    expect(prettyPrint(reordered.context[2]!.type, reordered.context.slice(0, 2).map(entry => entry.name).reverse())).toBe("(Leq m m')");
  });
});
