import { TTKTerm } from "./kernel";
import { Constraint, MetaVar, TTKContext, TCEnv } from "./term";

export function solveConstraints(
  metaVars: Map<string, MetaVar>,
  constraints: Constraint[],
  liftContext?: TTKContext
): { constraints: Constraint[], metaVars: Map<string, MetaVar> } {
  const stillStuck: Constraint[] = [];

  const newMetaVars = new Map(metaVars);

  for (const constraint of constraints) {
    const meta = newMetaVars.get(constraint.meta)!;

    if (meta.solution !== null) continue;

    if (canSolveMeta(meta, constraint.rhs)) {
      newMetaVars.set(constraint.meta, { ...meta, solution: constraint.rhs, ctx: liftContext ?? meta.ctx });
    } else {
      stillStuck.push(constraint);
    }
  }

  return { constraints: stillStuck, metaVars: newMetaVars };
}

export function canSolveMeta(meta: MetaVar, rhs: TTKTerm): boolean {
  return maxFreeVarIndex(rhs) < meta.ctx.length;
}

function maxFreeVarIndex(term: TTKTerm): number {
  return maxFreeVarIndexAt(term, 0)
}

function maxFreeVarIndexAt(term: TTKTerm, depth: number): number {
  switch (term.tag) {
    case 'Var':
      return term.index >= depth ? term.index - depth : -1;
    case 'Sort':
    case 'Const':
      return -1;
    case 'Binder':
      if (term.binderKind.tag === 'BLet') {
        // In Let, defVal is at depth, body is at depth+1
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.binderKind.defVal, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      } else {
        // Pi, Lam, etc.
        return Math.max(
          maxFreeVarIndexAt(term.domain, depth),
          maxFreeVarIndexAt(term.body, depth + 1)
        );
      }
    case 'App':
      return Math.max(
        maxFreeVarIndexAt(term.fn, depth),
        maxFreeVarIndexAt(term.arg, depth),
      );
    case 'Hole':
    case 'Meta':
      return -Infinity; // No free variables
    case 'Annot':
      return Math.max(maxFreeVarIndexAt(term.term, depth), maxFreeVarIndexAt(term.type, depth));
    case 'Match':
      return Math.max(maxFreeVarIndexAt(term.scrutinee, depth), ...term.clauses.map(c => maxFreeVarIndexAt(c.rhs, depth)));

    case 'ULevel':
      return -1;
  }
}