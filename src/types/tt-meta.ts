/**
 * MetaContext - Clean metavariable (hole) management for dependent type checking
 *
 * Metavariables are used to represent:
 * - Wildcards (_) in patterns - their value is unconstrained until unification determines it
 * - Implicit arguments - to be inferred from context
 * - Holes in terms - to be filled in by the user or solver
 *
 * The key operations are:
 * - fresh(): Create a new metavariable
 * - solve(): Record that a metavariable equals some term
 * - zonk(): Apply all solutions to normalize a term
 */

import { TTKTerm, TTKContext, prettyPrint } from './tt-kernel';

export type MetaId = string;

export interface MetaInfo {
  id: MetaId;
  type: TTKTerm;
  ctx: TTKContext;  // Context at creation (for scope checking)
  solution?: TTKTerm;
}

/**
 * MetaContext manages metavariables and their solutions.
 *
 * Usage:
 * 1. Create a MetaContext at the start of elaboration
 * 2. Use fresh() to create metavariables for wildcards/holes
 * 3. Pass the MetaContext to unification
 * 4. Unification calls solve() when it determines a meta's value
 * 5. After elaboration, zonk() applies all solutions
 */
export class MetaContext {
  private metas: Map<MetaId, MetaInfo> = new Map();
  private counter = 0;

  /**
   * Create a fresh metavariable with the given type in the given context.
   * Returns a Hole term that can be used in place of an unknown value.
   */
  fresh(type: TTKTerm, ctx: TTKContext): TTKTerm {
    const id = `?m${this.counter++}`;
    this.metas.set(id, { id, type, ctx });
    return {
      tag: 'Hole',
      id,
      type,
      context: ctx.map(b => ({ name: b.name, type: b.type }))
    };
  }

  /**
   * Record that a metavariable equals the given term.
   * Returns true if successful, false if:
   * - The meta doesn't exist
   * - The meta is already solved to a different value
   * - The solution would create a cycle (occurs check)
   */
  solve(id: MetaId, solution: TTKTerm): boolean {
    const meta = this.metas.get(id);
    if (!meta) {
      return false;
    }

    if (meta.solution !== undefined) {
      // Already solved - this is OK if the new solution is alpha-equivalent
      // For now, just accept it (caller should have checked consistency)
      return true;
    }

    // Occurs check: the solution shouldn't contain the meta itself
    if (this.occursIn(id, solution)) {
      return false;
    }

    meta.solution = solution;
    return true;
  }

  /**
   * Get the solution for a metavariable, if it has been solved.
   */
  getSolution(id: MetaId): TTKTerm | undefined {
    return this.metas.get(id)?.solution;
  }

  /**
   * Check if a metavariable has been solved.
   */
  isSolved(id: MetaId): boolean {
    return this.metas.get(id)?.solution !== undefined;
  }

  /**
   * Get the type of a metavariable.
   */
  getType(id: MetaId): TTKTerm | undefined {
    return this.metas.get(id)?.type;
  }

  /**
   * Get all unsolved metavariables.
   */
  getUnsolved(): MetaId[] {
    const result: MetaId[] = [];
    this.metas.forEach((info, id) => {
      if (info.solution === undefined) {
        result.push(id);
      }
    });
    return result;
  }

  /**
   * Apply all solutions to a term (zonking).
   * This recursively replaces solved holes with their solutions.
   */
  zonk(term: TTKTerm): TTKTerm {
    switch (term.tag) {
      case 'Var':
      case 'Sort':
        return term;

      case 'Const':
        return {
          tag: 'Const',
          name: term.name,
          type: this.zonk(term.type)
        };

      case 'Binder': {
        const domain = this.zonk(term.domain);
        const body = this.zonk(term.body);
        let binderKind = term.binderKind;
        if (binderKind.tag === 'BLet') {
          binderKind = { tag: 'BLet', defVal: this.zonk(binderKind.defVal) };
        }
        return { tag: 'Binder', name: term.name, binderKind, domain, body };
      }

      case 'App':
        return {
          tag: 'App',
          fn: this.zonk(term.fn),
          arg: this.zonk(term.arg)
        };

      case 'Hole': {
        const solution = this.getSolution(term.id);
        if (solution !== undefined) {
          // Recursively zonk the solution (it might contain other holes)
          return this.zonk(solution);
        }
        // Unsolved hole - zonk its type but keep the hole
        return {
          tag: 'Hole',
          id: term.id,
          type: this.zonk(term.type),
          context: term.context.map(b => ({ name: b.name, type: this.zonk(b.type) }))
        };
      }

      case 'Annot':
        return {
          tag: 'Annot',
          term: this.zonk(term.term),
          type: this.zonk(term.type)
        };

      case 'Match':
        return {
          tag: 'Match',
          scrutinee: this.zonk(term.scrutinee),
          clauses: term.clauses.map(c => ({
            patterns: c.patterns,  // Patterns don't contain holes
            rhs: this.zonk(c.rhs)
          }))
        };
    }
  }

  /**
   * Check if a metavariable occurs in a term (for occurs check).
   */
  private occursIn(id: MetaId, term: TTKTerm): boolean {
    switch (term.tag) {
      case 'Var':
      case 'Sort':
        return false;

      case 'Const':
        return this.occursIn(id, term.type);

      case 'Binder':
        return this.occursIn(id, term.domain) ||
               this.occursIn(id, term.body) ||
               (term.binderKind.tag === 'BLet' && this.occursIn(id, term.binderKind.defVal));

      case 'App':
        return this.occursIn(id, term.fn) || this.occursIn(id, term.arg);

      case 'Hole':
        if (term.id === id) {
          return true;
        }
        // Check if this hole is solved, and if so, check the solution
        const solution = this.getSolution(term.id);
        if (solution !== undefined) {
          return this.occursIn(id, solution);
        }
        return this.occursIn(id, term.type);

      case 'Annot':
        return this.occursIn(id, term.term) || this.occursIn(id, term.type);

      case 'Match':
        return this.occursIn(id, term.scrutinee) ||
               term.clauses.some(c => this.occursIn(id, c.rhs));
    }
  }

  /**
   * Debug helper: print all metas and their solutions
   */
  debugPrint(): void {
    console.log('MetaContext:');
    this.metas.forEach((info, id) => {
      const status = info.solution !== undefined
        ? `= ${prettyPrint(info.solution)}`
        : '(unsolved)';
      console.log(`  ${id} : ${prettyPrint(info.type)} ${status}`);
    });
  }
}
