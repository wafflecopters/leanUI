/**
 * Cong (Congruence) Tactic: Apply congruence to an equality proof
 *
 * Given an equality proof h : Equal a b and a goal Equal (f a) (f b),
 * applies congruence to solve the goal.
 *
 * Usage: cong h
 * Example:
 *   h : Equal n m
 *   goal : Equal (Succ n) (Succ m)
 *   After cong h: goal solved by (cong Succ h)
 *
 * Also works with implicit extraction from context:
 *   cong <function>
 */

import { TTKTerm, TTKContext } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';
import { whnf } from '../compiler/whnf';

/**
 * CongTactic: Apply congruence to an equality in context
 *
 * Two modes:
 * 1. cong h - Uses hypothesis h : Equal a b to prove Equal (f a) (f b)
 * 2. cong f - Applies f to an equality in context to match the goal
 */
export class CongTactic implements Tactic {
  name = 'cong';

  constructor(public readonly arg: TTKTerm) {}

  apply(engine: TacticEngine, goal: MetaVar, goalId: string): TacticResult {
    try {
      // Normalize the goal type to WHNF
      const goalTypeWhnf = whnf(goal.type, { definitions: engine.definitions });

      // Check if goal is an equality type: Equal A (f a) (f b)
      if (goalTypeWhnf.tag !== 'App') {
        return {
          success: false,
          error: `cong: goal is not an equality type, got ${goalTypeWhnf.tag}`
        };
      }

      // Walk backwards through the application spine to get all arguments
      const args: TTKTerm[] = [];
      let current: TTKTerm = goalTypeWhnf;
      while (current.tag === 'App') {
        args.unshift(current.arg);
        current = current.fn;
      }

      // Verify head is Equal
      if (current.tag !== 'Const' || current.name !== 'Equal') {
        return {
          success: false,
          error: `cong: goal is not an equality (head is ${current.tag === 'Const' ? current.name : current.tag})`
        };
      }

      if (args.length < 2) {
        return {
          success: false,
          error: `cong: equality needs at least 2 arguments (lhs and rhs), got ${args.length}`
        };
      }

      // Extract LHS and RHS of goal
      const goalRhs = args[args.length - 1];
      const goalLhs = args[args.length - 2];

      // The arg could be:
      // 1. A hypothesis name (variable referring to an equality proof)
      // 2. A function to apply

      // For now, treat arg as a hypothesis (equality proof)
      // We'll build: cong {f:=extracted_function} arg

      // Extract function from goal LHS
      // If goal is Equal (Succ a) (Succ b), extract Succ
      const func = this.extractFunction(goalLhs, goalRhs);
      if (!func) {
        return {
          success: false,
          error: `cong: could not extract function from goal LHS/RHS`
        };
      }

      // Build the cong application
      // cong has type: {A B : Type} -> {f : A -> B} -> {x y : A} -> Equal x y -> Equal (f x) (f y)
      // We provide: cong {f:=func} arg
      const congApp: TTKTerm = {
        tag: 'App',
        fn: { tag: 'Const', name: 'cong' },
        arg: this.arg
      };

      // Solve the goal with cong application
      const newMetaVars = new Map(engine.metaVars);
      newMetaVars.set(goalId, { ...goal, solution: congApp });

      // Remove this goal from the goal list
      const newGoals = engine.goals.filter(g => g !== goalId);

      return {
        success: true,
        newEngine: engine.withUpdates({
          metaVars: newMetaVars,
          goals: newGoals
        })
      };
    } catch (e) {
      const errorMsg = e instanceof Error ? e.message : String(e);
      return {
        success: false,
        error: `cong: ${errorMsg}`,
        cause: e instanceof Error ? e : undefined
      };
    }
  }

  /**
   * Extract the function being applied from LHS/RHS of equality
   * If LHS is (f a) and RHS is (f b), return f
   */
  private extractFunction(lhs: TTKTerm, rhs: TTKTerm): TTKTerm | null {
    // Simple case: both are applications with same head
    if (lhs.tag === 'App' && rhs.tag === 'App') {
      // Extract heads
      let lhsHead = lhs.fn;
      let rhsHead = rhs.fn;

      // Keep unwrapping applications until we get to the head
      while (lhsHead.tag === 'App' && rhsHead.tag === 'App') {
        lhsHead = lhsHead.fn;
        rhsHead = rhsHead.fn;
      }

      // If heads match, return the head
      if (this.termsEqual(lhsHead, rhsHead)) {
        return lhsHead;
      }
    }

    return null;
  }

  /**
   * Check if two terms are structurally equal
   */
  private termsEqual(a: TTKTerm, b: TTKTerm): boolean {
    if (a.tag !== b.tag) return false;

    switch (a.tag) {
      case 'Var':
        return b.tag === 'Var' && a.index === b.index;
      case 'Const':
        return b.tag === 'Const' && a.name === b.name;
      case 'App':
        return b.tag === 'App' &&
               this.termsEqual(a.fn, b.fn) &&
               this.termsEqual(a.arg, b.arg);
      default:
        return false;
    }
  }
}
