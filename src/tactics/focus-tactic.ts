/**
 * FocusTactic: Focus on the first subgoal until solved
 *
 * This implements Lean-style bullet syntax (·) for managing multiple subgoals.
 * When a tactic like `apply trans` creates multiple goals, bullets let you
 * solve them one at a time in a structured way:
 *
 * apply trans
 * · exact proof1  -- Focus on first subgoal
 * · exact proof2  -- Focus on second subgoal
 *
 * The FocusTactic:
 * 1. Saves the current number of goals
 * 2. Applies nested tactics (which may create more subgoals)
 * 3. Ensures exactly one of the original goals was solved
 * 4. Moves focus to the next goal
 */

import { TTKTerm } from '../compiler/kernel';
import { MetaVar } from '../compiler/term';
import { TacticEngine } from './tacticsEngine';
import { Tactic, TacticResult } from './tactic';

export class FocusTactic implements Tactic {
  name = 'focus';

  constructor(public readonly tactics: Tactic[]) {}

  apply(engine: TacticEngine, _goal: MetaVar, _goalId: string): TacticResult {
    if (this.tactics.length === 0) {
      return {
        success: false,
        error: 'focus: no tactics provided'
      };
    }

    // Record initial goal count and focused goal
    const initialGoalCount = engine.goals.length;
    const initialFocusedGoalId = engine.getFocusedGoalId();

    if (!initialFocusedGoalId) {
      return {
        success: false,
        error: 'focus: no focused goal'
      };
    }

    // Apply tactics in sequence, staying focused on the first subgoal
    let current = engine;

    for (const tactic of this.tactics) {
      const currentGoal = current.getFocusedGoal();
      const currentGoalId = current.getFocusedGoalId();

      if (!currentGoal || !currentGoalId) {
        // Goal was solved by previous tactics - this is OK, just stop
        break;
      }

      const result = tactic.apply(current, currentGoal, currentGoalId);
      if (!result.success) {
        return {
          success: false,
          error: `focus: ${result.error}`,
          cause: result.cause
        };
      }

      current = result.newEngine;
    }

    // Verify that the initial focused goal was solved
    const finalFocusedGoalId = current.getFocusedGoalId();

    // If the initial goal still exists in the goal list, it wasn't solved
    if (current.goals.includes(initialFocusedGoalId)) {
      return {
        success: false,
        error: 'focus: bullet (·) did not solve the focused goal'
      };
    }

    // Goal was solved! Focus should automatically move to next goal
    return {
      success: true,
      newEngine: current
    };
  }
}
