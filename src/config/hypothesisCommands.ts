/**
 * Hypothesis-specific commands
 *
 * Commands available when a hypothesis is focused:
 * - n: Edit name (with current value pre-filled)
 * - e: Edit expression (with current value pre-filled)
 * - s: Set (clear fields, then choose n/e)
 * - d: Delete (with safety check for usage)
 */

import { Command, createCommand } from '../types/commands';
import { Assumption } from '../types/enhanced-focus';

export interface HypothesisCommandHandlers {
  onEditExpression: (id: string, clearFirst?: boolean) => void;
  onEditName: (id: string, clearFirst?: boolean) => void;
  onDelete: (id: string) => void;
  onCheckUsage?: (hypothesisName: string) => boolean; // Check if hypothesis is used
}

/**
 * Create commands for a focused hypothesis
 */
export function createHypothesisCommands(
  hypothesis: Assumption,
  index: number,
  handlers: HypothesisCommandHandlers
): Command[] {
  const { onEditExpression, onEditName, onCheckUsage } = handlers;

  return [
    // Edit name (pre-filled)
    createCommand(
      `hyp-${hypothesis.id}-edit-name`,
      'n',
      'Name',
      () => {
        onEditName(hypothesis.id, false); // Pre-fill with current name
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Name'],
          mode: 'edit' as const,
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis name',
      }
    ),

    // Edit expression (pre-filled)
    createCommand(
      `hyp-${hypothesis.id}-edit-expr`,
      'e',
      'Edit',
      () => {
        onEditExpression(hypothesis.id, false); // Pre-fill with current expression
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Expression'],
          mode: 'edit' as const,
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis expression',
      }
    ),

    // Set (clear fields, then choose n/e)
    createCommand(
      `hyp-${hypothesis.id}-set`,
      's',
      'Set',
      () => {
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Set'],
          preventDefault: true,
        };
      },
      {
        description: 'Set hypothesis (clear fields first)',
        children: [
          // Set name (sn)
          createCommand(
            `hyp-${hypothesis.id}-set-name`,
            'n',
            'Name',
            () => {
              onEditName(hypothesis.id, true); // Clear first
              return {
                navigationPath: ['Hypotheses', `${index}`, 'Name'],
                mode: 'edit' as const,
                preventDefault: true,
              };
            },
            {
              description: 'Set name (clear field)',
            }
          ),

          // Set expression (se)
          createCommand(
            `hyp-${hypothesis.id}-set-expr`,
            'e',
            'Expression',
            () => {
              onEditExpression(hypothesis.id, true); // Clear first
              return {
                navigationPath: ['Hypotheses', `${index}`, 'Expression'],
                mode: 'edit' as const,
                preventDefault: true,
              };
            },
            {
              description: 'Set expression (clear field)',
            }
          ),
        ],
      }
    ),

    // Delete (with usage check)
    createCommand(
      `hyp-${hypothesis.id}-delete`,
      'd',
      'Delete',
      () => {
        // Check if hypothesis is used
        if (onCheckUsage) {
          const isUsed = onCheckUsage(hypothesis.name);
          if (isUsed) {
            // Show error - hypothesis is used and cannot be deleted
            alert(`Cannot delete hypothesis "${hypothesis.name}" because it is used in other hypotheses, the goal, or the proof body.`);
            return {
              navigationPath: ['Hypotheses', `${index}`],
              preventDefault: true,
            };
          }
        }

        // Safe to delete - show confirmation
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Confirm Delete'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete hypothesis (with safety check)',
      }
    ),
  ];
}

/**
 * Create confirmation dialog commands for delete
 */
export function createDeleteConfirmationCommands(
  hypothesis: Assumption,
  index: number,
  onConfirm: () => void
): Command[] {
  return [
    // Yes - confirm delete
    createCommand(
      `hyp-${hypothesis.id}-delete-yes`,
      'y',
      'Yes',
      () => {
        onConfirm();
        return {
          navigationPath: ['Hypotheses'],
          preventDefault: true,
        };
      },
      {
        description: 'Confirm delete',
      }
    ),

    // No - cancel delete
    createCommand(
      `hyp-${hypothesis.id}-delete-no`,
      'n',
      'No',
      () => {
        return {
          navigationPath: ['Hypotheses', `${index}`],
          preventDefault: true,
        };
      },
      {
        description: 'Cancel delete',
      }
    ),
  ];
}
