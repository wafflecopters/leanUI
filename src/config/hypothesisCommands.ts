/**
 * Hypothesis-specific commands
 *
 * Commands available when a hypothesis is focused:
 * - e: Edit expression
 * - n: Edit name
 * - d: Delete (with confirmation)
 * - r: Reset (prefix for 're' and 'rn')
 */

import { Command, createCommand } from '../types/commands';
import { Assumption } from '../types/enhanced-focus';

export interface HypothesisCommandHandlers {
  onEditExpression: (id: string) => void;
  onEditName: (id: string) => void;
  onDelete: (id: string) => void;
}

/**
 * Create commands for a focused hypothesis
 */
export function createHypothesisCommands(
  hypothesis: Assumption,
  index: number,
  handlers: HypothesisCommandHandlers
): Command[] {
  const { onEditExpression, onEditName } = handlers;

  return [
    // Edit expression
    createCommand(
      `hyp-${hypothesis.id}-edit-expr`,
      'e',
      'Edit',
      () => {
        onEditExpression(hypothesis.id);
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

    // Edit name
    createCommand(
      `hyp-${hypothesis.id}-edit-name`,
      'n',
      'Name',
      () => {
        onEditName(hypothesis.id);
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

    // Delete (will show confirmation)
    createCommand(
      `hyp-${hypothesis.id}-delete`,
      'd',
      'Delete',
      () => {
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Confirm Delete'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete hypothesis',
      }
    ),

    // Reset (prefix command with children)
    createCommand(
      `hyp-${hypothesis.id}-reset`,
      'r',
      'Reset',
      () => {
        return {
          navigationPath: ['Hypotheses', `${index}`, 'Reset'],
          preventDefault: true,
        };
      },
      {
        description: 'Reset (edit with selection)',
        children: [
          // Reset expression (re)
          createCommand(
            `hyp-${hypothesis.id}-reset-expr`,
            'e',
            'Expression',
            () => {
              onEditExpression(hypothesis.id);
              return {
                navigationPath: ['Hypotheses', `${index}`, 'Expression'],
                mode: 'edit' as const,
                preventDefault: true,
                escapeLevels: 2, // Pop both 'Reset' and 'Expression' levels
              };
            },
            {
              description: 'Reset expression (select all)',
            }
          ),

          // Reset name (rn)
          createCommand(
            `hyp-${hypothesis.id}-reset-name`,
            'n',
            'Name',
            () => {
              onEditName(hypothesis.id);
              return {
                navigationPath: ['Hypotheses', `${index}`, 'Name'],
                mode: 'edit' as const,
                preventDefault: true,
                escapeLevels: 2, // Pop both 'Reset' and 'Name' levels
              };
            },
            {
              description: 'Reset name (select all)',
            }
          ),
        ],
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
