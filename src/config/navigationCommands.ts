/**
 * Application Navigation Commands
 *
 * Defines the keyboard navigation command tree for the Lean UI application.
 */

import {
  Command,
  createCommand,
  createSectionCommand,
  createEscapeCommand,
  buildCommandTree,
  CommandTree,
} from '../types/commands';

/**
 * Create commands for the Goals section
 */
function createGoalsCommands(): Command[] {
  return [
    createCommand(
      'goals-edit',
      'e',
      'Edit',
      (context) => {
        // Trigger edit goal action
        const onEditGoal = context.metadata?.onEditGoal as (() => void) | undefined;
        onEditGoal?.();

        return {
          navigationPath: ['Goals', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit the current goal',
      }
    ),

    createCommand(
      'goals-set',
      's',
      'Set',
      (context) => {
        // Trigger set goal action
        const onSetGoal = context.metadata?.onSetGoal as (() => void) | undefined;
        onSetGoal?.();

        return {
          navigationPath: ['Goals', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Set a new goal (clears existing)',
      }
    ),

    createCommand(
      'goals-clear',
      'd',
      'Delete',
      (context) => {
        // Trigger clear goal action
        const onClearGoal = context.metadata?.onClearGoal as (() => void) | undefined;
        onClearGoal?.();

        return {
          navigationPath: [],
          preventDefault: true,
        };
      },
      {
        description: 'Delete the current goal',
      }
    ),
  ];
}

/**
 * Create commands for the Hypotheses section
 */
function createHypothesesCommands(): Command[] {
  return [
    // Add hypothesis (only when NO hypothesis is selected)
    createCommand(
      'hypotheses-add',
      'a',
      'Add',
      (context) => {
        // Trigger add hypothesis action
        const onAddHypothesis = context.metadata?.onAddHypothesis as (() => void) | undefined;
        onAddHypothesis?.();

        return {
          navigationPath: ['Hypotheses', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Add a new hypothesis',
        isAvailable: (ctx) => ctx.metadata?.selectedHypothesisId == null, // Only when nothing selected
      }
    ),

    // Edit name (only when hypothesis selected) - INLINE
    createCommand(
      'hypotheses-edit-name',
      'n',
      'Name',
      (context) => {
        const index = context.metadata?.selectedHypothesisIndex as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        return {
          navigationPath: ['Hypotheses', String(index), 'EditName'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis name',
        isAvailable: (ctx) => ctx.metadata?.selectedHypothesisId != null,
      }
    ),

    // Edit expression (only when hypothesis selected) - INLINE
    createCommand(
      'hypotheses-edit-expr',
      'e',
      'Edit',
      (context) => {
        const index = context.metadata?.selectedHypothesisIndex as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        return {
          navigationPath: ['Hypotheses', String(index), 'EditExpression'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis expression',
        isAvailable: (ctx) => ctx.metadata?.selectedHypothesisId != null,
      }
    ),

    // Set (clear first, then choose) - only when hypothesis selected
    createCommand(
      'hypotheses-set',
      's',
      'Set',
      (context) => {
        const index = context.metadata?.selectedHypothesisIndex as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        return {
          navigationPath: ['Hypotheses', String(index), 'Set'],
          preventDefault: true,
        };
      },
      {
        description: 'Set hypothesis (clear fields first)',
        isAvailable: (ctx) => ctx.metadata?.selectedHypothesisId != null,
        children: [
          // Set name (sn)
          createCommand(
            'hypotheses-set-name',
            'n',
            'Name',
            (context) => {
              const index = context.metadata?.selectedHypothesisIndex as number | undefined;
              if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

              return {
                navigationPath: ['Hypotheses', String(index), 'SetName'],
                preventDefault: true,
              };
            },
            {
              description: 'Set name (clear field)',
            }
          ),

          // Set expression (se)
          createCommand(
            'hypotheses-set-expr',
            'e',
            'Expression',
            (context) => {
              const index = context.metadata?.selectedHypothesisIndex as number | undefined;
              if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

              return {
                navigationPath: ['Hypotheses', String(index), 'SetExpression'],
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

    // Delete (with usage check) - only when hypothesis selected
    createCommand(
      'hypotheses-delete',
      'd',
      'Delete',
      (context) => {
        const index = context.metadata?.selectedHypothesisIndex as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        // Check if hypothesis is used
        const onCheckUsage = context.metadata?.onCheckHypothesisUsage as ((name: string) => boolean) | undefined;
        const hypothesisName = context.metadata?.selectedHypothesisName as string | undefined;

        if (onCheckUsage && hypothesisName) {
          const isUsed = onCheckUsage(hypothesisName);
          if (isUsed) {
            // Show error - hypothesis is used
            alert(`Cannot delete hypothesis "${hypothesisName}" because it is used in other hypotheses, the goal, or the proof body.`);
            return {
              navigationPath: ['Hypotheses', String(index)],
              preventDefault: true,
            };
          }
        }

        // Safe to delete - show confirmation
        return {
          navigationPath: ['Hypotheses', String(index), 'Confirm Delete'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected hypothesis (with safety check)',
        isAvailable: (ctx) => ctx.metadata?.selectedHypothesisId != null,
      }
    ),
  ];
}

/**
 * Create commands for the Let Bindings section
 */
function createLetBindingsCommands(): Command[] {
  return [
    createCommand(
      'letbindings-add',
      'a',
      'Add',
      (context) => {
        // Trigger add let binding action
        const onAddLetBinding = context.metadata?.onAddLetBinding as (() => void) | undefined;
        onAddLetBinding?.();

        return {
          navigationPath: ['Let Bindings', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Add a new let binding',
      }
    ),

    createCommand(
      'letbindings-edit',
      'e',
      'Edit',
      (context) => {
        // Trigger edit let binding action
        const onEditLetBinding = context.metadata?.onEditLetBinding as (() => void) | undefined;
        onEditLetBinding?.();

        return {
          navigationPath: ['Let Bindings', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit selected let binding',
        isAvailable: (ctx) => {
          return ctx.metadata?.selectedLetBindingId != null;
        },
      }
    ),

    createCommand(
      'letbindings-delete',
      'd',
      'Delete',
      (context) => {
        // Trigger delete let binding action
        const onDeleteLetBinding = context.metadata?.onDeleteLetBinding as (() => void) | undefined;
        onDeleteLetBinding?.();

        return {
          navigationPath: [],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected let binding',
        isAvailable: (ctx) => {
          return ctx.metadata?.selectedLetBindingId != null;
        },
      }
    ),
  ];
}

/**
 * Create the root-level navigation commands
 */
export function createRootCommands(): Command[] {
  return [
    // Escape command - clear context or exit to navigation mode
    createEscapeCommand(),

    // Section navigation commands
    createSectionCommand(
      'nav-hypotheses',
      'h',
      'Hypotheses',
      'Hypotheses',
      {
        description: 'Navigate to hypotheses section',
        children: createHypothesesCommands(),
      }
    ),

    createSectionCommand(
      'nav-goals',
      'g',
      'Goals',
      'Goals',
      {
        description: 'Navigate to goals section',
        children: createGoalsCommands(),
      }
    ),

    createSectionCommand(
      'nav-letbindings',
      'l',
      'Let Bindings',
      'Let Bindings',
      {
        description: 'Navigate to let bindings section',
        children: createLetBindingsCommands(),
      }
    ),
  ];
}

/**
 * Build the complete application command tree
 */
export function createApplicationCommandTree(): CommandTree {
  const rootCommands = createRootCommands();
  return buildCommandTree(rootCommands);
}
