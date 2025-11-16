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
      () => {
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
      () => {
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
      'r',
      'Remove',
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
        description: 'Remove the current goal',
      }
    ),
  ];
}

/**
 * Create commands for the Hypotheses section
 */
function createHypothesesCommands(): Command[] {
  return [
    createCommand(
      'hypotheses-add',
      'a',
      'Add',
      () => {
        return {
          navigationPath: ['Hypotheses', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Add a new hypothesis',
      }
    ),

    createCommand(
      'hypotheses-edit',
      'e',
      'Edit',
      () => {
        return {
          navigationPath: ['Hypotheses', 'Editor'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit selected hypothesis',
        isAvailable: (ctx) => {
          // Only available if a hypothesis is selected
          return ctx.metadata?.selectedHypothesisId != null;
        },
      }
    ),

    createCommand(
      'hypotheses-delete',
      'd',
      'Delete',
      (context) => {
        // Trigger delete hypothesis action
        const onDeleteHypothesis = context.metadata?.onDeleteHypothesis as (() => void) | undefined;
        onDeleteHypothesis?.();

        return {
          navigationPath: [],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected hypothesis',
        isAvailable: (ctx) => {
          // Only available if a hypothesis is selected
          return ctx.metadata?.selectedHypothesisId != null;
        },
      }
    ),

    // TODO: Add navigation between hypotheses (j/k for down/up)
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
      () => {
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
      () => {
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
