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
import { PROOF_WORKSPACE_KEYS } from '../utils/proofWorkspaceSelection';

/**
 * Create commands for the Goals section
 */
function createGoalsCommands(): Command[] {
  return [
    createCommand(
      'goals-edit',
      'e',
      'Edit',
      () => ({
        navigationPath: ['Goals', 'Editor'],
        preventDefault: true,
      }),
      {
        description: 'Edit the current goal',
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
      () => ({
        navigationPath: ['Hypotheses', 'Editor'],
        preventDefault: true,
      }),
      {
        description: 'Add a new hypothesis',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisId] == null,
      }
    ),

    // Edit name (only when hypothesis selected) - INLINE
    createCommand(
      'hypotheses-edit-name',
      'n',
      'Name',
      (context) => {
        const index = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisIndex] as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        return {
          navigationPath: ['Hypotheses', String(index), 'EditName'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis name',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisId] != null,
      }
    ),

    // Edit expression (only when hypothesis selected) - INLINE
    createCommand(
      'hypotheses-edit-expr',
      'e',
      'Edit',
      (context) => {
        const index = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisIndex] as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };

        return {
          navigationPath: ['Hypotheses', String(index), 'EditExpression'],
          preventDefault: true,
        };
      },
      {
        description: 'Edit hypothesis expression',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisId] != null,
      }
    ),

    // Delete - safety checks live in the workspace handler itself
    createCommand(
      'hypotheses-delete',
      'd',
      'Delete',
      (context) => {
        const selectedId = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisId] as string | null | undefined;
        const onDeleteHypothesis = context.metadata?.[PROOF_WORKSPACE_KEYS.onDeleteHypothesis] as ((id: string) => void) | undefined;
        const index = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisIndex] as number | undefined;
        if (index == null) return { navigationPath: context.navigationPath, preventDefault: true };
        if (selectedId && onDeleteHypothesis) {
          onDeleteHypothesis(selectedId);
        }
        return {
          navigationPath: ['Hypotheses'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected hypothesis',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedHypothesisId] != null,
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
      () => ({
        navigationPath: ['Let Bindings', 'Editor'],
        preventDefault: true,
      }),
      {
        description: 'Add a new let binding',
      }
    ),

    createCommand(
      'letbindings-edit',
      'e',
      'Edit',
      (context) => {
        const selectedId = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedLetBindingId] as string | null | undefined;
        const selectedIndex = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedLetBindingIndex] as number | undefined;
        const onEditLetBinding = context.metadata?.[PROOF_WORKSPACE_KEYS.onEditLetBinding] as ((id: string) => void) | undefined;
        if (selectedId && onEditLetBinding) {
          onEditLetBinding(selectedId);
        }

        return {
          navigationPath: selectedIndex == null
            ? context.navigationPath
            : ['Let Bindings', String(selectedIndex)],
          preventDefault: true,
        };
      },
      {
        description: 'Edit selected let binding',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedLetBindingId] != null,
      }
    ),

    createCommand(
      'letbindings-delete',
      'd',
      'Delete',
      (context) => {
        const selectedId = context.metadata?.[PROOF_WORKSPACE_KEYS.selectedLetBindingId] as string | null | undefined;
        const onDeleteLetBinding = context.metadata?.[PROOF_WORKSPACE_KEYS.onDeleteLetBinding] as ((id: string) => void) | undefined;
        if (selectedId && onDeleteLetBinding) {
          onDeleteLetBinding(selectedId);
        }

        return {
          navigationPath: ['Let Bindings'],
          preventDefault: true,
        };
      },
      {
        description: 'Delete selected let binding',
        isAvailable: (ctx) => ctx.metadata?.[PROOF_WORKSPACE_KEYS.selectedLetBindingId] != null,
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
