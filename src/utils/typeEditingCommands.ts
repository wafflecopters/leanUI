/**
 * Reusable Type Editing Commands
 *
 * These commands work with any type expression editor through a standardized
 * TypeEditingContext interface. This allows the same commands to be used for:
 * - Inductive type signatures
 * - Constructor type signatures
 * - Hypothesis types
 * - Let binding types
 * - etc.
 */

import { Command, createCommand, CommandContext } from '../types/commands';
import { TTerm, mkType, mkPi, mkHole } from '../types/tt-core';
import {
  TermFocusPath,
  getTermAtPath,
  setTermAtPath,
  freshHoleId,
  navigateUp,
  navigateDown,
  navigateLeft,
  navigateRight,
} from './termNavigation';

/**
 * Standardized context for type editing.
 * Any component that wants to use the shared type editing commands
 * should populate these fields in navigation metadata.
 */
export interface TypeEditingContext {
  /** The current type term being edited */
  term: TTerm;
  /** Current focus path within the term */
  focusPath: TermFocusPath;
  /** Setter for the term */
  setTerm: (t: TTerm) => void;
  /** Setter for the focus path */
  setFocusPath: (p: TermFocusPath) => void;
  /** Navigation path to return to after actions complete (the "Type" editing state) */
  returnPath: string[];
}

/** Standard metadata keys for TypeEditingContext */
export const TYPE_EDITING_KEYS = {
  term: 'typeEditing.term',
  focusPath: 'typeEditing.focusPath',
  setTerm: 'typeEditing.setTerm',
  setFocusPath: 'typeEditing.setFocusPath',
  returnPath: 'typeEditing.returnPath',
} as const;

/**
 * Extract TypeEditingContext from command context metadata.
 * Returns null if required fields are missing.
 */
function getTypeEditingContext(context: CommandContext): TypeEditingContext | null {
  const term = context.metadata?.[TYPE_EDITING_KEYS.term] as TTerm | undefined;
  const focusPath = context.metadata?.[TYPE_EDITING_KEYS.focusPath] as TermFocusPath | undefined;
  const setTerm = context.metadata?.[TYPE_EDITING_KEYS.setTerm] as ((t: TTerm) => void) | undefined;
  const setFocusPath = context.metadata?.[TYPE_EDITING_KEYS.setFocusPath] as ((p: TermFocusPath) => void) | undefined;
  const returnPath = context.metadata?.[TYPE_EDITING_KEYS.returnPath] as string[] | undefined;

  if (!term || focusPath === undefined || !setTerm || !setFocusPath || !returnPath) {
    return null;
  }

  return { term, focusPath, setTerm, setFocusPath, returnPath };
}

/**
 * Create the standard set of type editing commands.
 * These commands read from TypeEditingContext in metadata.
 */
export function createTypeEditingCommands(): Command[] {
  return [
    // Arrow key navigation
    createCommand(
      'type-nav-up',
      'ArrowUp',
      '↑',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };

        const newPath = navigateUp(ctx.focusPath);
        if (newPath !== null) {
          ctx.setFocusPath(newPath);
        }

        return { navigationPath: ctx.returnPath, preventDefault: true };
      },
      { description: 'Navigate up to parent' }
    ),

    createCommand(
      'type-nav-down',
      'ArrowDown',
      '↓',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };

        const newPath = navigateDown(ctx.term, ctx.focusPath);
        if (newPath !== null) {
          ctx.setFocusPath(newPath);
        }

        return { navigationPath: ctx.returnPath, preventDefault: true };
      },
      { description: 'Navigate down to first child' }
    ),

    createCommand(
      'type-nav-left',
      'ArrowLeft',
      '←',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };

        const newPath = navigateLeft(ctx.term, ctx.focusPath);
        if (newPath !== null) {
          ctx.setFocusPath(newPath);
        }

        return { navigationPath: ctx.returnPath, preventDefault: true };
      },
      { description: 'Navigate to previous sibling' }
    ),

    createCommand(
      'type-nav-right',
      'ArrowRight',
      '→',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };

        const newPath = navigateRight(ctx.term, ctx.focusPath);
        if (newPath !== null) {
          ctx.setFocusPath(newPath);
        }

        return { navigationPath: ctx.returnPath, preventDefault: true };
      },
      { description: 'Navigate to next sibling' }
    ),

    // 'w' - Wrap menu
    createCommand(
      'type-wrap',
      'w',
      'Wrap',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };
        // Navigate to Wrap submenu
        return { navigationPath: [...ctx.returnPath, 'Wrap'], preventDefault: true };
      },
      {
        description: 'Wrap current term',
        transient: true,
        children: [
          createCommand(
            'type-wrap-arg',
            'a',
            'Arg (Pi)',
            (context) => {
              const ctx = getTypeEditingContext(context);
              if (!ctx) return { preventDefault: true };

              const focusedTerm = getTermAtPath(ctx.term, ctx.focusPath);
              if (!focusedTerm) return { preventDefault: true };

              const holeId = freshHoleId();
              const hole = mkHole(holeId, mkType(0), []);
              const newPi = mkPi(hole, focusedTerm, '');

              const newTerm = setTermAtPath(ctx.term, ctx.focusPath, newPi);
              if (!newTerm) return { preventDefault: true };

              ctx.setTerm(newTerm);
              ctx.setFocusPath([...ctx.focusPath, 'domain']);

              return { navigationPath: ctx.returnPath, preventDefault: true };
            },
            { description: 'Wrap as Pi argument (?hole -> current)' }
          ),
        ],
      }
    ),

    // 't' - Replace with Type_0
    createCommand(
      'type-replace-type0',
      't',
      'Type_0',
      (context) => {
        const ctx = getTypeEditingContext(context);
        if (!ctx) return { preventDefault: true };

        const newTerm = setTermAtPath(ctx.term, ctx.focusPath, mkType(0));
        if (!newTerm) return { preventDefault: true };

        ctx.setTerm(newTerm);

        return { navigationPath: ctx.returnPath, preventDefault: true };
      },
      { description: 'Replace current term with Type_0' }
    ),
  ];
}
