/**
 * Keyboard Navigation Command System
 *
 * This module provides a robust, hierarchical command system for keyboard navigation.
 * Commands form a tree structure where each command can have child commands,
 * creating navigation contexts (e.g., "Goals" -> "Editor").
 *
 * NO MODES! Navigation is just a path through the tree. If you're at an editable
 * leaf (like a text input), that's just part of the navigation, not a separate "mode".
 */

/**
 * Represents a keyboard shortcut key
 */
export type CommandKey = string; // e.g., 'h', 'g', 'l', 'e', 's', 'r', 'Escape'

/**
 * Context passed to command handlers
 */
export interface CommandContext {
  /** Current navigation path (breadcrumb) */
  navigationPath: string[];
  /** Additional metadata that can be passed to commands */
  metadata?: Record<string, any>;
}

/**
 * Result of executing a command
 */
export interface CommandResult {
  /** Whether to change the navigation path */
  navigationPath?: string[];
  /** Whether to prevent default browser behavior */
  preventDefault?: boolean;
  /** Whether to stop event propagation */
  stopPropagation?: boolean;
  /** Number of levels escape should pop (for command chains like 're') */
  escapeLevels?: number;
}

/**
 * A command that can be executed via keyboard
 */
export interface Command {
  /** Unique identifier for this command */
  id: string;

  /** Keyboard key that triggers this command */
  key: CommandKey;

  /** Human-readable label for display */
  label: string;

  /** Optional description for help/documentation */
  description?: string;

  /**
   * Execute the command
   * @returns CommandResult or void (void treated as { preventDefault: true })
   */
  execute: (context: CommandContext) => CommandResult | void;

  /**
   * Check if command is available in current context
   * @returns true if command should be shown/enabled
   */
  isAvailable?: (context: CommandContext) => boolean;

  /**
   * Child commands available after this command is executed
   * This creates hierarchical navigation (e.g., Goals -> Edit)
   */
  children?: Command[];

  /**
   * Whether this command should exit to parent context
   * Used for "back" or "cancel" operations
   */
  exitToParent?: boolean;

  /**
   * Number of levels to pop on escape (default: 1)
   * Useful for command chains like 're' where escape should pop both 'r' and 'e'
   */
  escapeLevels?: number;
}

/**
 * A dynamic command whose children or availability changes based on runtime state
 * This is useful for commands that depend on data (e.g., list of hypotheses)
 */
export interface DynamicCommand extends Omit<Command, 'children'> {
  /**
   * Generate child commands dynamically based on current context
   */
  getChildren?: (context: CommandContext) => Command[];
}

/**
 * Command tree root - represents all available commands at the root level
 */
export interface CommandTree {
  /** Root-level commands (available when navigationPath is empty) */
  root: Command[];

  /**
   * Get commands available at a specific navigation path
   */
  getCommandsAtPath: (path: string[]) => Command[];

  /**
   * Find a command by key at a specific path
   */
  findCommand: (key: string, path: string[]) => Command | undefined;
}

/**
 * Helper to create a simple command
 */
export function createCommand(
  id: string,
  key: CommandKey,
  label: string,
  execute: (context: CommandContext) => CommandResult | void,
  options?: {
    description?: string;
    isAvailable?: (context: CommandContext) => boolean;
    children?: Command[];
    exitToParent?: boolean;
  }
): Command {
  return {
    id,
    key,
    label,
    execute,
    ...options,
  };
}

/**
 * Helper to create a command that navigates to a section
 */
export function createSectionCommand(
  id: string,
  key: CommandKey,
  label: string,
  sectionName: string,
  options?: {
    description?: string;
    children?: Command[];
    onNavigate?: (context: CommandContext) => void;
  }
): Command {
  return createCommand(
    id,
    key,
    label,
    (context) => {
      options?.onNavigate?.(context);
      return {
        navigationPath: [sectionName],
        preventDefault: true,
      };
    },
    {
      description: options?.description || `Navigate to ${label}`,
      children: options?.children,
    }
  );
}

/**
 * Helper to create the default Escape command behavior
 * - Pop one level from navigation path
 * - If at root: does nothing
 */
export function createEscapeCommand(): Command {
  return createCommand(
    'escape',
    'Escape',
    'Go Back',
    (context) => {
      // Pop one level from the path
      if (context.navigationPath.length > 0) {
        return {
          navigationPath: context.navigationPath.slice(0, -1),
          preventDefault: true,
        };
      }
      // Already at root, do nothing
      return {
        preventDefault: true,
      };
    },
    {
      description: 'Go back one level in navigation',
    }
  );
}

/**
 * Build a command tree from root commands
 */
export function buildCommandTree(rootCommands: Command[]): CommandTree {
  const getCommandsAtPath = (path: string[]): Command[] => {
    if (path.length === 0) {
      return rootCommands;
    }

    let currentCommands = rootCommands;

    for (const segment of path) {
      // Skip numeric segments - these represent selections, not command nodes
      if (/^\d+$/.test(segment)) {
        continue;
      }

      const command = currentCommands.find(cmd => cmd.label === segment);
      if (!command || !command.children) {
        return [];
      }
      currentCommands = command.children;
    }

    return currentCommands;
  };

  const findCommand = (key: string, path: string[]): Command | undefined => {
    const commands = getCommandsAtPath(path);
    return commands.find(cmd => cmd.key.toLowerCase() === key.toLowerCase());
  };

  return {
    root: rootCommands,
    getCommandsAtPath,
    findCommand,
  };
}

/**
 * Navigation state
 */
export interface NavigationState {
  /** Current navigation path (breadcrumb trail) */
  navigationPath: string[];

  /** Escape levels stack - tracks how many levels each path segment should pop */
  escapeLevelsStack: number[];

  /** Currently focused section/element ID */
  focusedSectionId: string | null;

  /** Modal stack (for handling modals in navigation) */
  modalStack: string[];

  /** Additional metadata */
  metadata: Record<string, any>;
}

/**
 * Initial navigation state
 */
export const initialNavigationState: NavigationState = {
  navigationPath: [],
  escapeLevelsStack: [],
  focusedSectionId: null,
  modalStack: [],
  metadata: {},
};

/**
 * Editor controller interface for managing edit mode
 */
export interface EditorController {
  /** Whether the editor is currently open */
  isOpen: boolean;
  /** Submit the editor and close */
  submit: () => void;
  /** Cancel editing and close */
  cancel: () => void;
  /** Focus the editor input */
  focus: () => void;
}

/**
 * Section metadata for navigation
 */
export interface NavigableSection {
  id: string;
  label: string;
  /** Order index for arrow key navigation */
  order: number;
}

/**
 * Navigation utilities
 */
export const NavigationUtils = {
  /**
   * Pop the last segment from a path
   */
  popPath: (path: string[]): string[] => {
    return path.slice(0, -1);
  },

  /**
   * Clear path to root
   */
  clearPath: (): string[] => {
    return [];
  },

  /**
   * Build breadcrumb display text
   */
  buildBreadcrumb: (path: string[]): string => {
    return path.length > 0 ? `Root > ${path.join(' > ')}` : 'Root';
  },

  /**
   * Check if we're at root
   */
  isAtRoot: (path: string[]): boolean => {
    return path.length === 0;
  },

  /**
   * Pop levels from path using escape levels stack
   * Returns new path and new escape levels stack
   */
  popLevelsWithStack: (path: string[], escapeLevelsStack: number[]): [string[], number[]] => {
    if (path.length === 0) return [path, escapeLevelsStack];

    // Get the escape level for the current segment
    const currentEscapeLevel = escapeLevelsStack[escapeLevelsStack.length - 1] || 1;

    // Pop that many levels
    const levelsToPop = Math.min(currentEscapeLevel, path.length);
    const newPath = path.slice(0, -levelsToPop);
    const newStack = escapeLevelsStack.slice(0, -levelsToPop);

    return [newPath, newStack];
  },
};
