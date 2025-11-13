/**
 * Navigation Context
 *
 * Provides global keyboard navigation state and handlers.
 * This context manages:
 * - Current navigation path (breadcrumb)
 * - Input mode (navigation vs typing)
 * - Keyboard event handling
 * - Focus management across the application
 */

import React, { createContext, useContext, useState, useCallback, useEffect, useRef } from 'react';
import {
  NavigationState,
  initialNavigationState,
  CommandTree,
  Command,
  CommandContext,
  InputMode,
  NavigationUtils,
  NavigableSection,
} from '../types/commands';

interface NavigationContextValue {
  /** Current navigation state */
  state: NavigationState;

  /** Command tree for the application */
  commandTree: CommandTree | null;

  /** Set the command tree (typically done once at app initialization) */
  setCommandTree: (tree: CommandTree) => void;

  /** Navigate to a specific path */
  navigateTo: (path: string[]) => void;

  /** Clear navigation context (return to root) */
  clearNavigation: () => void;

  /** Set the input mode */
  setMode: (mode: InputMode) => void;

  /** Set the focused section ID */
  setFocusedSection: (sectionId: string | null) => void;

  /** Push a modal onto the stack */
  pushModal: (modalId: string) => void;

  /** Pop a modal from the stack */
  popModal: () => void;

  /** Update metadata */
  updateMetadata: (updates: Record<string, any>) => void;

  /** Execute a command by key */
  executeCommand: (key: string) => boolean;

  /** Register a ref for a focusable section */
  registerSection: (sectionId: string, ref: HTMLElement) => void;

  /** Unregister a section ref */
  unregisterSection: (sectionId: string) => void;

  /** Get available commands at current path */
  getAvailableCommands: () => Command[];

  /** Register a navigable section */
  registerNavigableSection: (section: NavigableSection) => void;

  /** Unregister a navigable section */
  unregisterNavigableSection: (sectionId: string) => void;

  /** Cycle to next/previous section */
  cycleSection: (direction: 'next' | 'prev') => void;
}

const NavigationContext = createContext<NavigationContextValue | null>(null);

export function useNavigation(): NavigationContextValue {
  const context = useContext(NavigationContext);
  if (!context) {
    throw new Error('useNavigation must be used within NavigationProvider');
  }
  return context;
}

interface NavigationProviderProps {
  children: React.ReactNode;
  /** Optional initial command tree */
  initialCommandTree?: CommandTree;
}

export function NavigationProvider({ children, initialCommandTree }: NavigationProviderProps) {
  const [state, setState] = useState<NavigationState>(initialNavigationState);
  const [commandTree, setCommandTree] = useState<CommandTree | null>(initialCommandTree || null);

  // Store refs to focusable sections for direct DOM manipulation
  const sectionRefs = useRef<Map<string, HTMLElement>>(new Map());

  // Store navigable sections with their metadata
  const navigableSections = useRef<Map<string, NavigableSection>>(new Map());

  // Navigate to a specific path
  const navigateTo = useCallback((path: string[]) => {
    setState(prev => ({
      ...prev,
      navigationPath: path,
    }));
  }, []);

  // Clear navigation (return to root)
  const clearNavigation = useCallback(() => {
    setState(prev => ({
      ...prev,
      navigationPath: [],
    }));
  }, []);

  // Set input mode
  const setMode = useCallback((mode: InputMode) => {
    setState(prev => ({
      ...prev,
      mode,
    }));
  }, []);

  // Set focused section
  const setFocusedSection = useCallback((sectionId: string | null) => {
    setState(prev => {
      // Only update if changed
      if (prev.focusedSectionId === sectionId) {
        return prev;
      }

      return {
        ...prev,
        focusedSectionId: sectionId,
      };
    });

    // Focus the section element if we have a ref
    if (sectionId) {
      const element = sectionRefs.current.get(sectionId);
      if (element && document.activeElement !== element) {
        // Use requestAnimationFrame to ensure DOM is ready
        requestAnimationFrame(() => {
          element.focus();
        });
      }
    }
  }, []);

  // Modal stack management
  const pushModal = useCallback((modalId: string) => {
    setState(prev => ({
      ...prev,
      modalStack: [...prev.modalStack, modalId],
    }));
  }, []);

  const popModal = useCallback(() => {
    setState(prev => ({
      ...prev,
      modalStack: prev.modalStack.slice(0, -1),
    }));
  }, []);

  // Update metadata
  const updateMetadata = useCallback((updates: Record<string, any>) => {
    setState(prev => ({
      ...prev,
      metadata: { ...prev.metadata, ...updates },
    }));
  }, []);

  // Register/unregister section refs
  const registerSection = useCallback((sectionId: string, ref: HTMLElement) => {
    sectionRefs.current.set(sectionId, ref);
  }, []);

  const unregisterSection = useCallback((sectionId: string) => {
    sectionRefs.current.delete(sectionId);
  }, []);

  // Register/unregister navigable sections
  const registerNavigableSection = useCallback((section: NavigableSection) => {
    navigableSections.current.set(section.id, section);
  }, []);

  const unregisterNavigableSection = useCallback((sectionId: string) => {
    navigableSections.current.delete(sectionId);
  }, []);

  // Cycle through sections with arrow keys
  const cycleSection = useCallback((direction: 'next' | 'prev') => {
    if (!commandTree) return;

    // If we're at root (empty path), there's nothing to cycle
    if (state.navigationPath.length === 0) return;

    // Get the parent path (all but the last element)
    const parentPath = state.navigationPath.slice(0, -1);

    // Get available commands at the parent level
    const siblingCommands = commandTree.getCommandsAtPath(parentPath);

    // Filter to only navigation commands (those that have a navigationPath result)
    const navigationCommands = siblingCommands.filter(cmd => {
      // A command is a navigation command if it typically sets navigationPath
      // We can identify these as section commands (those with children)
      return cmd.children && cmd.children.length > 0;
    });

    if (navigationCommands.length === 0) return;

    // Get the current leaf (last element of path)
    const currentLeaf = state.navigationPath[state.navigationPath.length - 1];

    // Find current command index
    const currentIndex = navigationCommands.findIndex(cmd => cmd.label === currentLeaf);

    // If we can't find the current command, don't cycle
    if (currentIndex === -1) return;

    // Calculate next index with wrapping
    let nextIndex: number;
    if (direction === 'next') {
      nextIndex = (currentIndex + 1) % navigationCommands.length;
    } else {
      nextIndex = (currentIndex - 1 + navigationCommands.length) % navigationCommands.length;
    }

    const nextCommand = navigationCommands[nextIndex];

    // Build the new path: parent path + new leaf
    const newPath = [...parentPath, nextCommand.label];
    navigateTo(newPath);
  }, [state, navigateTo, commandTree]);

  // Get available commands at current path
  const getAvailableCommands = useCallback((): Command[] => {
    if (!commandTree) return [];

    const commands = commandTree.getCommandsAtPath(state.navigationPath);

    // Filter by availability
    const context: CommandContext = {
      navigationPath: state.navigationPath,
      mode: state.mode,
      metadata: state.metadata,
    };

    return commands.filter(cmd => {
      if (!cmd.isAvailable) return true;
      return cmd.isAvailable(context);
    });
  }, [commandTree, state]);

  // Execute a command by key
  const executeCommand = useCallback((key: string): boolean => {
    if (!commandTree) return false;

    // Don't handle commands if we're in typing mode (unless it's Escape)
    if (state.mode === 'edit' && key !== 'Escape') {
      return false;
    }

    // If modal is open, only allow escape to close it
    if (state.modalStack.length > 0) {
      if (key === 'Escape') {
        popModal();
        return true;
      }
      return false;
    }

    const command = commandTree.findCommand(key, state.navigationPath);
    if (!command) {
      return false;
    }

    // Check availability
    const context: CommandContext = {
      navigationPath: state.navigationPath,
      mode: state.mode,
      metadata: state.metadata,
    };

    if (command.isAvailable && !command.isAvailable(context)) {
      return false;
    }

    // Execute command
    const result = command.execute(context);

    // Apply result
    if (result) {
      setState(prev => {
        const updates: Partial<NavigationState> = {};

        if (result.navigationPath !== undefined) {
          updates.navigationPath = result.navigationPath;
        }

        if (result.mode !== undefined) {
          updates.mode = result.mode;
        }

        return { ...prev, ...updates };
      });

      return result.preventDefault !== false; // Default to true
    }

    return true; // Default: prevent default behavior
  }, [commandTree, state, popModal]);

  // Global keyboard event handler
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      const target = e.target as HTMLElement;
      const isInInput = target.tagName === 'INPUT' || target.tagName === 'TEXTAREA' || target.isContentEditable;

      // Handle Escape key - special behavior based on context
      if (e.key === 'Escape') {
        if (isInInput) {
          // If in an input field, blur it and return to navigate mode
          target.blur();
          setMode('navigate');
          e.preventDefault();
          e.stopPropagation();
          return;
        }

        // In navigate mode, Escape clears to root
        if (state.mode === 'navigate') {
          if (state.navigationPath.length > 0) {
            // Clear to root
            navigateTo(NavigationUtils.clearPath());
            e.preventDefault();
            e.stopPropagation();
            return;
          }
        }
      }

      // Don't handle other keys if user is typing
      if (isInInput && e.key !== 'Escape') {
        return;
      }

      // Only handle special keys in navigate mode
      if (state.mode === 'navigate') {
        // Backspace/Delete - pop one level
        if (e.key === 'Backspace' || e.key === 'Delete') {
          if (state.navigationPath.length > 0) {
            navigateTo(NavigationUtils.popPath(state.navigationPath));
            e.preventDefault();
            e.stopPropagation();
            return;
          }
        }

        // Arrow keys - cycle through sibling sections at current level
        if (e.key === 'ArrowRight' || e.key === 'ArrowDown') {
          cycleSection('next');
          e.preventDefault();
          e.stopPropagation();
          return;
        }
        if (e.key === 'ArrowLeft' || e.key === 'ArrowUp') {
          cycleSection('prev');
          e.preventDefault();
          e.stopPropagation();
          return;
        }
      }

      // Try to execute command
      const handled = executeCommand(e.key);

      if (handled) {
        e.preventDefault();
        e.stopPropagation();
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [executeCommand, state, navigateTo, setMode, cycleSection]);

  // Update focused section when navigation path changes
  useEffect(() => {
    if (state.navigationPath.length > 0) {
      // Get the section ID from the last segment of the path
      const sectionId = state.navigationPath[0].toLowerCase();
      setFocusedSection(sectionId);
    } else {
      setFocusedSection(null);
    }
  }, [state.navigationPath, setFocusedSection]);

  const value: NavigationContextValue = {
    state,
    commandTree,
    setCommandTree,
    navigateTo,
    clearNavigation,
    setMode,
    setFocusedSection,
    pushModal,
    popModal,
    updateMetadata,
    executeCommand,
    registerSection,
    unregisterSection,
    getAvailableCommands,
    registerNavigableSection,
    unregisterNavigableSection,
    cycleSection,
  };

  return (
    <NavigationContext.Provider value={value}>
      {children}
    </NavigationContext.Provider>
  );
}

/**
 * Hook to make a section focusable via keyboard navigation
 */
export function useFocusableSection(sectionId: string, label: string, order: number) {
  const { state, registerSection, unregisterSection, registerNavigableSection, unregisterNavigableSection } = useNavigation();
  const ref = useRef<HTMLDivElement>(null);

  const isFocused = state.focusedSectionId === sectionId;

  useEffect(() => {
    if (ref.current) {
      registerSection(sectionId, ref.current);
    }

    // Register as navigable section
    registerNavigableSection({ id: sectionId, label, order });

    return () => {
      unregisterSection(sectionId);
      unregisterNavigableSection(sectionId);
    };
  }, [sectionId, label, order, registerSection, unregisterSection, registerNavigableSection, unregisterNavigableSection]);

  return {
    ref,
    isFocused,
    tabIndex: -1, // Make focusable but not in tab order
  };
}
