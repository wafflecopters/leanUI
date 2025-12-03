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

  /** Set the focused section ID (DEPRECATED - focusedSectionId is now derived from navigationPath) */
  setFocusedSection?: (sectionId: string | null) => void;

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

  // DERIVED: Compute focusedSectionId directly from navigationPath
  const focusedSectionId = state.navigationPath.length > 0
    ? state.navigationPath[0].toLowerCase()
    : null;

  // Navigate to a specific path
  const navigateTo = useCallback((path: string[]) => {
    setState(prev => ({
      ...prev,
      navigationPath: path,
      // Prune transient indices that are no longer valid for the new path
      transientSegmentIndices: NavigationUtils.pruneTransientIndices(prev.transientSegmentIndices, path.length),
    }));
  }, []);

  // Clear navigation (return to root)
  const clearNavigation = useCallback(() => {
    setState(prev => ({
      ...prev,
      navigationPath: [],
    }));
  }, []);

  // Note: focusedSectionId is now derived from navigationPath (see line 100-102)
  // No need for setFocusedSection or useEffect to sync it!

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
        let newPath: string[];
        let newTransientIndices = new Set(prev.transientSegmentIndices);

        if (result.navigationPath !== undefined) {
          // Command explicitly set the navigation path
          newPath = result.navigationPath;

          // If command navigated to a shorter or different path, prune transient indices
          newTransientIndices = NavigationUtils.pruneTransientIndices(newTransientIndices, newPath.length);

          // If this command is transient AND it's navigating deeper (adding a segment),
          // mark the new segment as transient
          if (command.transient && newPath.length > prev.navigationPath.length) {
            // The last segment of the new path is the transient menu
            newTransientIndices.add(newPath.length - 1);
          }

          // If the command was a child of a transient segment and is an "action" (sets explicit path),
          // we should pop through transient segments to return to the base path
          if (!command.transient && !command.children?.length) {
            // This is a leaf command (action) - compute base path after action
            const basePath = NavigationUtils.getBasePathAfterAction(prev.navigationPath, prev.transientSegmentIndices);

            // If the command set a relative path (same base), use base path instead
            // This handles the case where 'wa' sets navigationPath: ['Type'] but should pop 'Wrap'
            if (newPath.length > 0 && basePath.length > 0) {
              // Check if result path starts with the base path
              const resultStartsWithBase = basePath.every((seg, i) => newPath[i] === seg);
              if (resultStartsWithBase) {
                // Command returned to a valid base - clear transient indices below new path
                newTransientIndices = NavigationUtils.pruneTransientIndices(newTransientIndices, newPath.length);
              }
            }
          }
        } else if (command.children && command.children.length > 0) {
          // Auto-navigate into children if command has children but didn't specify a path
          // This prevents the common bug of forgetting to return navigationPath for menu commands
          newPath = [...prev.navigationPath, command.label];

          // If this command is transient, mark the new segment as transient
          if (command.transient) {
            newTransientIndices.add(newPath.length - 1);
          }
        } else {
          // No path change
          newPath = prev.navigationPath;
        }

        return {
          ...prev,
          navigationPath: newPath,
          transientSegmentIndices: newTransientIndices,
        };
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

      // Handle Escape key - pop one level in navigation path
      // If the current segment is transient, keep popping until we hit a non-transient segment
      if (e.key === 'Escape') {
        if (state.navigationPath.length > 0) {
          // Compute path after popping through any trailing transient segments
          const basePath = NavigationUtils.getBasePathAfterAction(
            state.navigationPath,
            state.transientSegmentIndices
          );

          // If we're in a transient segment, pop to base path
          // Otherwise, just pop one level from base path
          let newPath: string[];
          if (basePath.length < state.navigationPath.length) {
            // We're in transient segments - go back to base path
            newPath = basePath;
          } else {
            // Normal case - pop one level
            newPath = NavigationUtils.popPath(state.navigationPath);
          }

          navigateTo(newPath);
          if (isInInput) {
            target.blur(); // Also blur the input
          }
          e.preventDefault();
          e.stopPropagation();
          return;
        }
      }

      // Don't handle other keys if user is typing
      if (isInInput && e.key !== 'Escape') {
        return;
      }

      // Backspace/Delete - also pops levels (same as Escape, respects transient segments)
      if (e.key === 'Backspace' || e.key === 'Delete') {
        if (state.navigationPath.length > 0) {
          const basePath = NavigationUtils.getBasePathAfterAction(
            state.navigationPath,
            state.transientSegmentIndices
          );

          let newPath: string[];
          if (basePath.length < state.navigationPath.length) {
            newPath = basePath;
          } else {
            newPath = NavigationUtils.popPath(state.navigationPath);
          }

          navigateTo(newPath);
          e.preventDefault();
          e.stopPropagation();
          return;
        }
      }

      // Try to execute command first (including arrow keys if commands exist for them)
      const handled = executeCommand(e.key);

      if (handled) {
        e.preventDefault();
        e.stopPropagation();
        return;
      }

      // Arrow keys fallback - cycle through sibling sections at current level
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
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [executeCommand, state, navigateTo, cycleSection]);

  // Create enhanced state with derived focusedSectionId
  const enhancedState = {
    ...state,
    focusedSectionId,
  };

  const value: NavigationContextValue = {
    state: enhancedState,
    commandTree,
    setCommandTree,
    navigateTo,
    clearNavigation,
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
