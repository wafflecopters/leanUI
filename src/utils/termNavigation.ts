/**
 * Term Navigation Utilities
 *
 * Provides focus path navigation for TTerm structures.
 * A TermFocusPath is a sequence of steps that navigate into a term.
 */

import { TTerm } from '../types/tt-core';

/**
 * A path into a TTerm structure.
 * Each step is either 'domain' or 'body' for Binder terms,
 * 'fn' or 'arg' for App terms, or 'term' for Annot terms.
 */
export type TermFocusPath = ('domain' | 'body' | 'fn' | 'arg' | 'term' | 'type')[];

/**
 * Get the sub-term at a given focus path.
 * Returns null if the path is invalid.
 */
export function getTermAtPath(term: TTerm, path: TermFocusPath): TTerm | null {
  let current: TTerm = term;

  for (const step of path) {
    if (current.tag === 'Binder' && (step === 'domain' || step === 'body')) {
      current = current[step];
    } else if (current.tag === 'App' && (step === 'fn' || step === 'arg')) {
      current = current[step];
    } else if (current.tag === 'Annot' && (step === 'term' || step === 'type')) {
      current = current[step];
    } else {
      // Invalid path
      return null;
    }
  }

  return current;
}

/**
 * Replace the sub-term at a given focus path with a new term.
 * Returns the updated root term, or null if the path is invalid.
 */
export function setTermAtPath(term: TTerm, path: TermFocusPath, newTerm: TTerm): TTerm | null {
  // Base case: empty path means replace the whole term
  if (path.length === 0) {
    return newTerm;
  }

  const [step, ...restPath] = path;

  if (term.tag === 'Binder' && (step === 'domain' || step === 'body')) {
    const updatedSubTerm = setTermAtPath(term[step], restPath, newTerm);
    if (updatedSubTerm === null) return null;

    return {
      ...term,
      [step]: updatedSubTerm
    };
  } else if (term.tag === 'App' && (step === 'fn' || step === 'arg')) {
    const updatedSubTerm = setTermAtPath(term[step], restPath, newTerm);
    if (updatedSubTerm === null) return null;

    return {
      ...term,
      [step]: updatedSubTerm
    };
  } else if (term.tag === 'Annot' && (step === 'term' || step === 'type')) {
    const updatedSubTerm = setTermAtPath(term[step], restPath, newTerm);
    if (updatedSubTerm === null) return null;

    return {
      ...term,
      [step]: updatedSubTerm
    };
  }

  // Invalid path
  return null;
}

/**
 * Pretty-print a TTerm to a string.
 * Handles unnamed binders by omitting the name.
 */
export function prettyPrintTerm(term: TTerm): string {
  switch (term.tag) {
    case 'Var':
      return `@${term.index}`;

    case 'Sort':
      return `Type_${term.level}`;

    case 'Binder':
      if (term.binderKind.tag === 'BPi') {
        const domainStr = prettyPrintTerm(term.domain);
        const bodyStr = prettyPrintTerm(term.body);

        // If name is empty, just show "domain -> body"
        if (term.name === '') {
          return `${domainStr} -> ${bodyStr}`;
        }

        // Otherwise show "(name : domain) -> body"
        return `(${term.name} : ${domainStr}) -> ${bodyStr}`;
      } else if (term.binderKind.tag === 'BLam') {
        const bodyStr = prettyPrintTerm(term.body);
        return `λ${term.name}. ${bodyStr}`;
      } else if (term.binderKind.tag === 'BLet') {
        const defValStr = prettyPrintTerm(term.binderKind.defVal);
        const bodyStr = prettyPrintTerm(term.body);
        return `let ${term.name} := ${defValStr} in ${bodyStr}`;
      }
      return '?';

    case 'App':
      const fnStr = prettyPrintTerm(term.fn);
      const argStr = prettyPrintTerm(term.arg);
      return `(${fnStr} ${argStr})`;

    case 'Const':
      return term.name;

    case 'Hole':
      return `?${term.id}`;

    case 'Annot':
      const termStr = prettyPrintTerm(term.term);
      const typeStr = prettyPrintTerm(term.type);
      return `(${termStr} : ${typeStr})`;
  }
}

/**
 * Get the parent binder name for a given path.
 * Returns null if the path doesn't point into a binder, or if the parent is the root.
 */
export function getParentBinderName(term: TTerm, path: TermFocusPath): string | null {
  if (path.length === 0) return null;

  // Get the parent term
  const parentPath = path.slice(0, -1);
  const parent = getTermAtPath(term, parentPath);

  if (parent && parent.tag === 'Binder') {
    return parent.name;
  }

  return null;
}

/**
 * Update the parent binder's name.
 * Returns the updated root term, or null if invalid.
 */
export function setParentBinderName(term: TTerm, path: TermFocusPath, newName: string): TTerm | null {
  if (path.length === 0) return null;

  const parentPath = path.slice(0, -1);
  const parent = getTermAtPath(term, parentPath);

  if (parent && parent.tag === 'Binder') {
    const updatedParent = { ...parent, name: newName };
    return setTermAtPath(term, parentPath, updatedParent);
  }

  return null;
}

/**
 * Create a fresh hole ID based on a counter or timestamp.
 */
let holeCounter = 0;
export function freshHoleId(): string {
  return `hole_${holeCounter++}`;
}

/**
 * Check if the focused term is a "symbol" (Sort, Const, or Var) that can be edited.
 */
export function isSymbol(term: TTerm | null): boolean {
  if (!term) return false;
  return term.tag === 'Sort' || term.tag === 'Const' || term.tag === 'Var';
}

/**
 * Navigate up in the term tree (go to parent).
 * Returns the new focus path, or null if already at root.
 */
export function navigateUp(path: TermFocusPath): TermFocusPath | null {
  if (path.length === 0) return null;
  return path.slice(0, -1);
}

/**
 * Navigate down in the term tree (go to first child).
 * Returns the new focus path, or null if the term has no children.
 */
export function navigateDown(term: TTerm, path: TermFocusPath): TermFocusPath | null {
  const current = getTermAtPath(term, path);
  if (!current) return null;

  // For terms with children, go to the first child
  if (current.tag === 'Binder') {
    return [...path, 'domain'];
  } else if (current.tag === 'App') {
    return [...path, 'fn'];
  } else if (current.tag === 'Annot') {
    return [...path, 'term'];
  }

  // No children
  return null;
}

/**
 * Get the next sibling path, or go up if there's no next sibling.
 */
export function navigateRight(term: TTerm, path: TermFocusPath): TermFocusPath | null {
  if (path.length === 0) return null;

  const parentPath = path.slice(0, -1);
  const currentStep = path[path.length - 1];
  const parent = getTermAtPath(term, parentPath);

  if (!parent) return null;

  // Determine the next sibling based on parent type
  let nextStep: TermFocusPath[number] | null = null;

  if (parent.tag === 'Binder') {
    if (currentStep === 'domain') nextStep = 'body';
    // If at body, no next sibling - go up
  } else if (parent.tag === 'App') {
    if (currentStep === 'fn') nextStep = 'arg';
    // If at arg, no next sibling - go up
  } else if (parent.tag === 'Annot') {
    if (currentStep === 'term') nextStep = 'type';
    // If at type, no next sibling - go up
  }

  if (nextStep) {
    return [...parentPath, nextStep];
  }

  // No next sibling, go up
  return navigateUp(path);
}

/**
 * Get the previous sibling path, or go up if there's no previous sibling.
 */
export function navigateLeft(term: TTerm, path: TermFocusPath): TermFocusPath | null {
  if (path.length === 0) return null;

  const parentPath = path.slice(0, -1);
  const currentStep = path[path.length - 1];
  const parent = getTermAtPath(term, parentPath);

  if (!parent) return null;

  // Determine the previous sibling based on parent type
  let prevStep: TermFocusPath[number] | null = null;

  if (parent.tag === 'Binder') {
    if (currentStep === 'body') prevStep = 'domain';
    // If at domain, no previous sibling - go up
  } else if (parent.tag === 'App') {
    if (currentStep === 'arg') prevStep = 'fn';
    // If at fn, no previous sibling - go up
  } else if (parent.tag === 'Annot') {
    if (currentStep === 'type') prevStep = 'term';
    // If at term, no previous sibling - go up
  }

  if (prevStep) {
    return [...parentPath, prevStep];
  }

  // No previous sibling, go up
  return navigateUp(path);
}

/**
 * Check if the term at the given path is a Binder.
 */
export function isBinder(term: TTerm, path: TermFocusPath): boolean {
  const termAtPath = getTermAtPath(term, path);
  return termAtPath !== null && termAtPath.tag === 'Binder';
}

/**
 * Get the name of a binder at the given path, or null if not a binder.
 */
export function getBinderName(term: TTerm, path: TermFocusPath): string | null {
  const termAtPath = getTermAtPath(term, path);
  if (termAtPath === null || termAtPath.tag !== 'Binder') return null;
  return termAtPath.name;
}

/**
 * Rename the binder at the given path.
 * Since we use De Bruijn indices, we only need to update the name field on the Binder itself.
 * Returns the updated term, or null if the path doesn't point to a Binder.
 */
export function renameBinderAtPath(
  term: TTerm,
  path: TermFocusPath,
  newName: string
): TTerm | null {
  const termAtPath = getTermAtPath(term, path);
  if (termAtPath === null || termAtPath.tag !== 'Binder') return null;

  // Create a new binder with the updated name
  const renamedBinder: TTerm = {
    ...termAtPath,
    name: newName,
  };

  // Replace the binder at the path
  return setTermAtPath(term, path, renamedBinder);
}
