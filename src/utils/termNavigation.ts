/**
 * Term Navigation Utilities
 *
 * Provides focus path navigation for TTerm structures.
 * A TermFocusPath is a sequence of steps that navigate into a term.
 */

import { TTerm, prettyPrintLevelTermTT } from '../compiler/surface';

/**
 * A path into a TTerm structure.
 *
 * For Binder terms: 'name' (the binder's name), 'domain' (the type), 'body' (the body)
 *   - This treats binders as having 3 children: [name, domain, body]
 *   - For Let bindings: [name, domain (value), body]
 * For App terms: 'fn' or 'arg'
 * For Annot terms: 'term' or 'type'
 *
 * Note: 'name' is special - it's not a sub-term but rather the binder's name string.
 * Navigation to 'name' means we're editing the binder's name.
 */
export type TermFocusPath = ('name' | 'domain' | 'body' | 'fn' | 'arg' | 'term' | 'type')[];

/**
 * Get the sub-term at a given focus path.
 * Returns null if the path is invalid.
 *
 * Note: For 'name' paths, returns the parent binder (since name is not a sub-term).
 * Use isNamePath() to check if focused on a name.
 */
export function getTermAtPath(term: TTerm, path: TermFocusPath): TTerm | null {
  let current: TTerm = term;

  for (let i = 0; i < path.length; i++) {
    const step = path[i];

    if (current.tag === 'Binder') {
      if (step === 'name') {
        // 'name' is terminal - we're focused on this binder's name
        // Return the binder itself (the remaining path should be empty)
        if (i === path.length - 1) {
          return current;
        }
        // Can't navigate further from 'name'
        return null;
      } else if (step === 'domain') {
        if (current.domain === undefined) return null;
        current = current.domain;
      } else if (step === 'body') {
        current = current.body;
      } else {
        return null;
      }
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
 * Check if a path points to a binder's name (ends with 'name').
 */
export function isNamePath(path: TermFocusPath): boolean {
  return path.length > 0 && path[path.length - 1] === 'name';
}

/**
 * Get the binder that owns the name at the given path.
 * Returns null if the path doesn't point to a name.
 */
export function getBinderForNamePath(term: TTerm, path: TermFocusPath): TTerm | null {
  if (!isNamePath(path)) return null;
  // The binder is at the parent path (path without 'name')
  const parentPath = path.slice(0, -1);
  const parent = getTermAtPath(term, parentPath);
  if (parent && parent.tag === 'Binder') {
    return parent;
  }
  return null;
}

/**
 * Replace the sub-term at a given focus path with a new term.
 * Returns the updated root term, or null if the path is invalid.
 *
 * Note: Does NOT handle 'name' paths - use setNameAtPath for those.
 */
export function setTermAtPath(term: TTerm, path: TermFocusPath, newTerm: TTerm): TTerm | null {
  // Base case: empty path means replace the whole term
  if (path.length === 0) {
    return newTerm;
  }

  const [step, ...restPath] = path;

  // 'name' is not a sub-term, use setNameAtPath instead
  if (step === 'name') {
    return null;
  }

  if (term.tag === 'Binder') {
    if (step === 'domain') {
      if (term.domain === undefined) return null;
      const updatedSubTerm = setTermAtPath(term.domain, restPath as TermFocusPath, newTerm);
      if (updatedSubTerm === null) return null;
      return { ...term, domain: updatedSubTerm };
    } else if (step === 'body') {
      const updatedSubTerm = setTermAtPath(term.body, restPath as TermFocusPath, newTerm);
      if (updatedSubTerm === null) return null;
      return { ...term, body: updatedSubTerm };
    }
  }
  if (term.tag === 'App' && (step === 'fn' || step === 'arg')) {
    const updatedSubTerm = setTermAtPath(term[step], restPath as TermFocusPath, newTerm);
    if (updatedSubTerm === null) return null;

    return {
      ...term,
      [step]: updatedSubTerm
    };
  } else if (term.tag === 'Annot' && (step === 'term' || step === 'type')) {
    const updatedSubTerm = setTermAtPath(term[step], restPath as TermFocusPath, newTerm);
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
 * Set the name of a binder at the given path.
 * The path should end with 'name'.
 * Returns the updated root term, or null if invalid.
 */
export function setNameAtPath(term: TTerm, path: TermFocusPath, newName: string): TTerm | null {
  if (!isNamePath(path)) return null;

  // Get path to the binder (without 'name')
  const binderPath = path.slice(0, -1);

  if (binderPath.length === 0) {
    // Renaming the root term's name (if it's a binder)
    if (term.tag === 'Binder') {
      return { ...term, name: newName };
    }
    return null;
  }

  // Navigate to parent of the binder and update
  const parentPath = binderPath.slice(0, -1);
  const binderStep = binderPath[binderPath.length - 1];

  const parent = getTermAtPath(term, parentPath);
  if (!parent) return null;

  // Get the binder and update its name
  let binder: TTerm | null = null;
  if (parent.tag === 'Binder') {
    if (binderStep === 'domain') {
      binder = parent.domain ?? null;
    } else if (binderStep === 'body') {
      binder = parent.body;
    }
  } else if (parent.tag === 'App' && (binderStep === 'fn' || binderStep === 'arg')) {
    binder = parent[binderStep];
  } else if (parent.tag === 'Annot' && (binderStep === 'term' || binderStep === 'type')) {
    binder = parent[binderStep];
  }

  if (!binder || binder.tag !== 'Binder') return null;

  const updatedBinder = { ...binder, name: newName };
  return setTermAtPath(term, binderPath, updatedBinder);
}

// Helper to strip outer parentheses from a string
function stripOuterParens(s: string): string {
  if (s.startsWith('(') && s.endsWith(')')) {
    return s.slice(1, -1);
  }
  return s;
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
      return `Type_${prettyPrintLevelTermTT(term.level)}`;

    case 'ULit':
      return term.n.toString();

    case 'UOmega':
      return 'ω';

    case 'Binder':
      if (term.binderKind.tag === 'BPiTT') {
        // Collect all arrow parts: A -> B -> C -> D
        const parts: string[] = [];
        let current: TTerm = term;
        while (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
          const isAnonymous = current.name === '_' || current.name === '';
          // Pi binders always have domain
          const domain = stripOuterParens(prettyPrintTerm(current.domain!));
          if (isAnonymous) {
            parts.push(domain);
          } else {
            parts.push(`(${current.name} : ${domain})`);
          }
          current = current.body;
        }
        parts.push(prettyPrintTerm(current));
        return `(${parts.join(' -> ')})`;
      } else if (term.binderKind.tag === 'BLamTT') {
        // Lambda binders always have domain
        const domainStr = stripOuterParens(prettyPrintTerm(term.domain!));
        const bodyStr = prettyPrintTerm(term.body);
        return `λ(${term.name} : ${domainStr}). ${bodyStr}`;
      } else if (term.binderKind.tag === 'BLetTT') {
        const defValStr = prettyPrintTerm(term.binderKind.defVal);
        const bodyStr = prettyPrintTerm(term.body);
        if (term.domain !== undefined) {
          const domainStr = stripOuterParens(prettyPrintTerm(term.domain));
          return `let ${term.name} : ${domainStr} = ${defValStr} in ${bodyStr}`;
        }
        return `let ${term.name} = ${defValStr} in ${bodyStr}`;
      }
      return '?';

    case 'App': {
      // Collect all arguments from nested applications: ((f a) b) c -> [f, a, b, c]
      const parts: string[] = [];
      let current: TTerm = term;
      while (current.tag === 'App') {
        parts.unshift(prettyPrintTerm(current.arg));
        current = current.fn;
      }
      parts.unshift(prettyPrintTerm(current));
      return `(${parts.join(' ')})`;
    }

    case 'Const':
      return term.name;

    case 'Hole':
      return `?${term.id}`;

    case 'Annot': {
      const termStr = prettyPrintTerm(term.term);
      const typeStr = stripOuterParens(prettyPrintTerm(term.type));
      return `(${termStr} : ${typeStr})`;
    }

    case 'Match':
      const scrutineeStr = prettyPrintTerm(term.scrutinee);
      return `match ${scrutineeStr} (${term.clauses.length} clauses)`;

    case 'ULevel':
      return 'Level';

    case 'MultiBinder': {
      const domainStr = stripOuterParens(prettyPrintTerm(term.domain));
      const bodyStr = prettyPrintTerm(term.body);
      const namesStr = term.names.join(' ');
      if (term.binderKind.tag === 'BPiTT') {
        return `((${namesStr} : ${domainStr}) -> ${bodyStr})`;
      } else if (term.binderKind.tag === 'BLamTT') {
        return `λ(${namesStr} : ${domainStr}). ${bodyStr}`;
      } else {
        return `let ${namesStr} : ${domainStr} = ... in ${bodyStr}`;
      }
    }

    case 'AbsurdMarker':
      return '#absurd';

    case 'WithClause':
      return '#with';

    case 'TacticBlock':
      return '#tactics';

    case 'NatLit':
      return term.value.toString();
    case 'RatLit':
      return `${term.num}/${term.den}`;

    default: {
      const _never: never = term;
      throw new Error(`Unreachable code: ${_never}`);
    }
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
 *
 * For binders, the first child is 'name' (the binder's name).
 * Children order: name -> domain -> body
 */
export function navigateDown(term: TTerm, path: TermFocusPath): TermFocusPath | null {
  // Can't navigate down from a name
  if (isNamePath(path)) return null;

  const current = getTermAtPath(term, path);
  if (!current) return null;

  // For terms with children, go to the first child
  if (current.tag === 'Binder') {
    // First child of a binder is its name
    return [...path, 'name'];
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
 *
 * For binders, sibling order is: name -> domain -> body
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
    // Order: name -> domain -> body
    if (currentStep === 'name') nextStep = 'domain';
    else if (currentStep === 'domain') nextStep = 'body';
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
 *
 * For binders, sibling order is: name -> domain -> body
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
    // Order: name -> domain -> body (so reverse is body -> domain -> name)
    if (currentStep === 'body') prevStep = 'domain';
    else if (currentStep === 'domain') prevStep = 'name';
    // If at name, no previous sibling - go up
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
