/**
 * Fill in real constructor names + parameter names on a proof tree's induction
 * cases, using the goal states Lean reported.
 *
 * When the editor first applies `induction n`, it has no way to know the
 * inductive type's constructors, so it prints a bare `induction n` + `·` bullets
 * and Lean auto-generates INACCESSIBLE hypothesis names (rendered with a `✝`
 * dagger, e.g. `a✝`, `a_ih✝`). After one round-trip we DO know — the goal map
 * carries each case's Lean case name (`zero`/`succ`) and the hypotheses that
 * case introduced. Baking those into the case nodes makes the printer emit the
 * named form `induction n with | zero => … | succ a ih => …`, so Lean binds
 * accessible, dagger-free names.
 *
 * Only bullet-cases (no constructor name yet) are enriched; once a case is named
 * it is left alone, so this converges in a single pass and never oscillates.
 */
import { type ProofNode, type CaseNode, type ProofNodeId, splitCaseParams } from '../proof-tree/proof-tree';
import type { NodeGoalInfo } from '../proof-tree/goal-types';

/** Lean's inaccessible-name marker (LATIN CROSS, U+271D). */
const DAGGER = '✝';

/** Labels that mean "no name yet", written by whichever path made the case:
 *  `?` from a bare `cases x`, the literal `case` from a `·` bullet. Both read
 *  as a name in the prose — "Case (case):" — until Lean supplies the real one. */
function isPlaceholderLabel(label: string): boolean {
  const t = label.trim();
  return t === '' || t === '?' || t === 'case';
}

/** A valid Lean constructor identifier (letters/digits/_/., not a display label). */
function isLeanCtorName(name: string | undefined): name is string {
  return name !== undefined && /^[A-Za-z_][A-Za-z0-9_.]*$/.test(name);
}

/** Strip the inaccessible dagger (and any superscript after it) from a hyp name. */
function cleanHypName(n: string): string {
  return n.split(DAGGER)[0];
}

/** Make names unique — against each other (a cleaned `a✝`/`a✝¹` could both
 *  become `a`) AND against `taken` (hypotheses already in scope): a cleaned
 *  name that shadows an existing hypothesis strands every later reference to
 *  it (the second `cases` on a DPair would hide the first pair's `fst`). */
function uniquify(names: string[], taken: ReadonlySet<string> = new Set()): string[] {
  const used = new Set(taken);
  return names.map((n) => {
    if (!used.has(n)) {
      used.add(n);
      return n;
    }
    let i = 1;
    while (used.has(`${n}${i}`)) i++;
    used.add(`${n}${i}`);
    return `${n}${i}`;
  });
}

/**
 * Return a copy of `root` with induction case nodes' constructor names + param
 * names filled from `goalMap`, plus whether anything changed. Pure; `goalMap` is
 * read-only.
 */
export function enrichInductionCaseNames(
  root: ProofNode,
  goalMap: Map<ProofNodeId, NodeGoalInfo>,
): { root: ProofNode; changed: boolean } {
  let changed = false;

  const enrichCase = (c: CaseNode, parentHypNames: Set<string>): CaseNode => {
    const body = walk(c.body);
    // Already named (e.g. re-seeded from a `with` block) → leave constructor
    // metadata alone, only recurse into the body.
    if (isLeanCtorName(c.constructorName)) {
      return body === c.body ? c : { ...c, body };
    }
    // The case's own goal, or — when the case has no line of its own — the goal
    // at the head of its BODY, which is the same goal. A LONE unnamed case
    // prints as a plain continuation rather than a `·` bullet (a bullet focuses
    // one goal, which hides the others from validation), so it contributes no
    // source range and Lean reports nothing at it. Without this fallback such a
    // case is never enriched: `cases fProof` on a one-constructor structure kept
    // the placeholder label and left its fields as inaccessible `fst✝`/`snd✝`,
    // which the user cannot refer to.
    const info = goalMap.get(c.id) ?? goalMap.get(c.body.id);
    // Lean COMPOSES case tags when goals nest: `cases hF` inside a goal already
    // tagged `eps_delta` (a `constructor` on Limit) reports `eps_delta.mk`. A
    // `with |` alternative must be the constructor's OWN tag — Lean rejects the
    // composed form ("Invalid alternative name `eps_delta.mk`: Expected `mk`")
    // — so keep only the last component.
    const fullTag = info?.caseLabelLatex;
    const ctorName = isLeanCtorName(fullTag) ? fullTag.split('.').pop() : undefined;
    if (!isLeanCtorName(ctorName)) {
      return body === c.body ? c : { ...c, body };
    }
    // Hypotheses this case introduced that the induction's incoming goal didn't
    // have = the constructor's args + the induction hypotheses. Split them so the
    // label shows only the args (`succ a`), not the IH (`succ (a, a_ih)`).
    const caseHyps = info?.hypotheses ?? [];
    const introduced = uniquify(
      caseHyps.filter((h) => !parentHypNames.has(h.name)).map((h) => cleanHypName(h.name)),
      parentHypNames,
    );
    const { args, ihNames } = splitCaseParams(introduced);
    changed = true;
    return {
      ...c,
      body,
      constructorName: ctorName,
      constructorParamNames: args,
      // The DISPLAY label too, not just the printed alternative: a placeholder
      // case reads "Case ?" in the prose and the outline until something gives
      // it a name, and the name Lean just told us is that name.
      ...(isPlaceholderLabel(c.label) ? { label: ctorName } : {}),
      ...(ihNames.length ? { ihNames } : {}),
    };
  };

  const walk = (node: ProofNode): ProofNode => {
    switch (node.tag) {
      case 'induction': {
        const parentHypNames = new Set(
          (goalMap.get(node.id)?.hypotheses ?? []).map((h) => h.name),
        );
        const cases = node.cases.map((c) => enrichCase(c, parentHypNames));
        const casesChanged = cases.some((c, i) => c !== node.cases[i]);
        return casesChanged ? { ...node, cases } : node;
      }
      case 'intros':
      // A destructure has one child and no cases of its own, but anything
      // BELOW it still needs naming — without this the walk stopped here.
      case 'destructure': {
        const child = walk(node.child);
        return child === node.child ? node : { ...node, child };
      }
      case 'unfold':
      case 'fold':
      case 'rewrite':
      case 'simp': {
        const child = walk(node.child);
        return child === node.child ? node : { ...node, child };
      }
      case 'have': {
        const child = walk(node.child);
        const proofTree = node.proofTree ? walk(node.proofTree) : node.proofTree;
        if (child === node.child && proofTree === node.proofTree) return node;
        return { ...node, child, ...(node.proofTree ? { proofTree } : {}) };
      }
      case 'suffices': {
        const child = walk(node.child);
        const byProof = node.byProof ? walk(node.byProof) : node.byProof;
        if (child === node.child && byProof === node.byProof) return node;
        return { ...node, child, ...(node.byProof ? { byProof } : {}) };
      }
      case 'apply': {
        const children = node.children.map(walk);
        const kidsChanged = children.some((c, i) => c !== node.children[i]);
        return kidsChanged ? { ...node, children } : node;
      }
      default:
        return node;
    }
  };

  const newRoot = walk(root);
  return { root: newRoot, changed };
}
