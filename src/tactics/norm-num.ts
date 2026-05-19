/**
 * norm_num — closed-arithmetic decision procedure on any "Carrier"-style type
 * registered via @carrierAdd/@carrierSub/@carrierMul/@carrierNeg/@carrierInv/
 * @carrierDiv operation tags and @carrierValue literal tags.
 *
 * Generic across presets: no hardcoded names like "radd". Reads from
 * `definitions.carrierOpByFn` (function name → op kind) and
 * `definitions.carrierValues` (function name → Rat literal value) to
 * recognize which kernel terms count as arithmetic operations vs literals.
 *
 * For coercions (e.g. `realOfRat R q` mapping a Rat literal into Carrier R),
 * reads from `definitions.ofRatByTargetHead` / `ofNatByTargetHead` /
 * `ofIntByTargetHead` (existing registries populated by @ofRat / @ofNat /
 * @ofInt annotations) to find coercion-function names dynamically.
 *
 * MVP exports `inferIsRat(term, definitions)` — pure function that returns
 * the term's closed Rat value or null if it's not a recognized closed
 * arithmetic expression in the registered Carrier algebra.
 */

import { TTKTerm } from '../compiler/kernel';
import { DefinitionsMap } from '../compiler/term';

export interface RatValue {
  readonly num: bigint;
  readonly den: bigint;
}

/** Reduce a num/den pair to canonical form: gcd-reduced, positive den. */
function canonRat(num: bigint, den: bigint): RatValue | null {
  if (den === 0n) return null;
  if (den < 0n) { num = -num; den = -den; }
  let a = num < 0n ? -num : num;
  let b = den;
  while (b !== 0n) { [a, b] = [b, a % b]; }
  const g = a === 0n ? 1n : a;
  return { num: num / g, den: den / g };
}

const ratAdd = (a: RatValue, b: RatValue) => canonRat(a.num * b.den + b.num * a.den, a.den * b.den);
const ratSub = (a: RatValue, b: RatValue) => canonRat(a.num * b.den - b.num * a.den, a.den * b.den);
const ratMul = (a: RatValue, b: RatValue) => canonRat(a.num * b.num, a.den * b.den);
const ratNeg = (a: RatValue) => canonRat(-a.num, a.den);
const ratInv = (a: RatValue) => a.num === 0n ? null : canonRat(a.den, a.num);
const ratDiv = (a: RatValue, b: RatValue) => b.num === 0n ? null : canonRat(a.num * b.den, a.den * b.num);

function collectSpine(term: TTKTerm): { head: TTKTerm; args: TTKTerm[] } {
  const args: TTKTerm[] = [];
  let cur = term;
  while (cur.tag === 'App') {
    args.unshift(cur.arg);
    cur = cur.fn;
  }
  return { head: cur, args };
}

/** Extract a closed Nat value from kernel Nat representation. */
function natToBigInt(term: TTKTerm, definitions: DefinitionsMap): bigint | null {
  if (term.tag === 'NatLit') return term.value;
  if (term.tag !== 'App' && term.tag !== 'Const') return null;
  const { head, args } = collectSpine(term);
  if (head.tag !== 'Const') return null;
  // Zero ctor of any @impl=nat type
  if (args.length === 0) {
    const nat = definitions.natImplByCtor?.get(head.name);
    return nat?.zeroCtor === head.name ? 0n : null;
  }
  if (args.length === 1) {
    const nat = definitions.natImplByCtor?.get(head.name);
    if (nat?.succCtor === head.name) {
      const inner = natToBigInt(args[0], definitions);
      return inner === null ? null : inner + 1n;
    }
  }
  return null;
}

/** Extract a closed Int value from kernel Int representation. */
function intToBigInt(term: TTKTerm, definitions: DefinitionsMap): bigint | null {
  if (term.tag !== 'App') return null;
  const { head, args } = collectSpine(term);
  if (head.tag !== 'Const' || args.length !== 1) return null;
  const intImpl = definitions.intImplByCtor?.get(head.name);
  if (!intImpl) return null;
  const inner = natToBigInt(args[0], definitions);
  if (inner === null) return null;
  if (head.name === intImpl.ofNatCtor) return inner;
  if (head.name === intImpl.negSuccCtor) return -(inner + 1n);
  return null;
}

/** Extract a closed Rat value from kernel Rat representation. */
function ratToValue(term: TTKTerm, definitions: DefinitionsMap): RatValue | null {
  if (term.tag === 'RatLit') return canonRat(term.num, term.den);
  if (term.tag === 'NatLit') return canonRat(term.value, 1n);
  if (term.tag !== 'App') return null;
  const { head, args } = collectSpine(term);
  if (head.tag !== 'Const') return null;
  const ratImpl = definitions.ratImplByCtor?.get(head.name);
  if (ratImpl && args.length === 3) {
    // MkRat-style ctor: (num: Int, den: Nat, proof). We ignore proof.
    const num = intToBigInt(args[0], definitions);
    if (num === null) return null;
    const den = natToBigInt(args[1], definitions);
    if (den === null) return null;
    return canonRat(num, den);
  }
  return null;
}

/** Build inverse maps: function name → coercion role (one of 'ofNat'/'ofInt'/'ofRat'). */
function buildCoercionFnSet(definitions: DefinitionsMap): {
  ofNat: Set<string>;
  ofInt: Set<string>;
  ofRat: Set<string>;
} {
  const ofNat = new Set<string>();
  const ofInt = new Set<string>();
  const ofRat = new Set<string>();
  if (definitions.ofNatByTargetHead) {
    for (const fn of definitions.ofNatByTargetHead.values()) ofNat.add(fn);
  }
  if (definitions.ofIntByTargetHead) {
    for (const fn of definitions.ofIntByTargetHead.values()) ofInt.add(fn);
  }
  if (definitions.ofRatByTargetHead) {
    for (const fn of definitions.ofRatByTargetHead.values()) ofRat.add(fn);
  }
  return { ofNat, ofInt, ofRat };
}

/**
 * Classify a kernel term as a closed Rat literal value, if recognized.
 *
 * Recognition is fully data-driven from registry entries:
 *   - `@carrierValue N` tags  → leaf literal (rzero R / rone R / rtwo R / etc.)
 *   - `@carrierAdd / @carrierSub / @carrierMul / @carrierNeg / @carrierInv /
 *      @carrierDiv` tags → arithmetic compound (radd / rsub / rmul / etc.)
 *   - `@ofNat / @ofInt / @ofRat` tags → coercion of a closed Nat / Int / Rat
 *     literal into the Carrier (realOfNat / realOfInt / realOfRat / etc.)
 *
 * Returns null if the term contains any non-recognized head, free variable,
 * hole, or meta — i.e. it's not a closed arithmetic expression in the
 * registered algebra.
 */
export function inferIsRat(term: TTKTerm, definitions: DefinitionsMap): RatValue | null {
  const { head, args } = collectSpine(term);
  if (head.tag !== 'Const') return null;
  const name = head.name;

  // 1. Carrier-level literal (rzero / rone / rtwo / rhalf / user-defined)
  const carrierVal = definitions.carrierValues?.get(name);
  if (carrierVal) {
    return canonRat(carrierVal.num, carrierVal.den);
  }

  // 2. Coercion of a closed literal (realOfNat / realOfInt / realOfRat / etc.)
  const coerc = buildCoercionFnSet(definitions);
  if (coerc.ofRat.has(name)) {
    // realOfRat-like: spine has (carrier-type-arg, rat-literal); rat-literal is last
    if (args.length < 1) return null;
    return ratToValue(args[args.length - 1], definitions);
  }
  if (coerc.ofInt.has(name)) {
    if (args.length < 1) return null;
    const i = intToBigInt(args[args.length - 1], definitions);
    return i === null ? null : canonRat(i, 1n);
  }
  if (coerc.ofNat.has(name)) {
    if (args.length < 1) return null;
    const n = natToBigInt(args[args.length - 1], definitions);
    return n === null ? null : canonRat(n, 1n);
  }

  // 3. Carrier-level arithmetic op (radd / rsub / rmul / rneg / rinv / rdiv)
  const op = definitions.carrierOpByFn?.get(name);
  if (op) {
    // Spine shape is (R-implicit-or-explicit, args...). We're lenient: take
    // the LAST 1 or 2 args as the value args, ignoring leading type/instance
    // args. radd has shape `radd {R} a b` (3 spine elements: R, a, b) but
    // could appear with R curried away (2 elements: a, b).
    const isBinary = op === 'add' || op === 'sub' || op === 'mul' || op === 'div';
    const isUnary = op === 'neg' || op === 'inv';
    if (isBinary) {
      if (args.length < 2) return null;
      const a = inferIsRat(args[args.length - 2], definitions);
      const b = inferIsRat(args[args.length - 1], definitions);
      if (a === null || b === null) return null;
      switch (op) {
        case 'add': return ratAdd(a, b);
        case 'sub': return ratSub(a, b);
        case 'mul': return ratMul(a, b);
        case 'div': return ratDiv(a, b);
      }
    }
    if (isUnary) {
      if (args.length < 1) return null;
      const a = inferIsRat(args[args.length - 1], definitions);
      if (a === null) return null;
      switch (op) {
        case 'neg': return ratNeg(a);
        case 'inv': return ratInv(a);
      }
    }
  }

  return null;
}

/** Render a RatValue for display in suggestion labels. */
export function ratValueLabel(v: RatValue): string {
  if (v.den === 1n) return v.num.toString();
  return `${v.num.toString()}/${v.den.toString()}`;
}

/** Check if a term's head is a registered carrier-arithmetic op. Used by the
 *  suggestion pipeline to decide whether to attempt `Compute → X` on a
 *  subterm click without hardcoding op names. */
export function isCarrierArithHead(headName: string | undefined, definitions: DefinitionsMap): boolean {
  if (!headName) return false;
  return definitions.carrierOpByFn?.has(headName) ?? false;
}
