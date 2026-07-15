/**
 * Slot-based term building — the Lean-path port of the TT editor's
 * TermBuilder (term-builder.ts): pick a hypothesis projection (e.g.
 * `limF.eps_delta`), see one SLOT per remaining argument with its type, fill
 * slots from per-slot suggestions or free input, validate live, commit as a
 * `have`.
 *
 * Where TT used kernel metas per slot, the Lean path PROBES: analyze
 * `have __use := <fn> <filled…>` and read `__use`'s (function) type from the
 * goal state — the remaining Pi binders ARE the open slots. One round-trip per
 * fill (~0.2s with the persistent workers), so the builder feels live.
 *
 * This module is the PURE part: parsing a pretty-printed function type into
 * slots, assembling the applied expression, ranking suggestions. The probing
 * itself lives with the UI (it needs the assemble/analyze plumbing).
 */

export interface TermSlot {
  /** Binder name, when the type ascribed one (`(epsilon : ℝ)` → "epsilon"). */
  name?: string;
  /** Pretty-printed slot type (Lean's own rendering, notation included). */
  type: string;
}

export interface ParsedSlots {
  slots: TermSlot[];
  /** What remains after all explicit slots are given. */
  returnType: string;
}

/** Split `s` at the first TOP-LEVEL occurrence of `sep` (depth 0 wrt (), [], {}). */
function splitTop(s: string, sep: string): [string, string] | null {
  let depth = 0;
  for (let i = 0; i + sep.length <= s.length; i++) {
    const c = s[i];
    if (c === '(' || c === '[' || c === '{' || c === '⟨') depth++;
    else if (c === ')' || c === ']' || c === '}' || c === '⟩') depth--;
    else if (depth === 0 && s.startsWith(sep, i)) return [s.slice(0, i), s.slice(i + sep.length)];
  }
  return null;
}

/** The matching close for the group opening at `s[0]` (assumed `(` or `{`). */
function matchingClose(s: string): number {
  const open = s[0];
  const close = open === '(' ? ')' : '}';
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === open) depth++;
    else if (s[i] === close) {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

/**
 * Parse a pretty-printed (function) type into explicit argument SLOTS.
 * Handles the forms Lean prints:
 *   `(a b : T) → rest`      — named explicit binders (one slot per name)
 *   `{a : T} → rest`        — implicit: SKIPPED (Lean infers them)
 *   `[inst : C] → rest`     — instance: skipped likewise
 *   `T → rest`              — anonymous antecedent (unnamed slot)
 *   `∀ (a : T) (b : S), rest` — ∀-spelled binders
 * Stops at the first non-arrow remainder — the return type.
 */
export function parseSlots(prettyType: string): ParsedSlots {
  const slots: TermSlot[] = [];
  let rest = prettyType.replace(/\s+/g, ' ').trim();

  for (;;) {
    // ∀ <binder groups>, rest — unwrap into the same binder handling.
    if (rest.startsWith('∀')) {
      const comma = splitTop(rest, ', ');
      if (!comma) break;
      let binders = comma[0].slice(1).trim(); // drop '∀'
      rest = comma[1].trim();
      while (binders.length > 0) {
        if (binders[0] === '(' || binders[0] === '{') {
          const close = matchingClose(binders);
          if (close === -1) break;
          const group = binders.slice(1, close);
          if (binders[0] === '(') pushGroupSlots(slots, group);
          binders = binders.slice(close + 1).trim();
        } else {
          // Bare ∀-bound names without ascription (rare in pp) — skip them.
          const sp = binders.indexOf(' ');
          if (sp === -1) break;
          binders = binders.slice(sp + 1).trim();
        }
      }
      continue;
    }

    const arrow = splitTop(rest, ' → ');
    if (!arrow) break;
    const [head, tail] = arrow;
    const h = head.trim();
    if ((h.startsWith('(') || h.startsWith('{') || h.startsWith('[')) && matchingClose(h.replace('[', '{').replace(']', '}')) === h.length - 1) {
      const inner = h.slice(1, -1);
      const isBinder = splitTop(inner, ' : ') !== null;
      if (h.startsWith('(') && isBinder) {
        pushGroupSlots(slots, inner);
      } else if (h.startsWith('(') && !isBinder) {
        slots.push({ type: inner.trim() }); // parenthesized anonymous antecedent
      }
      // `{…}` / `[…]` binders: implicit/instance — Lean infers, no slot.
    } else {
      slots.push({ type: h }); // anonymous antecedent, e.g. `0 < ε → …`
    }
    rest = tail.trim();
  }

  return { slots, returnType: rest };
}

/** `a b : T` → one slot per name, all with type T. */
function pushGroupSlots(slots: TermSlot[], group: string): void {
  const colon = splitTop(group, ' : ');
  if (!colon) {
    slots.push({ type: group.trim() });
    return;
  }
  const names = colon[0].trim().split(/\s+/).filter(Boolean);
  const type = colon[1].trim();
  for (const n of names) slots.push({ name: n, type });
}

/** The applied expression for the builder's current fill state:
 *  `fn (v₁) (v₂) …` — each value parenthesized unless it's a single token. */
export function appliedExpr(fn: string, values: readonly string[]): string {
  const parts = [fn.trim()];
  for (const v of values) {
    const t = v.trim();
    if (!t) continue;
    parts.push(/^[A-Za-z0-9_.'⟨⟩]+$/.test(t) || (t.startsWith('(') && t.endsWith(')')) ? t : `(${t})`);
  }
  return parts.join(' ');
}

/** The applied expression with `?_` for UNFILLED slots — Lean's term-mode
 *  hole, so a partially-built have still elaborates and the holes become
 *  visible goals (exactly the TT builder's `?` placeholders). */
export function appliedExprWithHoles(fn: string, values: ReadonlyArray<string | null>): string {
  const parts = [fn.trim()];
  for (const v of values) {
    if (v === null || v.trim() === '') {
      parts.push('?_');
      continue;
    }
    const t = v.trim();
    parts.push(/^[A-Za-z0-9_.'⟨⟩?]+$/.test(t) || (t.startsWith('(') && t.endsWith(')')) ? t : `(${t})`);
  }
  return parts.join(' ');
}

/** Parse a have-expression back into fn + argument values (`?_`/`?` → null) —
 *  inverse of appliedExprWithHoles for re-opening the builder on an existing
 *  have. Top-level split only (parens kept intact). */
export function parseApplied(expr: string): { fn: string; values: Array<string | null> } {
  const s = expr.replace(/\s+/g, ' ').trim();
  const parts: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of s) {
    if (ch === '(' || ch === '[' || ch === '{' || ch === '⟨') depth++;
    else if (ch === ')' || ch === ']' || ch === '}' || ch === '⟩') depth--;
    if (ch === ' ' && depth === 0) {
      if (cur) parts.push(cur);
      cur = '';
    } else {
      cur += ch;
    }
  }
  if (cur) parts.push(cur);
  const [fn = '', ...args] = parts;
  const values = args.map((a) => {
    if (a === '?_' || a === '?') return null;
    return a.startsWith('(') && a.endsWith(')') ? a.slice(1, -1) : a;
  });
  return { fn, values };
}

/** First identifier-ish token of a type — its head shape, for loose matching. */
function headToken(type: string): string {
  const m = type.trim().match(/[A-Za-z_][A-Za-z0-9_.']*|[<≤≥=∈+\-*/⟦]/);
  return m ? m[0] : '';
}

/**
 * Rank hypothesis names as fills for a slot: exact type-text match first
 * (the common case right after a re-probe specializes the slot type), then
 * same head shape. Mirrors TT's computeTermSlots head-matching.
 */
export function slotSuggestionNames(
  slotType: string,
  hyps: ReadonlyArray<{ name: string; type: string }>,
): string[] {
  const want = slotType.replace(/\s+/g, ' ').trim();
  const exact: string[] = [];
  const headMatch: string[] = [];
  const head = headToken(want);
  for (const h of hyps) {
    const t = h.type.replace(/\s+/g, ' ').trim();
    if (t === want) exact.push(h.name);
    else if (head && headToken(t) === head) headMatch.push(h.name);
  }
  return [...exact, ...headMatch];
}

/**
 * Candidate PROJECTIONS to "use" on a hypothesis — the Lean-path version of
 * TT's record-field "Use <field>" suggestions. Generic: every dotted
 * declaration `T.field` is a potential projection; rank by token overlap
 * between the declaration's type text and the hypothesis's type text (a
 * projection of the hyp's own structure shares its notation/tokens), cap, and
 * let the standard validation trials drop the ones that don't typecheck.
 */
export function projectionCandidates(
  hypName: string,
  hypType: string,
  declarations: ReadonlyArray<{ name: string; prettyType: string }>,
  cap = 6,
): string[] {
  const hypTokens = new Set(hypType.match(/[A-Za-z_][A-Za-z0-9_.']*|[⟦⟧]/g) ?? []);
  const scored: Array<{ expr: string; score: number }> = [];
  const seen = new Set<string>();
  for (const d of declarations) {
    const dot = d.name.lastIndexOf('.');
    if (dot <= 0) continue;
    const field = d.name.slice(dot + 1);
    if (seen.has(field)) continue;
    seen.add(field);
    let score = 0;
    for (const t of d.prettyType.match(/[A-Za-z_][A-Za-z0-9_.']*|[⟦⟧]/g) ?? []) {
      if (hypTokens.has(t)) score++;
    }
    if (score > 0) scored.push({ expr: `${hypName}.${field}`, score });
  }
  scored.sort((a, b) => b.score - a.score);
  return scored.slice(0, cap).map((s) => s.expr);
}
