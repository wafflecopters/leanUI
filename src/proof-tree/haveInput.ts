/**
 * Parse what the user typed into a "Have…" box.
 *
 * Two shapes, and the difference matters:
 *
 *   `h := divTwoPos ε epsPos`   — a TERM have. The expression is the proof.
 *   `h : 0 < ε / 2`             — a TYPED have. The statement is given and the
 *                                 proof is an open goal you build interactively.
 *
 * The typed form is the one an ε-δ proof is made of ("observe that 0 < ε/2 …"),
 * and it's what hoisting an obligation produces — but until now the only way to
 * get one was to hoist, because the input box accepted `:=` and nothing else.
 * `h : T := ?` (an explicit hole) means the same as `h : T`.
 */
export type HaveInput =
  | { kind: 'term'; name: string; expr: string }
  | { kind: 'typed'; name: string; typeExpr: string };

/** A hole the user can write for "I'll prove this later". */
const HOLE = /^(\?|\?_|_|sorry)$/;

export function parseHaveInput(value: string): HaveInput | null {
  const trimmed = value.trim();
  if (!trimmed) return null;

  const assign = trimmed.indexOf(':=');
  const head = (assign === -1 ? trimmed : trimmed.slice(0, assign)).trim();
  const tail = assign === -1 ? '' : trimmed.slice(assign + 2).trim();

  // The name is everything before the first top-level `:`; the rest is a type
  // ascription. `h : 0 < ε` — note the type itself may contain no top-level `:`.
  const colon = head.indexOf(':');
  const name = (colon === -1 ? head : head.slice(0, colon)).trim();
  const typeExpr = colon === -1 ? '' : head.slice(colon + 1).trim();
  if (!name || /\s/.test(name)) return null;

  if (typeExpr) {
    // `h : T := e` gives both — the term proves the stated type, so it's still
    // a term have (with its type recorded); `h : T` and `h : T := ?` are typed.
    if (tail && !HOLE.test(tail)) return { kind: 'term', name, expr: tail };
    return { kind: 'typed', name, typeExpr };
  }
  if (!tail || HOLE.test(tail)) return null; // `h` alone says nothing
  return { kind: 'term', name, expr: tail };
}
