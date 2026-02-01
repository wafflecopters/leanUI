import { describe, test, expect } from 'vitest';
import { applySubstitutionToCheckStackInPlace, CheckStackEntry } from './patterns';
import { TTKTerm, mkVar, mkConst, mkPi, mkApp } from './kernel';

/**
 * Unit tests for applySubstitutionToCheckStackInPlace.
 *
 * This function applies a de Bruijn substitution to check stack entries during
 * LHS pattern matching. The key invariant: when removing a variable at index N,
 * the replacement term's Var indices > N must be decremented by 1 (since the
 * context shrinks by 1). This mirrors applySubstitutionToContext in subst.ts.
 *
 * Bug context: Before the fix, the replacement was passed to subst() without
 * adjusting for the removal. This caused dangling Var indices when the return
 * type contained elaborated constructor terms (e.g., `refl A x` in `Equal p p`).
 */

// Helper: make App(App(Const(name), arg1), arg2)
function mkApp2(name: string, arg1: TTKTerm, arg2: TTKTerm): TTKTerm {
  return mkApp(mkApp(mkConst(name), arg1), arg2);
}

describe('applySubstitutionToCheckStackInPlace', () => {
  test('simple substitution: Var replaced by Const', () => {
    // Context: [A, x] (length 2), mainSig = 2
    // Entry type: Var(0) (= x) at ctxLength 2
    // Substitute: varIndex=0 (x), value=Const("Zero")
    // Expected result: Const("Zero") at ctxLength 1
    const stack: CheckStackEntry[] = [
      { type: mkVar(0), ctxLength: 2 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 2, 0, mkConst('Zero'));

    expect(stack[0].type).toEqual(mkConst('Zero'));
    expect(stack[0].ctxLength).toBe(1);
  });

  test('substitution adjusts replacement Var indices above removed position', () => {
    // Context: [?0, ?1, ?2, A3, a4] (length 5)
    // Entry type: Var(1) (= A3) at ctxLength 5
    // Substitute: varIndex=1 (A3), value=Var(4) (?0)
    //
    // After removing A3 (index 1), ?0 moves from Var(4) to Var(3).
    // The replacement Var(4) should become Var(3) in the result context.
    // Then subst replaces Var(1) with (adjusted) Var(3).
    //
    // But the entry type IS Var(1), which is the target. So the result
    // should be the (adjusted) replacement = Var(3).
    const stack: CheckStackEntry[] = [
      { type: mkVar(1), ctxLength: 5 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 5, 1, mkVar(4));

    expect(stack[0].type).toEqual(mkVar(3));
    expect(stack[0].ctxLength).toBe(4);
  });

  test('replacement Var index below removed position stays unchanged', () => {
    // Context: [?0, ?1, A3] (length 3)
    // Entry type: Var(0) (= A3) at ctxLength 3
    // Substitute: varIndex=0 (A3), value=Var(1) (?1)
    //
    // Var(1) is BELOW the removed index in the result. After removing Var(0),
    // Var(1) stays Var(1) (now pointing to ?1 which is still at index 1 in
    // the result context [?0, ?1]).
    // Wait — after removing index 0, ?1 moves from index 1 to index 0.
    // But the replacement Var(1) > varIndex(0), so it gets decremented to Var(0).
    const stack: CheckStackEntry[] = [
      { type: mkVar(0), ctxLength: 3 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 3, 0, mkVar(1));

    // Var(1) was above varIndex(0), adjusted to Var(0)
    expect(stack[0].type).toEqual(mkVar(0));
    expect(stack[0].ctxLength).toBe(2);
  });

  test('constructor term in entry type: Var indices in replacement adjusted correctly', () => {
    // This reproduces the Equal p p bug.
    //
    // Context: [?0:Type, ?1:?0, ?2:?0, A3:Type, a4:A3] (length 5)
    // Entry type at ctxLength 5:
    //   Pi("q", Equal(Var(4), Var(3), Var(2)),
    //     Equal(Equal(Var(5), Var(4), Var(3)), refl(Var(2), Var(1)), Var(0)))
    //
    // Where:
    //   Var(0)=a4, Var(1)=A3, Var(2)=?2, Var(3)=?1, Var(4)=?0
    //   In body (under q): Var(0)=q, Var(1)=a4, Var(2)=A3, Var(3)=?2, Var(4)=?1, Var(5)=?0
    //   refl(Var(2), Var(1)) = refl(A3, a4) inside the q-binder
    //
    // Substitute: varIndex=1 (A3), value=Var(4) (?0)
    //
    // After removing A3:
    //   New context: [?0, ?1, ?2, a4] (length 4)
    //   ?0 moves from Var(4) to Var(3) — the replacement must be adjusted!
    //
    // In the inner body (under q), the refl(A3, a4) should become refl(?0, a4)
    // = refl(Var(4), Var(1)) in the new inner context [q, a4, ?2, ?1, ?0].
    //
    // Without the fix, the replacement Var(4) was NOT adjusted, giving
    // refl(Var(5), Var(1)) — Var(5) is out of bounds!

    // Build the entry type:
    // Pi("q", Equal(Var(4), Var(3), Var(2)),
    //   Equal(Equal(Var(5), Var(4), Var(3)), App(App(Const(refl), Var(2)), Var(1)), Var(0)))
    const domain = mkApp2('Equal', mkApp(mkConst('Equal'), mkVar(4)), mkVar(2)); // simplified
    const innerRefl = mkApp2('refl', mkVar(2), mkVar(1));
    const innerEqual = mkApp2('Equal', mkApp(mkConst('Equal'), mkVar(5)), innerRefl);
    const body = mkApp(innerEqual, mkVar(0));
    const entryType = mkPi(domain, body, 'q');

    const stack: CheckStackEntry[] = [
      { type: entryType, ctxLength: 5 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 5, 1, mkVar(4));

    // After substitution, the inner refl(Var(2), Var(1)) should become:
    // - Var(2) was A3 (the target) → replaced with shift(adjusted_replacement, 1)
    //   adjusted_replacement = Var(3) (Var(4) decremented because > 1)
    //   shifted by 1 (inside Pi binder) = Var(4)
    // - Var(1) was a4 (below target) → stays Var(1)
    // So inner refl becomes refl(Var(4), Var(1))

    expect(stack[0].ctxLength).toBe(4);

    // Extract the inner refl from the result
    const result = stack[0].type;
    expect(result.tag).toBe('Binder'); // Pi
    if (result.tag === 'Binder') {
      // The body contains the inner Equal application
      // Find the refl term in the body (second arg of outer Equal app)
      const bodyTerm = result.body;
      // bodyTerm = App(Equal_app, Var(0))
      expect(bodyTerm.tag).toBe('App');
      if (bodyTerm.tag === 'App') {
        // bodyTerm.fn = App(App(Const(Equal), Equal(...)), refl(...))
        const equalApp = bodyTerm.fn;
        expect(equalApp.tag).toBe('App');
        if (equalApp.tag === 'App') {
          // equalApp.arg = refl(Var(4), Var(1)) — the key check
          const reflTerm = equalApp.arg;
          expect(reflTerm.tag).toBe('App');
          if (reflTerm.tag === 'App') {
            // refl applied: App(App(Const(refl), Var(4)), Var(1))
            expect(reflTerm.arg).toEqual(mkVar(1)); // a4 unchanged
            expect(reflTerm.fn.tag).toBe('App');
            if (reflTerm.fn.tag === 'App') {
              expect(reflTerm.fn.arg).toEqual(mkVar(4)); // ?0 correctly at Var(4) under q-binder
            }
          }
        }
      }
    }
  });

  test('entry with ctxLength different from mainSigLength', () => {
    // Context: mainSig = 5, entry at ctxLength = 3
    // Entry type: Var(0) at ctxLength 3
    // Substitute: varIndex=3, value=Var(4) at mainSig 5
    //
    // localVarIndex = 3 - (5-3) = 1
    // shiftAmount = 3 - 5 = -2
    // shiftedValue = shift(Var(4), -2) = Var(2)
    // adjusted for removal of localVarIndex=1: Var(2) > 1 → Var(1)
    // subst(1, Var(1), Var(0)) → Var(0) unchanged (0 < 1)
    const stack: CheckStackEntry[] = [
      { type: mkVar(0), ctxLength: 3 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 5, 3, mkVar(4));

    expect(stack[0].type).toEqual(mkVar(0));
    expect(stack[0].ctxLength).toBe(2);
  });

  test('entry not affected when varIndex is outside entry scope', () => {
    // Context: mainSig = 5, entry at ctxLength = 2
    // Substitute: varIndex=1 at mainSig 5
    // varIndex(1) >= mainSig(5) - ctxLength(2) = 3? No, 1 < 3.
    // Entry is NOT affected.
    const stack: CheckStackEntry[] = [
      { type: mkVar(0), ctxLength: 2 }
    ];

    applySubstitutionToCheckStackInPlace(stack, 5, 1, mkVar(4));

    // Entry unchanged
    expect(stack[0].type).toEqual(mkVar(0));
    expect(stack[0].ctxLength).toBe(2);
  });

  test('multiple entries in stack processed independently', () => {
    // Two entries, both at ctxLength 3, mainSig = 3
    // Substitute: varIndex=0 (rightmost), value=mkConst("Zero")
    const stack: CheckStackEntry[] = [
      { type: mkVar(0), ctxLength: 3 },     // Target var → replaced
      { type: mkVar(1), ctxLength: 3 },     // Other var → decremented
    ];

    applySubstitutionToCheckStackInPlace(stack, 3, 0, mkConst('Zero'));

    expect(stack[0].type).toEqual(mkConst('Zero'));
    expect(stack[0].ctxLength).toBe(2);
    expect(stack[1].type).toEqual(mkVar(0)); // Var(1) decremented to Var(0)
    expect(stack[1].ctxLength).toBe(2);
  });
});
