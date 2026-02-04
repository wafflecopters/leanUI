import { describe, test, expect } from 'vitest';
import { TTKTerm, mkVar, mkConst, mkApp, TTKContext } from './kernel';
import { detectIllTypedAbstraction } from './with-abstraction';

/**
 * Ill-typed abstraction occurs when:
 *
 * 1. We want to abstract over scrutinee S in goal G
 * 2. Goal G contains a free variable V (other than S)
 * 3. The TYPE of V mentions S
 * 4. After abstracting S → w, V's type becomes ill-formed
 *
 * Classic example (Agda):
 *   bad : (p : Σ A B) → H (fst p) (snd p)
 *   bad p with fst p
 *
 * Problem:
 *   - snd p : B (fst p)  ← type mentions fst p
 *   - After abstracting fst p → w:
 *     - Goal has (snd p) with type B (fst p)
 *     - But we need type B w
 *     - Type mismatch! Ill-typed!
 */
describe('Ill-Typed Abstraction Detection', () => {
  describe('detectIllTypedAbstraction', () => {
    test('allows abstraction when no dependencies', () => {
      // Context: x : Nat, y : Nat
      const context: TTKContext = [
        { name: 'x', type: mkConst('Nat') },
        { name: 'y', type: mkConst('Nat') }
      ];

      const scrutinee = mkVar(1); // x
      // Goal: Equal x y (mentions both x and y)
      const goal = mkApp(
        mkApp(mkConst('Equal'), mkVar(1)), // x
        mkVar(0) // y
      );

      // y's type (Nat) does NOT mention x
      // So abstracting over x is safe
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(false);
      expect(result.problematicVars).toEqual([]);
    });

    test('detects dependent pair projection issue', () => {
      // Simplified dependent pair case
      // Context:
      //   A : Type
      //   B : A -> Type  (dependent function)
      //   p : Pair A (B a) for some a
      //   fst_p : A
      //   snd_p : B fst_p  ← TYPE MENTIONS fst_p!

      const context: TTKContext = [
        { name: 'A', type: mkConst('Type') },
        { name: 'B', type: mkApp(mkConst('Arrow'), mkVar(0)) }, // B : A -> Type
        { name: 'p', type: mkApp(mkConst('Pair'), mkVar(1)) },
        { name: 'fst_p', type: mkVar(2) }, // fst_p : A
        {
          name: 'snd_p',
          type: mkApp(mkVar(3), mkVar(0)) // snd_p : B fst_p
        }
      ];

      const scrutinee = mkVar(1); // fst_p
      // Goal: H fst_p snd_p
      const goal = mkApp(
        mkApp(mkConst('H'), mkVar(1)), // fst_p
        mkVar(0) // snd_p
      );

      // snd_p's type is (B fst_p), which MENTIONS fst_p
      // Abstracting over fst_p would make snd_p's type ill-formed
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(true);
      expect(result.problematicVars.length).toBe(1);
      expect(result.problematicVars[0].varIndex).toBe(0); // snd_p
      expect(result.problematicVars[0].varName).toBe('snd_p');
    });

    test('detects when dependent var appears in goal', () => {
      // If a variable appears in the goal AND its type mentions the scrutinee,
      // that's ill-typed

      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        { name: 'm', type: mkApp(mkConst('Vec'), mkVar(0)) } // m : Vec n (type mentions n!)
      ];

      const scrutinee = mkVar(1); // n
      // Goal: Append n m (m appears and its type mentions n)
      const goal = mkApp(
        mkApp(mkConst('Append'), mkVar(1)), // n
        mkVar(0) // m
      );

      // m's type mentions n, and m appears in the goal
      // This is ill-typed
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(true);
      expect(result.problematicVars.length).toBe(1);
      expect(result.problematicVars[0].varName).toBe('m');
    });

    test('detects multiple problematic variables', () => {
      // Context where TWO variables depend on the scrutinee
      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        { name: 'v1', type: mkApp(mkConst('Vec'), mkVar(0)) }, // v1 : Vec n
        { name: 'v2', type: mkApp(mkConst('Vec'), mkVar(1)) }  // v2 : Vec n
      ];

      const scrutinee = mkVar(2); // n
      // Goal: Append v1 v2
      const goal = mkApp(
        mkApp(mkConst('Append'), mkVar(1)), // v1
        mkVar(0) // v2
      );

      // Both v1 and v2 have types that mention n
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(true);
      expect(result.problematicVars.length).toBe(2);
    });

    test('only checks variables that appear in goal', () => {
      // If a variable doesn't appear in the goal, we don't care about its type

      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        { name: 'v', type: mkApp(mkConst('Vec'), mkVar(0)) }, // v : Vec n (mentions n!)
        { name: 'x', type: mkConst('Nat') }
      ];

      const scrutinee = mkVar(2); // n
      // Goal: Equal n x (doesn't mention v!)
      const goal = mkApp(
        mkApp(mkConst('Equal'), mkVar(2)), // n
        mkVar(0) // x
      );

      // v's type mentions n, but v doesn't appear in the goal
      // So this is safe
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(false);
    });

    test('handles nested type dependencies', () => {
      // Type mentions scrutinee deeply nested

      const context: TTKContext = [
        { name: 'n', type: mkConst('Nat') },
        {
          name: 'v',
          // v : List (Vec n) - scrutinee nested in type
          type: mkApp(
            mkConst('List'),
            mkApp(mkConst('Vec'), mkVar(0))
          )
        }
      ];

      const scrutinee = mkVar(1); // n
      // Goal mentions v
      const goal = mkApp(mkConst('length'), mkVar(0)); // length v

      // v's type mentions n (nested)
      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(true);
      expect(result.problematicVars[0].varName).toBe('v');
    });
  });

  describe('error messages', () => {
    test('produces helpful error message', () => {
      const context: TTKContext = [
        { name: 'p', type: mkConst('Pair') },
        { name: 'fst_p', type: mkConst('A') },
        { name: 'snd_p', type: mkApp(mkConst('B'), mkVar(0)) } // snd_p : B fst_p (mkVar(0) = fst_p from snd_p's perspective)
      ];

      const scrutinee = mkVar(1); // fst_p
      const goal = mkApp(mkConst('H'), mkVar(0)); // H snd_p

      const result = detectIllTypedAbstraction(scrutinee, goal, context);

      expect(result.isIllTyped).toBe(true);
      expect(result.errorMessage).toContain('snd_p');
      expect(result.errorMessage).toContain('fst_p');
      expect(result.errorMessage).toMatch(/type.*depends on/i);
    });
  });
});

/**
 * Result of ill-typed abstraction detection
 */
export interface IllTypedAbstractionResult {
  isIllTyped: boolean;
  problematicVars: Array<{
    varIndex: number;
    varName: string;
    varType: TTKTerm;
  }>;
  errorMessage?: string;
}
