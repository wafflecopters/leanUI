import { TTKTerm, TTKContext } from './tt-kernel';
import type { ConstructorInfo as StepperConstructorInfo } from './pattern-elab-stepper';

/**
 * Build constructor environment for pattern elaboration stepper.
 * Extracts constructors from typing context based on their return types.
 *
 * Constructors are identified as bindings whose types return applications or constants
 * (not Sort/Type), such as:
 * - Zero : Nat
 * - Succ : Nat -> Nat
 * - Cons : A -> List A -> List A
 *
 * @param context - Type checking context containing all bindings
 * @returns Map of constructor names to their parameter and return type information
 */
export function buildStepperEnvironment(
  context: TTKContext
): Map<string, StepperConstructorInfo> {
  const env = new Map<string, StepperConstructorInfo>();

  // Helper to unwrap Pi types and extract params + return type
  const unwrapPi = (type: TTKTerm): { params: Array<{ name: string; type: TTKTerm }>; returnType: TTKTerm } => {
    const params: Array<{ name: string; type: TTKTerm }> = [];
    let curr = type;
    while (curr.tag === 'Binder' && curr.binderKind.tag === 'BPi') {
      params.push({ name: curr.name, type: curr.domain });
      curr = curr.body;
    }
    return { params, returnType: curr };
  };

  // Helper to check if a type looks like it returns an inductive type (not Type/Sort)
  const isConstructorType = (type: TTKTerm): boolean => {
    const { returnType } = unwrapPi(type);
    // Constructors return applications or constants, not Sort/Type
    return returnType.tag === 'App' || returnType.tag === 'Const';
  };

  // Extract constructors from context
  for (const binding of context) {
    if (isConstructorType(binding.type)) {
      const { params, returnType } = unwrapPi(binding.type);
      env.set(binding.name, {
        name: binding.name,
        params,
        returnType
      });
    }
  }

  return env;
}
