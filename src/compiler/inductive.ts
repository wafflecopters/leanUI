import { addDefinition, addDefinitionInTCEnv, addInductiveDefinition, addInductiveDefinitionInTCEnv, CheckError, createTCEnv, DefinitionsMap, InductiveDefinition, TCEnvError } from "./term";
import { TTKTerm } from "../types/tt-kernel";
import { inferType } from "./checker";

export function checkInductiveDeclaration(
  name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  indexPositions: number[],
  definitions: DefinitionsMap,
): {
  success: false,
  errors: TCEnvError<unknown>[]
} | {
  success: true,
  newDefinitions: DefinitionsMap
} {
  const inductiveDefinition: InductiveDefinition = { name, type, constructors, indexPositions };
  const defEnv = createTCEnv(definitions).withValue(inductiveDefinition);

  try {
    inferType(defEnv.inInductiveDefinitionType());
  } catch (e) {
    if (e instanceof TCEnvError) {
      return {
        success: false,
        errors: [e]
      }
    } else {
      return {
        success: false,
        errors: [new TCEnvError(e instanceof Error ? e.message : String(e), defEnv)]
      }
    }
  }

  let ctorsEnv = addDefinitionInTCEnv(defEnv, name, type).inInductiveDefinitionConstructors();

  const errors: TCEnvError<unknown>[] = [];

  let index = 0
  for (const ctor of constructors) {
    try {
      inferType(ctorsEnv.inInductiveDefinitionConstructor(index).inInductiveDefinitionConstructorType());
      ctorsEnv = addDefinitionInTCEnv(ctorsEnv, ctor.name, ctor.type);
    } catch (e) {
      if (e instanceof TCEnvError) {
        errors.push(e)
      } else {
        errors.push(new TCEnvError(e instanceof Error ? e.message : String(e), ctorsEnv))
      }
    }
    index++;
  }

  if (errors.length > 0) {
    return {
      success: false,
      errors
    }
  }

  const newEnv = addInductiveDefinitionInTCEnv(ctorsEnv, name, type, constructors, indexPositions);

  // TODO: ensure indices fit within the type
  // TODO: check for strict positivity

  return {
    success: true,
    newDefinitions: newEnv.definitions
  }
}