import { addDefinition, addDefinitionInTCEnv, addInductiveDefinition, addInductiveDefinitionInTCEnv, CheckError, createTCEnv, DefinitionsMap } from "./term";
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
  errors: CheckError[]
} | {
  success: true,
  newDefinitions: DefinitionsMap
} {
  let newEnv = createTCEnv(definitions);

  const typeResult = inferType(type, [], newEnv);
  if (!typeResult.success) {
    return {
      success: false,
      errors: [{
        message: typeResult.error,
        path: [],
        term: type,
        definitions: definitions
      }]
    }
  }

  newEnv = addDefinitionInTCEnv(newEnv, name, type);

  const errors: CheckError[] = [];

  // Ensure the constructor types are well-formed
  for (const ctor of constructors) {
    const ctorResult = inferType(ctor.type, [], newEnv);
    if (!ctorResult.success) {
      errors.push({
        message: ctorResult.error,
        path: [],
        term: ctor.type,
        definitions: newEnv.definitions
      })
    }
  }

  if (errors.length > 0) {
    return {
      success: false,
      errors
    }
  }

  // Add the constructor types to the definitions
  for (const ctor of constructors) {
    newEnv = addDefinitionInTCEnv(newEnv, ctor.name, ctor.type);
  }

  // Add the inductive type to the definitions
  newEnv = addInductiveDefinitionInTCEnv(newEnv, name, type, constructors, indexPositions);

  // TODO: ensure indices fit within the type
  // TODO: check for strict positivity

  return {
    success: true,
    newDefinitions: newEnv.definitions
  }
}