import { addDefinition, addInductiveDefinition, CheckError, DefinitionsMap } from "./term";
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
  let newDefinitions = definitions;

  // Ensure the signature is well-formed
  const typeResult = inferType(type, [], [], definitions);
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

  newDefinitions = addDefinition(newDefinitions, name, type);

  const errors: CheckError[] = [];

  // Ensure the constructor types are well-formed
  for (const ctor of constructors) {
    const ctorResult = inferType(ctor.type, [], [], newDefinitions);
    if (!ctorResult.success) {
      errors.push({
        message: ctorResult.error,
        path: [],
        term: ctor.type,
        definitions: newDefinitions
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
    newDefinitions = addDefinition(newDefinitions, ctor.name, ctor.type);
  }

  // Add the inductive type to the definitions
  newDefinitions = addInductiveDefinition(newDefinitions, name, type, constructors, indexPositions);

  // TODO: ensure indices fit within the type
  // TODO: check for strict positivity

  return {
    success: true,
    newDefinitions
  }
}