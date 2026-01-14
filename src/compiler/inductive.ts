import { CheckError, DefinitionsMap } from "./term";
import { TTKTerm } from "../types/tt-kernel";
import { inferType } from "./checker";

export function checkInductiveDeclaration(
  _name: string,
  type: TTKTerm,
  constructors: Array<{ name: string; type: TTKTerm }>,
  _indexPositions: number[],
  definitions: DefinitionsMap,
): {
  success: false,
  errors: CheckError[]
} | {
  success: true,
  value: undefined
} {
  try {
    // Ensure the signature is well-formed
    inferType(type, [], [], definitions);

    const definitionsWithInductive = new Map<string, TTKTerm>(definitions);
    definitionsWithInductive.set(_name, type);

    // Ensure the constructor types are well-formed
    for (const ctor of constructors) {
      inferType(ctor.type, [], [], definitionsWithInductive);
    }
  } catch (e) {
    return {
      success: false,
      errors: [{
        message: e instanceof Error ? e.message : String(e),
        path: [],
        term: type,
        context: []
      }]
    }
  }

  debugger

  return {
    success: true,
    value: undefined
  }
}