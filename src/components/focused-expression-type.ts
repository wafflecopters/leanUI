import { expressionNodeToTTerm } from '../compiler/bridge';
import { inferTermInContext } from '../compiler/contextual-inference';
import { elabContextToKernel, elabToKernel } from '../compiler/elab';
import { prettyPrint as prettyPrintTTK } from '../compiler/kernel';
import { TContext, TTerm } from '../compiler/surface';
import { ExpressionNode, FocusPath } from '../types/enhanced-focus';
import { createDefinitionsMap, type DefinitionsMap } from '../compiler/term';

function contextToMaps(context: TContext): { varContext: Map<string, number>; typeContext: Map<string, TTerm> } {
  const varContext = new Map<string, number>();
  const typeContext = new Map<string, TTerm>();

  context.forEach((binding, index) => {
    const debruijnIndex = context.length - 1 - index;
    varContext.set(binding.name, debruijnIndex);
    typeContext.set(binding.name, binding.type);
  });

  return { varContext, typeContext };
}

function getFocusedNode(exprNode: ExpressionNode, focusPath: FocusPath): ExpressionNode | null {
  let focusedNode: ExpressionNode | undefined = exprNode;
  for (const segment of focusPath) {
    const idx = typeof segment === 'string' ? parseInt(segment, 10) : segment;
    if (!focusedNode?.children || Number.isNaN(idx) || idx < 0 || idx >= focusedNode.children.length) {
      return null;
    }
    focusedNode = focusedNode.children[idx];
  }
  return focusedNode ?? null;
}

export type FocusedExpressionTypeResult =
  | { readonly type: string }
  | { readonly error: string };

export function getFocusedExpressionType(
  exprNode: ExpressionNode,
  focusPath: FocusPath,
  typeContext: TContext,
  definitions?: DefinitionsMap,
): FocusedExpressionTypeResult {
  const focusedNode = getFocusedNode(exprNode, focusPath);
  if (!focusedNode) {
    return { error: 'Invalid focus path' };
  }

  const { varContext, typeContext: typeCtxMap } = contextToMaps(typeContext);
  const focusedTTerm = expressionNodeToTTerm(focusedNode, varContext, typeCtxMap);
  const focusedTTKTerm = elabToKernel(focusedTTerm);
  const kernelContext = elabContextToKernel(typeContext);

  try {
    const inferredEnv = inferTermInContext({
      term: focusedTTKTerm,
      context: kernelContext,
      definitions: definitions ?? createDefinitionsMap(),
    });
    return { type: prettyPrintTTK(inferredEnv.zonkTerm(inferredEnv.value)) };
  } catch (error) {
    return { error: error instanceof Error ? error.message : String(error) };
  }
}
