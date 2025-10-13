# Bugfix: Application Type Support in TT Bridge

## Issue

When trying to start a proof on a let-binding claim, the following error occurred:

```
Uncaught Error: Unsupported expression type: application
    at expressionNodeToTTerm (tt-bridge.ts:111)
    at createEqualityProofTerm (tt-bridge.ts:163)
```

## Root Cause

The UI expression parser ([enhanced-focus.ts:parseExpressionToAST](src/types/enhanced-focus.ts)) can create nodes with `type: 'application'` for function applications (e.g., `f x y`, or potentially from parsing certain expressions).

The TT bridge conversion function `expressionNodeToTTerm()` did not handle the `'application'` case, only handling:
- `variable`
- `literal`
- `binop`
- `equality`
- `unop`

## Fix

Added two new cases to [tt-bridge.ts:expressionNodeToTTerm](src/types/tt-bridge.ts#L110):

### 1. Application Type
```typescript
case 'application':
  // Function application: f a b c...
  // children[0] is the function, rest are arguments
  if (expr.children.length === 0) {
    throw new Error('Application requires at least a function');
  }

  // Convert function and all arguments to TT terms
  const func = expressionNodeToTTerm(expr.children[0], context);
  const args = expr.children.slice(1).map(arg => expressionNodeToTTerm(arg, context));

  // Build nested applications: (((f a) b) c)
  let result = func;
  for (const arg of args) {
    result = mkApp(result, arg);
  }
  return result;
```

**How it works:**
- `children[0]` is the function being applied
- `children[1..]` are the arguments
- We build nested left-associative applications: `((f a) b)` not `(f (a b))`
- Example: `f x y` → `((f x) y)`

### 2. Inequality Type (Bonus)
Also added support for inequalities (`<`, `>`, `≤`, `≥`) which were declared in the type but not handled:

```typescript
case 'inequality':
  // Handle inequality similar to equality
  if (expr.children.length !== 2) {
    throw new Error('Inequality requires exactly 2 children');
  }
  const ineqLeft = expressionNodeToTTerm(expr.children[0], context);
  const ineqRight = expressionNodeToTTerm(expr.children[1], context);

  const ineqOp: TTerm = {
    tag: 'Const',
    name: expr.operator || '<',
    type: TT_CONSTANTS.Real
  };

  return mkApp(mkApp(ineqOp, ineqLeft), ineqRight);
```

## Testing

Created [tt-bridge.test.ts](src/types/tt-bridge.test.ts) with comprehensive tests:
- Simple variables
- Literals
- Binary operations
- Equalities
- **Application nodes** (`f x y`)
- Unary negation
- Complex expressions (`a + a = 2 * a`)
- Proof term creation

## Result

✅ Now you can create let-binding claims and start proofs without errors!

The TT term will be properly constructed for any expression type that the UI parser can generate.
