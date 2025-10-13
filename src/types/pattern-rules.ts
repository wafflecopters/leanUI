// Pattern-based rule definitions for algebraic transformations

import {
  EnhancedFocusRule,
  ExpressionNode,
  Assumption,
  ProofContext,
  createPatternRule,
  parseExpressionToAST,
  astToString,
  substituteVariableInExpression
} from './enhanced-focus';

// Comprehensive real number rules
export const ENHANCED_FOCUS_RULES: EnhancedFocusRule[] = [
  // Equality rules (work at top level)
  createPatternRule({
    id: 'symmetry',
    name: 'Symmetry',
    description: 'a = b \\implies b = a',
    category: 'equality',
    nodeType: 'equality',
    from: ['=', 'a', 'b'],
    to: ['=', 'b', 'a']
  }),

  // Arithmetic commutativity
  createPatternRule({
    id: 'add_comm',
    name: 'Addition Commutativity',
    description: 'a + b = b + a',
    category: 'arithmetic',
    from: ['+', 'a', 'b'],
    to: ['+', 'b', 'a']
  }),

  createPatternRule({
    id: 'mul_comm',
    name: 'Multiplication Commutativity',
    description: 'a \\cdot b = b \\cdot a',
    category: 'arithmetic',
    from: ['*', 'a', 'b'],
    to: ['*', 'b', 'a']
  }),

  // Associativity rules
  createPatternRule({
    id: 'add_assoc_left',
    name: 'Addition Associativity (Left)',
    description: '(a + b) + c = a + (b + c)',
    category: 'arithmetic',
    from: ['+', ['+', 'a', 'b'], 'c'],
    to: ['+', 'a', ['+', 'b', 'c']],
    bidirectional: true,
    reverseName: 'Addition Associativity (Right)',
    reverseDescription: 'a + (b + c) = (a + b) + c'
  }),

  createPatternRule({
    id: 'mul_assoc_left',
    name: 'Multiplication Associativity (Left)',
    description: '(a \\cdot b) \\cdot c = a \\cdot (b \\cdot c)',
    category: 'arithmetic',
    from: ['*', ['*', 'a', 'b'], 'c'],
    to: ['*', 'a', ['*', 'b', 'c']],
    bidirectional: true,
    reverseName: 'Multiplication Associativity (Right)',
    reverseDescription: 'a \\cdot (b \\cdot c) = (a \\cdot b) \\cdot c'
  }),

  // Distribution - using simple variables to ensure factor consistency
  createPatternRule({
    id: 'distribute_mul_left',
    name: 'Left Distributivity',
    description: 'a \\cdot (b + c) = a \\cdot b + a \\cdot c',
    category: 'algebraic',
    from: ['*', 'a', ['+', 'b', 'c']],
    to: ['+', ['*', 'a', 'b'], ['*', 'a', 'c']],
    bidirectional: true,
    reverseName: 'Factor Left',
    reverseDescription: 'a \\cdot b + a \\cdot c = a \\cdot (b + c)'
  }),

  createPatternRule({
    id: 'distribute_mul_right',
    name: 'Right Distributivity',
    description: '(a + b) \\cdot c = \\, a \\cdot c + b \\cdot c',
    category: 'algebraic',
    from: ['*', ['+', 'a', 'b'], 'c'],
    to: ['+', ['*', 'a', 'c'], ['*', 'b', 'c']],
    bidirectional: true,
    reverseName: 'Factor Right',
    reverseDescription: 'a \\cdot c + b \\cdot c = (a + b) \\cdot c'
  }),

  createPatternRule({
    id: 'distribute_mul_left_sub',
    name: 'Left Distributivity (Subtraction)',
    description: 'a \\cdot (b - c) = a \\cdot b - a \\cdot c',
    category: 'algebraic',
    from: ['*', 'a', ['-', 'b', 'c']],
    to: ['-', ['*', 'a', 'b'], ['*', 'a', 'c']],
    bidirectional: true,
    reverseName: 'Factor Left (Subtraction)',
    reverseDescription: 'a \\cdot b - a \\cdot c = a \\cdot (b - c)'
  }),

  createPatternRule({
    id: 'factor_from_fraction',
    name: 'Factor from Fraction Numerator',
    description: '(a \\cdot b) / c = a \\cdot (b / c)',
    category: 'algebraic',
    from: ['/', ['*', 'a', 'b'], 'c'],
    to: ['*', 'a', ['/', 'b', 'c']],
    bidirectional: true,
    reverseName: 'Combine into Fraction',
    reverseDescription: 'a \\cdot (b / c) = (a \\cdot b) / c'
  }),

  createPatternRule({
    id: 'combine_fractions',
    name: 'Combine Fractions',
    description: '\\frac{a}{c} + \\frac{b}{c} = \\frac{a + b}{c}',
    category: 'algebraic',
    from: ['+', ['/', 'a', 'c'], ['/', 'b', 'c']],
    to: ['/', ['+', 'a', 'b'], 'c'],
    bidirectional: true,
    reverseName: 'Split Fraction',
    reverseDescription: '\\frac{a + b}{c} = \\frac{a}{c} + \\frac{b}{c}'
  }),

  createPatternRule({
    id: 'combine_fractions_sub',
    name: 'Combine Fractions (Subtraction)',
    description: '\\frac{a}{c} - \\frac{b}{c} = \\frac{a - b}{c}',
    category: 'algebraic',
    from: ['-', ['/', 'a', 'c'], ['/', 'b', 'c']],
    to: ['/', ['-', 'a', 'b'], 'c'],
    bidirectional: true,
    reverseName: 'Split Fraction (Subtraction)',
    reverseDescription: '\\frac{a - b}{c} = \\frac{a}{c} - \\frac{b}{c}'
  }),

  // Substitution rules with parameters
  createPatternRule({
    id: 'add_both_sides',
    name: 'Add to Both Sides',
    description: 'a = b \\implies a + c = b + c',
    category: 'substitution',
    nodeType: 'equality',
    from: ['=', 'a', 'b'],
    to: ['=', ['+', 'a', 'c'], ['+', 'b', 'c']]
  }),

  createPatternRule({
    id: 'subtract_both_sides',
    name: 'Subtract from Both Sides',
    description: 'a = b \\implies a - c = b - c',
    category: 'substitution',
    nodeType: 'equality',
    from: ['=', 'a', 'b'],
    to: ['=', ['-', 'a', 'c'], ['-', 'b', 'c']]
  }),

  createPatternRule({
    id: 'multiply_both_sides',
    name: 'Multiply Both Sides',
    description: 'a = b \\implies a \\cdot c = b \\cdot c',
    category: 'substitution',
    nodeType: 'equality',
    from: ['=', 'a', 'b'],
    to: ['=', ['*', 'a', 'c'], ['*', 'b', 'c']]
  }),

  // Division (note: user should ensure c ≠ 0)
  createPatternRule({
    id: 'divide_both_sides',
    name: 'Divide Both Sides',
    description: 'a = b \\implies a/c = b/c',
    category: 'introduction',
    nodeType: 'equality',
    from: ['=', 'a', 'b'],
    to: ['=', ['/', 'a', 'c'], ['/', 'b', 'c']]
  }),

  // Zero and identity properties
  createPatternRule({
    id: 'div_self',
    name: 'Division by Self',
    description: 'x/x = 1 (\\text{where} x \\neq 0)',
    category: 'arithmetic',
    from: ['/', 'x', 'x'],
    to: 1,
    bidirectional: true,
    reverseName: 'Expand One as Fraction',
    reverseDescription: '1 = \\frac{x}{x}\\, \\text{ (specify $x$)}'
  }),

  createPatternRule({
    id: 'sub_self',
    name: 'Subtraction by Self',
    description: 'a - a = 0',
    category: 'arithmetic',
    from: ['-', 'a', 'a'],
    to: 0,
    bidirectional: true,
    reverseName: 'Expand Zero as Difference',
    reverseDescription: '0 = a - a\\, \\text{ (specify $a$)}'
  }),

  createPatternRule({
    id: 'sub_as_add_neg',
    name: 'Subtraction as Addition',
    description: 'a - b = a + (-b)',
    category: 'arithmetic',
    from: ['-', 'a', 'b'],
    to: ['+', 'a', ['-', 'b']],
    bidirectional: true,
    reverseName: 'Addition as Subtraction',
    reverseDescription: 'a + (-b) = a - b'
  }),

  // Derivative limit definition rule (using Lean's hasDerivAt_iff_tendsto_slope)
  {
    id: 'deriv_limit_def',
    name: 'Derivative Limit Definition',
    description: 'dg/dx = lim_{h→0} [g(x+h)-g(x)]/h (using hasDerivAt_iff_tendsto_slope)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Limit to Derivative',
    reverseDescription: 'lim_{h→0} [g(x+h)-g(x)]/h = dg/dx',

    isApplicableToFocus: (node) => {
      // Check if this is a derivative expression: deriv g x
      if (!node || node.type !== 'application' || !node.children || node.children.length < 3) return false;
      return node.children[0]?.type === 'variable' && node.children[0]?.value === 'deriv';
    },

    isApplicableReverse: (node) => {
      // Check if this is a limit expression that looks like derivative definition
      if (!node || node.type !== 'application' || !node.children || node.children.length < 4) return false;

      // Must be a limit
      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'limit') return false;

      // Must be limit with h → 0
      const variable = node.children[2];
      const approach = node.children[3];
      if (variable?.type !== 'variable' || variable.value !== 'h') return false;
      if (approach?.type !== 'literal' || approach.value !== 0) return false;

      // The function should be a fraction: [...] / h
      const func = node.children[1];
      if (func.type !== 'binop' || func.operator !== '/') return false;

      const denominator = func.children[1];
      if (denominator?.type !== 'variable' || denominator.value !== 'h') return false;

      // The numerator should be a difference: g(x+h) - g(x)
      const numerator = func.children[0];
      if (numerator.type !== 'binop' || numerator.operator !== '-') return false;

      return true;
    },
    applyToFocus: (node) => {
      // Extract function g and variable x from deriv g x
      const g = node.children[1]; // The function being differentiated (e.g., c * f x)
      const x = node.children[2]; // The variable w.r.t. differentiation

      // Create the limit expression: lim_{h→0} [g(x+h)-g(x)]/h
      // This corresponds to Lean's hasDerivAt_iff_tendsto_slope theorem

      // For g(x+h), we need to substitute x+h into the expression g
      // If g = "c * f x", then g(x+h) = "c * f (x+h)"
      const h: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'h',
        children: [],
        raw: 'h'
      };

      const xPlusH: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [x, h],
        raw: `${astToString(x)} + h`
      };

      // Substitute x with (x+h) in the function g to get g(x+h)
      const gAtXPlusH = substituteVariableInExpression(g, astToString(x), xPlusH);

      // g(x) is just the original function g
      const gAtX = g;

      // g(x+h) - g(x) - numerator
      const numerator: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '-',
        children: [gAtXPlusH, gAtX],
        raw: `${astToString(gAtXPlusH)} - ${astToString(gAtX)}`
      };

      // h is already defined above as denominator

      // [g(x+h) - g(x)] / h - the slope
      const slope: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '/',
        children: [numerator, h],
        raw: `(${astToString(numerator)}) / ${astToString(h)}`
      };

      // 0 - the limit point
      const zero: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'literal',
        value: 0,
        children: [],
        raw: '0'
      };

      // lim_{h→0} [g(x+h)-g(x)]/h - the complete limit expression
      const limitExpr: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
          slope,  // the function (slope)
          h,      // the variable (h)
          zero    // the approach point (0)
        ],
        raw: `limit (fun h => (${astToString(numerator)}) / h) h 0`
      };

      const newAssumption: Assumption = {
        id: crypto.randomUUID(),
        name: 'h_deriv_exists',
        expression: `HasDerivAt ${astToString(g)} (deriv ${astToString(g)} ${astToString(x)}) ${astToString(x)}`,
        description: `${astToString(g)} is differentiable at ${astToString(x)} (from hasDerivAt_iff_tendsto_slope)`,
        introducedBy: 'deriv_limit_def'
      };

      return {
        newNode: limitExpr,
        newAssumptions: [newAssumption]
      };
    },

    applyReverse: (node) => {
      // Extract components from limit expression: limit ([g(x+h) - g(x)] / h) h 0
      const func = node.children[1]; // [g(x+h) - g(x)] / h

      const numerator = func.children[0]; // g(x+h) - g(x)
      const rightTerm = numerator.children[1]; // g(x)

      // We need to extract the base function and variable from the difference
      // This is complex because we need to "un-substitute" x+h back to x

      // For now, let's handle the simple case where we can identify the pattern
      // We'll extract the variable from the limit (h) and infer x from the structure

      // Find the main variable (not h) by looking at the right term g(x)
      let mainVariable: ExpressionNode;
      let baseFunction: ExpressionNode;

      // Simple case: if right term is a function application like f(x)
      if (rightTerm.type === 'application' && rightTerm.children.length >= 2) {
        baseFunction = rightTerm.children[0]; // f
        mainVariable = rightTerm.children[1]; // x
      } else {
        // More complex case: extract from the structure
        // For now, assume x as the main variable
        mainVariable = {
          id: crypto.randomUUID(),
          type: 'variable',
          value: 'x',
          children: [],
          raw: 'x'
        };
        baseFunction = rightTerm;
      }

      // Create the derivative expression: deriv baseFunction mainVariable
      const derivativeExpr: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'deriv', children: [], raw: 'deriv' },
          baseFunction,
          mainVariable
        ],
        raw: `deriv ${astToString(baseFunction)} ${astToString(mainVariable)}`
      };

      return {
        newNode: derivativeExpr
      };
    }
  },

  // Limit constant factoring rule
  {
    id: 'limit_const_factor',
    name: 'Limit Constant Factoring',
    description: 'lim_{a→b} n\\cdotg(a) = n \\cdot lim_{a→b} g(a)',
    category: 'algebraic',
    bidirectional: true,
    reverseName: 'Factor into Limit',
    reverseDescription: 'n \\cdot lim_{a→b} g(a) = lim_{a→b} n\\cdot g(a)',

    isApplicableToFocus: (node) => {
      // Check if this is a limit expression: limit (n * g(a)) a b
      if (!node || node.type !== 'application' || !node.children || node.children.length < 4) return false;

      // Must be a limit
      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'limit') return false;

      const func = node.children[1]; // The function inside the limit (should be n * g(a))

      // The function inside the limit must be a multiplication
      return func.type === 'binop' && func.operator === '*';
    },

    isApplicableReverse: (node) => {
      // Check if this is a multiplication: n * limit(g(a), a, b)
      if (!node || node.type !== 'binop' || node.operator !== '*') return false;
      if (!node.children || node.children.length !== 2) return false;

      const limitExpr = node.children[1]; // lim_{a→b} g(a)

      // Second part must be a limit
      if (limitExpr.type !== 'application' || !limitExpr.children || limitExpr.children.length < 4) return false;
      if (limitExpr.children[0]?.type !== 'variable' || limitExpr.children[0]?.value !== 'limit') return false;

      return true;
    },
    applyToFocus: (node) => {
      const limitFunc = node.children[1]; // n * g(a)
      const variable = node.children[2];  // a
      const approach = node.children[3];  // b

      const constant = limitFunc.children[0]; // n
      const innerFunc = limitFunc.children[1]; // g(a)

      // Create lim_{a→b} g(a)
      const innerLimit: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
          innerFunc,
          variable,
          approach
        ],
        raw: `limit ${astToString(innerFunc)} ${astToString(variable)} ${astToString(approach)}`
      };

      // Create n * lim_{a→b} g(a)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '*',
          children: [constant, innerLimit],
          raw: `${astToString(constant)} * (${astToString(innerLimit)})`
        }
      };
    },

    applyReverse: (node) => {
      const constant = node.children[0];     // n
      const limitExpr = node.children[1];   // lim_{a→b} g(a)

      const innerFunc = limitExpr.children[1]; // g(a)
      const variable = limitExpr.children[2];  // a
      const approach = limitExpr.children[3];  // b

      // Create n * g(a)
      const newLimitFunc: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '*',
        children: [constant, innerFunc],
        raw: `${astToString(constant)} * ${astToString(innerFunc)}`
      };

      // Create lim_{a→b} n*g(a)
      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'application',
          children: [
            { id: crypto.randomUUID(), type: 'variable', value: 'limit', children: [], raw: 'limit' },
            newLimitFunc,
            variable,
            approach
          ],
          raw: `limit (${astToString(newLimitFunc)}) ${astToString(variable)} ${astToString(approach)}`
        }
      };
    }
  },

  {
    id: 'subst_from_assumption',
    name: 'Substitute from Assumption',
    description: '\\text{Replace using equality from assumptions}',
    category: 'substitution',
    bidirectional: false,
    isApplicableToFocus: (node, _rootExpression, context) => {
      if (!node) return false;

      const nodeStr = astToString(node);

      return context.assumptions.some(assumption => {
        try {
          const assumptionExpr = parseExpressionToAST(assumption.expression);
          if (assumptionExpr.type !== 'equality' || assumptionExpr.operator !== '=') return false;

          const leftStr = astToString(assumptionExpr.children[0]);
          const rightStr = astToString(assumptionExpr.children[1]);

          return nodeStr === leftStr || nodeStr === rightStr;
        } catch {
          return false;
        }
      });
    },
    applyToFocus: (node, _rootExpression, _params, context?: ProofContext) => {
      if (!context) throw new Error('Context required for substitution');

      const nodeStr = astToString(node);

      // Find the first matching assumption
      for (const assumption of context.assumptions) {
        try {
          const assumptionExpr = parseExpressionToAST(assumption.expression);
          if (assumptionExpr.type !== 'equality' || assumptionExpr.operator !== '=') continue;

          const leftNode = assumptionExpr.children[0];
          const rightNode = assumptionExpr.children[1];
          const leftStr = astToString(leftNode);
          const rightStr = astToString(rightNode);

          if (nodeStr === leftStr) {
            // Replace with right side
            return {
              newNode: {
                ...rightNode,
                id: crypto.randomUUID()
              }
            };
          } else if (nodeStr === rightStr) {
            // Replace with left side
            return {
              newNode: {
                ...leftNode,
                id: crypto.randomUUID()
              }
            };
          }
        } catch {
          continue;
        }
      }

      throw new Error('No matching assumption found');
    }
  },

  {
    id: 'sum_singleton',
    name: 'Singleton Summation',
    description: '\\sum_{i=a}^{a} f(i) = f(a)',
    category: 'algebraic',
    bidirectional: false,
    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'application' || !node.children || node.children.length < 5) return false;

      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'sum') return false;

      const lowerBound = node.children[2];
      const upperBound = node.children[3];

      return astToString(lowerBound) === astToString(upperBound);
    },
    applyToFocus: (node) => {
      const variable = node.children[1];
      const bound = node.children[2];
      const expression = node.children[4];

      const substituted = substituteVariableInExpression(
        expression,
        astToString(variable),
        bound
      );

      return {
        newNode: substituted
      };
    }
  },

  {
    id: 'sum_split',
    name: 'Split Summation',
    description: '\\sum_{i=a}^{b+c} f(i) = \\sum_{i=a}^{b} f(i) + \\sum_{i=b+1}^{b+c} f(i)',
    category: 'algebraic',
    bidirectional: false,
    isApplicableToFocus: (node) => {
      if (!node || node.type !== 'application' || !node.children || node.children.length < 5) return false;

      if (node.children[0]?.type !== 'variable' || node.children[0]?.value !== 'sum') return false;

      const upperBound = node.children[3];
      return upperBound.type === 'binop' && upperBound.operator === '+';
    },
    applyToFocus: (node) => {
      const variable = node.children[1];
      const lowerBound = node.children[2];
      const upperBound = node.children[3];
      const expression = node.children[4];

      const b = upperBound.children[0];

      const bPlusOne: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        children: [
          b,
          {
            id: crypto.randomUUID(),
            type: 'literal',
            value: 1,
            children: [],
            raw: '1'
          }
        ],
        raw: `${astToString(b)} + 1`
      };

      const firstSum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'sum', children: [], raw: 'sum' },
          variable,
          lowerBound,
          b,
          expression
        ],
        raw: `sum ${astToString(variable)} ${astToString(lowerBound)} ${astToString(b)} ${astToString(expression)}`
      };

      const secondSum: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'application',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'sum', children: [], raw: 'sum' },
          variable,
          bPlusOne,
          upperBound,
          expression
        ],
        raw: `sum ${astToString(variable)} ${astToString(bPlusOne)} ${astToString(upperBound)} ${astToString(expression)}`
      };

      return {
        newNode: {
          id: crypto.randomUUID(),
          type: 'binop',
          operator: '+',
          children: [firstSum, secondSum],
          raw: `${astToString(firstSum)} + ${astToString(secondSum)}`
        }
      };
    }
  },

  // Pattern-based rules for identity and algebraic simplifications
  createPatternRule({
    id: 'add_zero_left',
    name: 'Add Zero (Left)',
    description: '0 + a = a',
    category: 'arithmetic',
    from: ['+', 0, 'a'],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Zero (Left)',
    reverseDescription: 'a = 0 + a'
  }),

  createPatternRule({
    id: 'add_zero_right',
    name: 'Add Zero (Right)',
    description: 'a + 0 = a',
    category: 'arithmetic',
    from: ['+', 'a', 0],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Zero (Right)',
    reverseDescription: 'a = a + 0'
  }),

  createPatternRule({
    id: 'mul_zero_left',
    name: 'Multiply by Zero (Left)',
    description: '0 \\cdot a = 0',
    category: 'arithmetic',
    from: ['*', 0, 'a'],
    to: 0
  }),

  createPatternRule({
    id: 'mul_zero_right',
    name: 'Multiply by Zero (Right)',
    description: 'a \\cdot 0 = 0',
    category: 'arithmetic',
    from: ['*', 'a', 0],
    to: 0
  }),

  createPatternRule({
    id: 'mul_one_left',
    name: 'Multiply by One (Left)',
    description: '1 \\cdot a = a',
    category: 'arithmetic',
    from: ['*', 1, 'a'],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce One (Left)',
    reverseDescription: 'a = 1 \\cdot a'
  }),

  createPatternRule({
    id: 'mul_one_right',
    name: 'Multiply by One (Right)',
    description: 'a \\cdot 1 = a',
    category: 'arithmetic',
    from: ['*', 'a', 1],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce One (Right)',
    reverseDescription: 'a = a \\cdot 1'
  }),

  createPatternRule({
    id: 'exponent_one',
    name: 'Exponent of One',
    description: 'a^1 = a',
    from: ['^', 'a', 1],
    to: 'a',
    bidirectional: true,
    reverseName: 'Introduce Exponent One',
    reverseDescription: 'a = a^1'
  }),

  // Exponent product rule: a^b * a^c = a^(b+c)
  createPatternRule({
    id: 'exponent_product',
    name: 'Exponent Product Rule',
    description: 'a^b \\cdot a^c = a^{b+c}',
    category: 'algebraic',
    from: ['*', ['^', 'a', 'b'], ['^', 'a', 'c']],
    to: ['^', 'a', ['+', 'b', 'c']],
    bidirectional: true,
    reverseName: 'Split Exponent',
    reverseDescription: 'a^{b+c} = a^b \\cdot a^c'
  }),

  // Constant simplification rules
  createPatternRule({
    id: 'constant_simplification_add',
    name: 'Simplify Constants (Addition)',
    description: '\\text{Evaluate addition on constants}',
    category: 'algebraic',
    from: ['+',
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' },
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' }
    ],
    to: {
      type: 'compute', fn: (bindings) => {
        const values = Array.from(bindings.values()).filter(n => n.type === 'literal');
        if (values.length >= 2) {
          const leftVal = (values[0].value as number);
          const rightVal = (values[1].value as number);
          return {
            id: crypto.randomUUID(),
            type: 'literal',
            value: leftVal + rightVal,
            children: [],
            raw: String(leftVal + rightVal)
          };
        }
        throw new Error('Invalid constant simplification');
      }
    }
  }),

  createPatternRule({
    id: 'constant_simplification_sub',
    name: 'Simplify Constants (Subtraction)',
    description: 'Evaluate subtraction on constants',
    category: 'algebraic',
    from: ['-',
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' },
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' }
    ],
    to: {
      type: 'compute', fn: (bindings) => {
        const values = Array.from(bindings.values()).filter(n => n.type === 'literal');
        if (values.length >= 2) {
          const leftVal = (values[0].value as number);
          const rightVal = (values[1].value as number);
          return {
            id: crypto.randomUUID(),
            type: 'literal',
            value: leftVal - rightVal,
            children: [],
            raw: String(leftVal - rightVal)
          };
        }
        throw new Error('Invalid constant simplification');
      }
    }
  }),

  createPatternRule({
    id: 'constant_simplification_mul',
    name: 'Simplify Constants (Multiplication)',
    description: 'Evaluate multiplication on constants',
    category: 'algebraic',
    from: ['*',
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' },
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' }
    ],
    to: {
      type: 'compute', fn: (bindings) => {
        const values = Array.from(bindings.values()).filter(n => n.type === 'literal');
        if (values.length >= 2) {
          const leftVal = (values[0].value as number);
          const rightVal = (values[1].value as number);
          return {
            id: crypto.randomUUID(),
            type: 'literal',
            value: leftVal * rightVal,
            children: [],
            raw: String(leftVal * rightVal)
          };
        }
        throw new Error('Invalid constant simplification');
      }
    }
  }),

  createPatternRule({
    id: 'constant_simplification_div',
    name: 'Simplify Constants (Division)',
    description: 'Evaluate division on constants',
    category: 'algebraic',
    from: ['/',
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' },
      { type: 'literal', check: (n) => n.type === 'literal' && typeof n.value === 'number' && n.value !== 0 }
    ],
    to: {
      type: 'compute', fn: (bindings) => {
        const values = Array.from(bindings.values()).filter(n => n.type === 'literal');
        if (values.length >= 2) {
          const leftVal = (values[0].value as number);
          const rightVal = (values[1].value as number);
          return {
            id: crypto.randomUUID(),
            type: 'literal',
            value: leftVal / rightVal,
            children: [],
            raw: String(leftVal / rightVal)
          };
        }
        throw new Error('Invalid constant simplification');
      }
    }
  })
];