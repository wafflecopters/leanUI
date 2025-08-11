// Core types for the proof workspace

export interface Expression {
  id: string;
  type: 'equality' | 'inequality' | 'proposition';
  left?: Expression | string;
  right?: Expression | string;
  operator?: '=' | '<' | '>' | '≤' | '≥' | '+' | '-' | '*' | '/' | '^';
  value?: string | number;
  raw: string; // The original string representation
}

export interface ProofRule {
  id: string;
  name: string;
  description: string;
  type: 'symmetry' | 'transitivity' | 'congruence' | 'substitution' | 'arithmetic' | 'custom';
  // Function to check if rule is applicable to current expression
  isApplicable: (expr: Expression, context?: ProofContext) => boolean;
  // Function to apply the rule and return new expression
  apply: (expr: Expression, params?: any) => ProofStep;
}

export interface ProofStep {
  id: string;
  expression: Expression;
  rule: ProofRule;
  ruleParams?: any; // Parameters used when applying the rule
  previousStep?: string; // ID of previous step
  leanTerm?: string; // Generated Lean proof term
  timestamp: number;
}

export interface ProofContext {
  currentExpression: Expression;
  steps: ProofStep[];
  variables: Map<string, string>; // variable name -> type
  hypotheses: Expression[]; // Available hypotheses
}

export interface ProofWorkspace {
  id: string;
  name: string;
  initialExpression: Expression;
  context: ProofContext;
  goalExpression?: Expression; // What we're trying to prove
}

// Predefined rules
export const PROOF_RULES: ProofRule[] = [
  {
    id: 'symmetry',
    name: 'Symmetry',
    description: 'If a = b, then b = a',
    type: 'symmetry',
    isApplicable: (expr) => expr.type === 'equality',
    apply: (expr) => ({
      id: crypto.randomUUID(),
      expression: {
        ...expr,
        id: crypto.randomUUID(),
        left: expr.right,
        right: expr.left,
        raw: `${expr.right} = ${expr.left}`
      },
      rule: PROOF_RULES.find(r => r.id === 'symmetry')!,
      timestamp: Date.now()
    })
  },
  {
    id: 'add_both_sides',
    name: 'Add to Both Sides',
    description: 'If a = b, then a + c = b + c',
    type: 'congruence',
    isApplicable: (expr) => expr.type === 'equality',
    apply: (expr, params) => {
      const { value } = params;
      const newLeft = `(${expr.left}) + ${value}`;
      const newRight = `(${expr.right}) + ${value}`;
      return {
        id: crypto.randomUUID(),
        expression: {
          ...expr,
          id: crypto.randomUUID(),
          left: newLeft,
          right: newRight,
          raw: `${newLeft} = ${newRight}`
        },
        rule: PROOF_RULES.find(r => r.id === 'add_both_sides')!,
        ruleParams: { value },
        timestamp: Date.now()
      };
    }
  },
  {
    id: 'subtract_both_sides',
    name: 'Subtract from Both Sides',
    description: 'If a = b, then a - c = b - c',
    type: 'congruence',
    isApplicable: (expr) => expr.type === 'equality',
    apply: (expr, params) => {
      const { value } = params;
      const newLeft = `(${expr.left}) - ${value}`;
      const newRight = `(${expr.right}) - ${value}`;
      return {
        id: crypto.randomUUID(),
        expression: {
          ...expr,
          id: crypto.randomUUID(),
          left: newLeft,
          right: newRight,
          raw: `${newLeft} = ${newRight}`
        },
        rule: PROOF_RULES.find(r => r.id === 'subtract_both_sides')!,
        ruleParams: { value },
        timestamp: Date.now()
      };
    }
  },
  {
    id: 'multiply_both_sides',
    name: 'Multiply Both Sides',
    description: 'If a = b, then a * c = b * c',
    type: 'congruence',
    isApplicable: (expr) => expr.type === 'equality',
    apply: (expr, params) => {
      const { value } = params;
      const newLeft = `(${expr.left}) * ${value}`;
      const newRight = `(${expr.right}) * ${value}`;
      return {
        id: crypto.randomUUID(),
        expression: {
          ...expr,
          id: crypto.randomUUID(),
          left: newLeft,
          right: newRight,
          raw: `${newLeft} = ${newRight}`
        },
        rule: PROOF_RULES.find(r => r.id === 'multiply_both_sides')!,
        ruleParams: { value },
        timestamp: Date.now()
      };
    }
  },
  {
    id: 'transitivity',
    name: 'Transitivity',
    description: 'If a = b and b = c, then a = c',
    type: 'transitivity',
    isApplicable: (expr, context) => {
      if (expr.type !== 'equality') return false;
      // Check if there's another equality with matching terms
      return context?.steps.some(step => 
        step.expression.type === 'equality' && (
          step.expression.left === expr.right || 
          step.expression.right === expr.left
        )
      ) || false;
    },
    apply: (expr, params) => {
      const { otherExpression } = params;
      // Determine the transitive result
      let newLeft = expr.left;
      let newRight = otherExpression.right;
      
      if (expr.right === otherExpression.left) {
        newRight = otherExpression.right;
      } else if (expr.right === otherExpression.right) {
        newRight = otherExpression.left;
      } else if (expr.left === otherExpression.left) {
        newLeft = expr.right;
        newRight = otherExpression.right;
      } else if (expr.left === otherExpression.right) {
        newLeft = expr.right;
        newRight = otherExpression.left;
      }
      
      return {
        id: crypto.randomUUID(),
        expression: {
          ...expr,
          id: crypto.randomUUID(),
          left: newLeft,
          right: newRight,
          raw: `${newLeft} = ${newRight}`
        },
        rule: PROOF_RULES.find(r => r.id === 'transitivity')!,
        ruleParams: { otherExpression },
        timestamp: Date.now()
      };
    }
  }
];

// Helper function to parse simple expressions
export function parseExpression(raw: string): Expression {
  const id = crypto.randomUUID();
  
  // Handle equality
  if (raw.includes('=')) {
    const [left, right] = raw.split('=').map(s => s.trim());
    return {
      id,
      type: 'equality',
      left,
      right,
      operator: '=',
      raw
    };
  }
  
  // Handle other operators
  for (const op of ['<', '>', '≤', '≥']) {
    if (raw.includes(op)) {
      const [left, right] = raw.split(op).map(s => s.trim());
      return {
        id,
        type: 'inequality',
        left,
        right,
        operator: op as any,
        raw
      };
    }
  }
  
  // Default to proposition
  return {
    id,
    type: 'proposition',
    value: raw,
    raw
  };
}