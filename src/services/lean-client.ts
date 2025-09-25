// Frontend service for communicating with the Lean server
import { ExpressionNode } from '../types/enhanced-focus';

export interface LeanSessionResponse {
  success: boolean;
  sessionId?: string;
  projectPath?: string;
  initResult?: {
    stdout: string;
    stderr: string;
    success: boolean;
  };
  error?: string;
}

export interface LeanCheckResponse {
  success: boolean;
  expression?: string;
  typeInfo?: Array<{
    expression: string;
    type: string;
  }>;
  errors?: string[];
  output?: {
    stdout: string;
    stderr: string;
  };
  error?: string;
}

export class LeanClient {
  private baseUrl: string;
  private currentSessionId: string | null = null;

  constructor(baseUrl: string = 'http://localhost:3001') {
    this.baseUrl = baseUrl;
  }

  // Create a new Lean session
  async createSession(): Promise<LeanSessionResponse> {
    try {
      const response = await fetch(`${this.baseUrl}/api/lean/session`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
      });

      const result = await response.json();

      if (result.success && result.sessionId) {
        this.currentSessionId = result.sessionId;
      }

      return result;
    } catch (error) {
      return {
        success: false,
        error: `Failed to create session: ${error}`
      };
    }
  }

  // Check an expression with Lean
  async checkExpression(
    expression: string,
    assumptions: string[] = []
  ): Promise<LeanCheckResponse> {
    if (!this.currentSessionId) {
      throw new Error('No active session. Create a session first.');
    }

    try {
      const response = await fetch(`${this.baseUrl}/api/lean/check`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          sessionId: this.currentSessionId,
          expression,
          assumptions
        }),
      });

      return await response.json();
    } catch (error) {
      return {
        success: false,
        error: `Failed to check expression: ${error}`
      };
    }
  }

  // Clean up the current session
  async cleanupSession(): Promise<void> {
    if (!this.currentSessionId) {
      return;
    }

    try {
      await fetch(`${this.baseUrl}/api/lean/session/${this.currentSessionId}`, {
        method: 'DELETE',
      });
    } catch (error) {
      console.warn('Failed to cleanup session:', error);
    } finally {
      this.currentSessionId = null;
    }
  }

  // Check if server is available
  async checkHealth(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/health`);
      const result = await response.json();
      return result.status === 'ok';
    } catch (error) {
      return false;
    }
  }

  // Get current session ID
  getCurrentSessionId(): string | null {
    return this.currentSessionId;
  }

  // Parse expression to Lean syntax
  expressionToLeanSyntax(expression: ExpressionNode): string {
    switch (expression.type) {
      case 'application':
        if (expression.children.length >= 1) {
          const func = expression.children[0];

          // Handle derivative: deriv f x
          if (func.type === 'variable' && func.value === 'deriv') {
            if (expression.children.length >= 3) {
              const f = this.expressionToLeanSyntax(expression.children[1]);
              const x = this.expressionToLeanSyntax(expression.children[2]);
              return `deriv (fun ${x} => ${f}) ${x}`;
            } else if (expression.children.length >= 2) {
              const f = this.expressionToLeanSyntax(expression.children[1]);
              return `deriv ${f} x`;
            }
          }

          // Handle limit: limit f h 0 (derivative limit definition)
          if (func.type === 'variable' && func.value === 'limit') {
            if (expression.children.length >= 4) {
              const slope = this.expressionToLeanSyntax(expression.children[1]); // [g(x+h)-g(x)]/h
              const variable = this.expressionToLeanSyntax(expression.children[2]); // h
              const approach = this.expressionToLeanSyntax(expression.children[3]); // 0

              // Convert to Lean's limit syntax using Filter.Tendsto
              // This corresponds to hasDerivAt_iff_tendsto_slope theorem
              return `Filter.Tendsto (fun ${variable} => ${slope}) (nhdsWithin ${approach} {${approach}}ᶜ) (nhds (deriv g x))`;
            }
          }

          // Handle regular function application
          const funcStr = this.expressionToLeanSyntax(func);
          const args = expression.children.slice(1)
            .map(child => this.expressionToLeanSyntax(child))
            .join(' ');
          return args ? `${funcStr} ${args}` : funcStr;
        }
        return expression.raw;

      case 'binop':
        if (expression.children.length === 2 && expression.operator) {
          const left = this.expressionToLeanSyntax(expression.children[0]);
          const right = this.expressionToLeanSyntax(expression.children[1]);

          switch (expression.operator) {
            case '*':
              return `${left} * ${right}`;
            case '+':
              return `${left} + ${right}`;
            case '-':
              return `${left} - ${right}`;
            case '/':
              return `${left} / ${right}`;
            case '^':
              return `${left} ^ ${right}`;
            case '=':
              return `${left} = ${right}`;
            default:
              return `${left} ${expression.operator} ${right}`;
          }
        }
        return expression.raw;

      case 'unop':
        if (expression.children.length === 1) {
          const operand = this.expressionToLeanSyntax(expression.children[0]);
          return `${expression.operator}${operand}`;
        }
        return expression.raw;

      case 'literal':
        return String(expression.value);

      case 'variable':
        return String(expression.value);

      default:
        return expression.raw;
    }
  }

  // Convert our assumptions to Lean variable declarations
  assumptionsToLeanVariables(assumptions: Array<{ name: string; expression: string }>): string[] {
    return assumptions.map(assumption => {
      // Convert types from our notation to Lean notation
      let leanType = assumption.expression;

      // Handle function types: f : ℝ → ℝ
      if (leanType.includes('ℝ → ℝ')) {
        return `(${assumption.name} : ℝ → ℝ)`;
      }

      // Handle basic types: c : ℝ
      if (leanType === 'ℝ') {
        return `(${assumption.name} : ℝ)`;
      }

      return `(${assumption.name} : ${leanType})`;
    });
  }
}

// Global instance
export const leanClient = new LeanClient();