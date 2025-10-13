import { parseExpressionToAST } from './types/enhanced-focus';

const expr = parseExpressionToAST('x + (-y)');
console.log('Parsed AST:', JSON.stringify(expr, null, 2));