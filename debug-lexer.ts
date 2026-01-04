import { Lexer } from './src/parser/tt-parser';

const blockSource = `inductive Nat : Type where
  Zero : Na
  Succ : Nat -> Nat`;

const lexer = new Lexer(blockSource);
const tokens = [];

let token = lexer.next();
while (token.type !== 'EOF') {
  tokens.push(token);
  token = lexer.next();
}

console.log('Tokens with line numbers:');
tokens.forEach((tok, i) => {
  if (tok.value === 'Na' || tok.value === 'Zero' || tok.value === 'Succ') {
    console.log(`Token ${i}: ${tok.type} "${tok.value}" at line ${tok.line}, col ${tok.col}`);
  }
});
