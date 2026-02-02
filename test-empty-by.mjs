import { parseDeclarations } from './src/parser/parser.js';

const input = `foo : Nat := by`;

try {
  const decls = parseDeclarations(input);
  console.log('Success!', JSON.stringify(decls, null, 2));
} catch (e) {
  console.error('Error name:', e.name);
  console.error('Error message:', e.message);
  if (e.errors && Array.isArray(e.errors)) {
    console.error('\nParse errors:');
    e.errors.forEach((err, i) => {
      console.error(`  ${i + 1}. ${err.message}`);
    });
  }
}
