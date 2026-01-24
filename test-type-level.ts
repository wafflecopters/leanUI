import { compileSource } from './src/test-utils';

const source = `foo : Type 1
foo = Type`;

const results = compileSource(source);

console.log('Full result:', JSON.stringify(results, null, 2));
