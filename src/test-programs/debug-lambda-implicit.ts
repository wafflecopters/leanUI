import { compileSource } from '../test-utils';
import * as fs from 'fs';
import * as path from 'path';

const dir = path.dirname(new URL(import.meta.url).pathname);

const imports = [
  'preambles/nat.tt',
  'preambles/equality.tt',
  'preambles/pair.tt',
  'preambles/dpair.tt',
];
const preamble = imports.map(p => fs.readFileSync(path.join(dir, p), 'utf-8')).join('\n');

const testLines = fs.readFileSync(path.join(dir, 'record-lambda-implicit.tt'), 'utf8')
  .split('\n').filter((l: string) => !l.startsWith('@')).join('\n');

const src = preamble + '\n' + testLines;
const results = compileSource(src, { recheckZonkedTerms: false });

for (const block of results) {
  if (block.isComment) continue;

  if (!block.parseSuccess) {
    console.log(`PARSE ERROR in block ${block.blockIndex} "${block.name}":`);
    for (const e of block.parseErrors) console.log(`  ${e.message}`);
  }
  if (!block.nameResolutionSuccess) {
    console.log(`NAME ERROR in block ${block.blockIndex} "${block.name}":`);
    for (const e of block.nameResolutionErrors) console.log(`  ${e.message}`);
  }
  for (const decl of block.declarations) {
    if (!decl.checkSuccess) {
      console.log(`CHECK ERROR in ${decl.name} (block ${block.blockIndex}):`);
      for (const e of (decl.checkErrors || [])) console.log(`  ${e.message}`);
    }
  }
}

const allOk = results.every(r => r.isComment || r.checkSuccess);
console.log('Total success:', allOk);
