import { compileTTFromText } from '../src/compiler/compile';
import * as fs from 'fs';
import * as path from 'path';

// Read the test file and resolve imports manually
function readTestFile(filePath: string): string {
  const content = fs.readFileSync(filePath, 'utf-8');
  const lines = content.split('\n');
  let result = '';
  for (const line of lines) {
    if (line.startsWith('@import ')) {
      const importPath = line.replace('@import ', '').trim();
      const fullPath = path.join(path.dirname(filePath), importPath);
      result += fs.readFileSync(fullPath, 'utf-8') + '\n';
    } else if (line.startsWith('@')) {
      continue;
    } else {
      result += line + '\n';
    }
  }
  return result;
}

const source = readTestFile('src/test-programs/debug-have-cases.tt');
const result = compileTTFromText(source);
for (const block of result.blocks) {
  for (const decl of block.declarations) {
    if (decl.checkSuccess !== true) {
      console.log(`FAIL: ${decl.name}`);
      for (const err of decl.checkErrors) {
        console.log(`  ${err.message}`);
        if (err.cause) console.log(`    cause: ${(err.cause as any).message?.slice(0, 500)}`);
      }
    }
  }
}
if (result.totalCheckErrors === 0) {
  console.log('ALL PASSED');
}
