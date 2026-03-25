import { PRESETS } from '../src/presets/index';
import { compileIncrementalTT, compileTTFromText } from '../src/compiler/compile';
import { createIncrementalCache } from '../src/compiler/incremental';

const preset = PRESETS.find(p => p.name === 'Real Analysis');
if (!preset) { console.log('Preset not found'); process.exit(1); }

const code = preset.code;

// 1. Initial full compile (warm the cache)
const cache = createIncrementalCache();
console.log('=== Initial compile ===');
let t0 = performance.now();
const r1 = compileIncrementalTT(code, cache);
let t1 = performance.now();
console.log(`  Time: ${(t1-t0).toFixed(0)}ms, blocks: ${r1.blocks.length}, cached blocks: ${cache.blocks.length}`);

// 2. Recompile identical source (should be instant)
console.log('\n=== Identical source (no change) ===');
t0 = performance.now();
const r2 = compileIncrementalTT(code, cache);
t1 = performance.now();
console.log(`  Time: ${(t1-t0).toFixed(0)}ms`);

// 3. Add newline in the MIDDLE of the file (between blocks)
const lines = code.split('\n');
const midLine = Math.floor(lines.length / 2);
// Find an empty line near the middle
let insertAt = midLine;
for (let i = midLine; i < lines.length; i++) {
  if (lines[i].trim() === '') { insertAt = i; break; }
}
const modifiedLines = [...lines];
modifiedLines.splice(insertAt, 0, '');
const modifiedCode = modifiedLines.join('\n');

console.log(`\n=== Add blank line at line ${insertAt} (middle of file) ===`);
t0 = performance.now();
const r3 = compileIncrementalTT(modifiedCode, cache);
t1 = performance.now();
console.log(`  Time: ${(t1-t0).toFixed(0)}ms, blocks: ${r3.blocks.length}`);

// Check how many blocks were recompiled by comparing cache
let recompiled = 0;
for (let i = 0; i < r3.blocks.length; i++) {
  // A block was recompiled if its cache entry changed
}

// 4. Add newline at the VERY END
const codeWithTrailingNewline = code + '\n';
console.log('\n=== Add newline at end of file ===');
// Reset cache for clean test
const cache2 = createIncrementalCache();
compileIncrementalTT(code, cache2); // warm
t0 = performance.now();
const r4 = compileIncrementalTT(codeWithTrailingNewline, cache2);
t1 = performance.now();
console.log(`  Time: ${(t1-t0).toFixed(0)}ms`);

// 5. Add newline in the BEGINNING
const codeWithLeadingNewline = '\n' + code;
console.log('\n=== Add newline at start of file ===');
const cache3 = createIncrementalCache();
compileIncrementalTT(code, cache3); // warm
t0 = performance.now();
const r5 = compileIncrementalTT(codeWithLeadingNewline, cache3);
t1 = performance.now();
console.log(`  Time: ${(t1-t0).toFixed(0)}ms`);

// 6. Measure just the parse step
console.log('\n=== Parse-only cost ===');
const { parseTTSource } = require('../src/compiler/compile');
t0 = performance.now();
for (let i = 0; i < 10; i++) {
  parseTTSource(code);
}
t1 = performance.now();
console.log(`  10x parse: ${(t1-t0).toFixed(0)}ms (avg ${((t1-t0)/10).toFixed(0)}ms)`);
