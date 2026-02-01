import { compileTTFromFile } from '/Users/arig/Development/leanUI/src/compiler/compile.ts';
import { setPatternLoggingEnabled } from '/Users/arig/Development/leanUI/src/compiler/patterns.ts';

// Enable detailed pattern matching logs
setPatternLoggingEnabled(true);

const result = compileTTFromFile('/Users/arig/Development/leanUI/src/test-programs/implicit-patterns/uip-without-explicit-A.tt');

console.log('\n=== RESULT ===');
if (result.checkSuccess) {
  console.log('SUCCESS');
} else {
  console.log('FAILED:');
  result.errors?.forEach(e => console.log('  ', e.message));
}
