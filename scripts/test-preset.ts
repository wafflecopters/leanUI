import { PRESETS } from '../src/presets/index';
import { compileTTFromText } from '../src/compiler/compile';

const preset = PRESETS.find(p => p.name === 'Real Analysis');
if (preset === undefined) { console.log('Preset not found'); process.exit(1); }

console.log('Compiling real-analysis preset...');
const result = compileTTFromText(preset.code);

const allDecls = result.blocks.flatMap(b => b.declarations);
const errors = allDecls.filter(d => d.checkSuccess !== true);
if (errors.length > 0) {
  console.log('\nERRORS (' + errors.length + '):');
  for (const d of errors) {
    const block = result.blocks.find(b => b.declarations.includes(d));
    const nameErrs = block?.nameResolutionErrors || [];
    console.log('\n  ' + d.name + ':');
    if (nameErrs.length > 0) {
      console.log('    NAME ERRORS: ' + nameErrs.map(e => e.message).join('; '));
    }
    if (d.checkErrors && d.checkErrors.length > 0) {
      for (const ce of d.checkErrors) {
        console.log('    CHECK ERROR: ' + ce.message);
        if (ce.cause) console.log('      CAUSE: ' + (ce.cause as any).message?.slice(0, 300));
      }
    }
  }
} else {
  console.log('\nSUCCESS: ' + allDecls.length + ' declarations compiled');
}
