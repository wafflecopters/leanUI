import { registerNatImpl, registerNatOp, registerOfNat, registerOfRat, registerRatImpl, registerRatOp, type DefinitionsMap } from './term';
import type { CompiledBlock } from './compile-types';

/**
 * Apply @impl/@ofNat/@ofRat/@natAdd/... annotations from a single compiled
 * block. This is kept separate from the top-level driver so both full and
 * incremental compilation can share one registration path.
 */
export function applyImplAnnotationsForBlock(block: CompiledBlock, definitions: DefinitionsMap): void {
  const implRegex = /^@impl=([a-zA-Z][a-zA-Z0-9_]*)$/;
  for (const decl of block.declarations) {
    if (!decl.syntax || !decl.name) continue;
    const trimmed = decl.syntax.trim();

    const m = trimmed.match(implRegex);
    if (m) {
      const role = m[1];
      if (role === 'nat') {
        const err = registerNatImpl(definitions, decl.name);
        if (err) console.warn(`@impl=nat verification failed for '${decl.name}': ${err}`);
      } else if (role === 'rat') {
        const err = registerRatImpl(definitions, decl.name);
        if (err) console.warn(`@impl=rat verification failed for '${decl.name}': ${err}`);
      }
      continue;
    }

    if (trimmed === '@ofNat') {
      const err = registerOfNat(definitions, decl.name);
      if (err) console.warn(`@ofNat verification failed for '${decl.name}': ${err}`);
      continue;
    }

    if (trimmed === '@ofRat') {
      const err = registerOfRat(definitions, decl.name);
      if (err) console.warn(`@ofRat verification failed for '${decl.name}': ${err}`);
      continue;
    }

    if (trimmed === '@natAdd') {
      const err = registerNatOp(definitions, decl.name, 'add');
      if (err) console.warn(`@natAdd verification failed for '${decl.name}': ${err}`);
      continue;
    }
    if (trimmed === '@natMul') {
      const err = registerNatOp(definitions, decl.name, 'mul');
      if (err) console.warn(`@natMul verification failed for '${decl.name}': ${err}`);
      continue;
    }

    if (trimmed === '@ratAdd' || trimmed === '@ratMul' || trimmed === '@ratSub') {
      const kind = trimmed === '@ratAdd' ? 'add' : trimmed === '@ratMul' ? 'mul' : 'sub';
      const err = registerRatOp(definitions, decl.name, kind);
      if (err) console.warn(`${trimmed} verification failed for '${decl.name}': ${err}`);
      continue;
    }
  }
}

/**
 * Apply impl annotations across all compiled blocks.
 */
export function applyImplAnnotations(blocks: CompiledBlock[], definitions: DefinitionsMap): void {
  for (const block of blocks) {
    applyImplAnnotationsForBlock(block, definitions);
  }
}
