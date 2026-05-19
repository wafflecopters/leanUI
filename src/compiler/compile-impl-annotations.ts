import { registerCarrierBridge, registerCarrierOp, registerCarrierValue, registerIntImpl, registerNatImpl, registerNatOp, registerOfInt, registerOfNat, registerOfRat, registerRatImpl, registerRatOp, registerSimp, type CarrierOp, type DefinitionsMap } from './term';
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
    // Each `@syntax` line on the declaration is concatenated with newlines
    // (see parser.ts). Process each line as an independent annotation so
    // one definition can carry multiple semantic tags (e.g. a notation hint
    // plus a @carrierValue tag).
    for (const line of decl.syntax.split('\n')) {
      const trimmed = line.trim();
      if (!trimmed) continue;
      applyImplAnnotationLine(trimmed, decl.name, definitions, implRegex);
    }
  }
}

function applyImplAnnotationLine(trimmed: string, declName: string, definitions: DefinitionsMap, implRegex: RegExp): void {
  const m = trimmed.match(implRegex);
  if (m) {
    const role = m[1];
    if (role === 'nat') {
      const err = registerNatImpl(definitions, declName);
      if (err) console.warn(`@impl=nat verification failed for '${declName}': ${err}`);
    } else if (role === 'int') {
      const err = registerIntImpl(definitions, declName);
      if (err) console.warn(`@impl=int verification failed for '${declName}': ${err}`);
    } else if (role === 'rat') {
      const err = registerRatImpl(definitions, declName);
      if (err) console.warn(`@impl=rat verification failed for '${declName}': ${err}`);
    }
    return;
  }

  if (trimmed === '@ofNat') {
    const err = registerOfNat(definitions, declName);
    if (err) console.warn(`@ofNat verification failed for '${declName}': ${err}`);
    return;
  }

  if (trimmed === '@ofRat') {
    const err = registerOfRat(definitions, declName);
    if (err) console.warn(`@ofRat verification failed for '${declName}': ${err}`);
    return;
  }

  if (trimmed === '@ofInt') {
    const err = registerOfInt(definitions, declName);
    if (err) console.warn(`@ofInt verification failed for '${declName}': ${err}`);
    return;
  }

  if (trimmed === '@simp') {
    const err = registerSimp(definitions, declName);
    if (err) console.warn(`@simp verification failed for '${declName}': ${err}`);
    return;
  }

  if (trimmed === '@natAdd') {
    const err = registerNatOp(definitions, declName, 'add');
    if (err) console.warn(`@natAdd verification failed for '${declName}': ${err}`);
    return;
  }
  if (trimmed === '@natMul') {
    const err = registerNatOp(definitions, declName, 'mul');
    if (err) console.warn(`@natMul verification failed for '${declName}': ${err}`);
    return;
  }

  if (trimmed === '@ratAdd' || trimmed === '@ratMul' || trimmed === '@ratSub') {
    const kind = trimmed === '@ratAdd' ? 'add' : trimmed === '@ratMul' ? 'mul' : 'sub';
    const err = registerRatOp(definitions, declName, kind);
    if (err) console.warn(`${trimmed} verification failed for '${declName}': ${err}`);
    return;
  }

  // Generic carrier-level arithmetic op registration. Any preset that
  // defines its own +/-/*/neg/inv/div on an abstract "Carrier"-like type
  // can tag the function name with one of these annotations; the
  // norm_num-style suggestion pipeline picks them up without hardcoding
  // names like "radd". Six kinds parallel to the corresponding kernel
  // BigInt-fast-path Rat ops, plus neg/inv/div which the kernel handles
  // via composition (sub = add+neg, div = mul+inv) — but at the suggestion
  // level we want all six as first-class.
  const carrierOpKinds: { tag: string; kind: CarrierOp }[] = [
    { tag: '@carrierAdd', kind: 'add' },
    { tag: '@carrierSub', kind: 'sub' },
    { tag: '@carrierMul', kind: 'mul' },
    { tag: '@carrierNeg', kind: 'neg' },
    { tag: '@carrierInv', kind: 'inv' },
    { tag: '@carrierDiv', kind: 'div' },
  ];
  for (const { tag, kind } of carrierOpKinds) {
    if (trimmed === tag) {
      const err = registerCarrierOp(definitions, declName, kind);
      if (err) console.warn(`${tag} verification failed for '${declName}': ${err}`);
      return;
    }
  }

  // @carrierValue <num>/<den> or @carrierValue <int>
  // Parses "0", "1", "2", "-1", "1/2", "-3/4", etc. into a Rat value
  // and registers the definition as that literal on the Carrier type.
  const cvMatch = trimmed.match(/^@carrierValue\s+(-?\d+)(?:\/(\d+))?$/);
  if (cvMatch) {
    const num = BigInt(cvMatch[1]);
    const den = cvMatch[2] ? BigInt(cvMatch[2]) : 1n;
    const err = registerCarrierValue(definitions, declName, num, den);
    if (err) console.warn(`@carrierValue verification failed for '${declName}': ${err}`);
    return;
  }

  // @carrierBridge: registers a lemma as an alias-→-realOfRat bridge for
  // norm_num. Lemma type should be `Equal (<fn> R) (realOfRat R q)` for
  // some @carrierValue-registered <fn>.
  if (trimmed === '@carrierBridge') {
    const err = registerCarrierBridge(definitions, declName);
    if (err) console.warn(`@carrierBridge verification failed for '${declName}': ${err}`);
    return;
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
