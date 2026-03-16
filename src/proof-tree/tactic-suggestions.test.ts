import { describe, test, expect } from 'vitest';
import { TTKTerm } from '../compiler/kernel';
import { createDefinitionsMap, addDefinition, MetaVar } from '../compiler/term';
import { collectRewriteCandidates } from './tactic-suggestions';

// ============================================================================
// Helpers
// ============================================================================

/** Make an Equal type: Equal A lhs rhs */
function mkEqual(lhs: TTKTerm, rhs: TTKTerm, typeA: TTKTerm = { tag: 'Const', name: 'Nat' }): TTKTerm {
  return {
    tag: 'App',
    fn: {
      tag: 'App',
      fn: { tag: 'App', fn: { tag: 'Const', name: 'Equal' }, arg: typeA },
      arg: lhs,
    },
    arg: rhs,
  };
}

/** Make a Pi type: (name : domain) -> body */
function mkPi(name: string, domain: TTKTerm, body: TTKTerm): TTKTerm {
  return { tag: 'Binder', binderKind: { tag: 'BPi' as const }, name, domain, body };
}

const nat: TTKTerm = { tag: 'Const', name: 'Nat' };
const zero: TTKTerm = { tag: 'Const', name: 'Zero' };

function mkApp(fn: TTKTerm, arg: TTKTerm): TTKTerm {
  return { tag: 'App', fn, arg };
}

function mkConst(name: string): TTKTerm {
  return { tag: 'Const', name };
}

function mkVar(index: number): TTKTerm {
  return { tag: 'Var', index };
}

// ============================================================================
// Tests for self-referential filtering
// ============================================================================

describe('collectRewriteCandidates', () => {
  test('includes equality definitions as rewrite candidates', () => {
    // Define: plusComm : (n m : Nat) -> Equal (add n m) (add m n)
    let defs = createDefinitionsMap();
    defs = addDefinition(defs, 'plusComm',
      mkPi('n', nat, mkPi('m', nat,
        mkEqual(mkApp(mkApp(mkConst('add'), mkVar(1)), mkVar(0)),
                mkApp(mkApp(mkConst('add'), mkVar(0)), mkVar(1))))),
    );

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(mkApp(mkApp(mkConst('add'), mkConst('a')), mkConst('b')),
                     mkApp(mkApp(mkConst('add'), mkConst('b')), mkConst('a'))),
    };

    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'add' });
    const names = candidates.map(c => c.name);
    expect(names).toContain('plusComm');
  });

  test('filters out self-referential definition when currentDeclName is set', () => {
    // Define: triangleSum : (n : Nat) -> Equal (mul 2 (sum n)) (mul (add n 1) n)
    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    // Also add a different equality
    defs = addDefinition(defs, 'mulComm',
      mkPi('a', nat, mkPi('b', nat,
        mkEqual(mkApp(mkApp(mkConst('mul'), mkVar(1)), mkVar(0)),
                mkApp(mkApp(mkConst('mul'), mkVar(0)), mkVar(1))))),
    );

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), zero)),
                     mkApp(mkApp(mkConst('mul'), mkConst('one')), zero)),
    };

    // Without currentDeclName: triangleSum IS included
    const candidatesWithout = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' });
    const namesWithout = candidatesWithout.map(c => c.name);
    expect(namesWithout).toContain('triangleSum');
    expect(namesWithout).toContain('mulComm');

    // With currentDeclName: triangleSum is FILTERED OUT
    const candidatesWith = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const namesWith = candidatesWith.map(c => c.name);
    expect(namesWith).not.toContain('triangleSum');
    expect(namesWith).toContain('mulComm');
  });

  test('hypothesis-based rewrites are not affected by currentDeclName', () => {
    let defs = createDefinitionsMap();

    // IH in context: Equal (mul 2 (sum n')) (mul (add n' 1) n')
    const ihType = mkEqual(
      mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
      mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
    );

    const goal: MetaVar = {
      ctx: [
        { name: 'n\'', type: nat },
        { name: 'IH', type: ihType },
      ],
      type: mkEqual(mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(1))),
                     mkApp(mkApp(mkConst('mul'), mkConst('one')), mkVar(1))),
    };

    // IH (a hypothesis, not a definition) should still appear even with currentDeclName
    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const names = candidates.map(c => c.name);
    expect(names).toContain('IH');
  });

  test('self-referential candidate allowed in induction case with structural decrease', () => {
    // In the Succ case of induction on n:
    // Context: [n' : Nat, IH : ...]
    // Goal has sum(n') — the smaller argument
    // triangleSum should be allowed because caseTag is set and argument is a Var

    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    const goal: MetaVar = {
      ctx: [
        { name: 'n\'', type: nat },
        { name: 'IH', type: mkEqual(mkConst('lhs'), mkConst('rhs')) },
      ],
      type: mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(1))),
        mkConst('rhs'),
      ),
      caseTag: 'Succ',  // We're inside an induction case
    };

    // Self-reference should be tagged for structural check (not blanket-filtered)
    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const selfRefs = candidates.filter(c => c.name === 'triangleSum');
    // Self-references in induction cases are included but tagged
    expect(selfRefs.length).toBeGreaterThan(0);
    expect(selfRefs[0].isSelfReference).toBe(true);
  });

  test('self-referential candidate rejected outside induction case', () => {
    let defs = createDefinitionsMap();
    const triangleType = mkPi('n', nat,
      mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), mkVar(0))),
        mkApp(mkApp(mkConst('mul'), mkApp(mkApp(mkConst('add'), mkVar(0)), mkConst('one'))), mkVar(0)),
      ),
    );
    defs = addDefinition(defs, 'triangleSum', triangleType);

    const goal: MetaVar = {
      ctx: [],
      type: mkEqual(
        mkApp(mkApp(mkConst('mul'), mkConst('two')), mkApp(mkConst('sum'), zero)),
        mkConst('rhs'),
      ),
      // No caseTag — not inside induction
    };

    const candidates = collectRewriteCandidates(goal, defs, { selectedHead: 'mul' }, 'triangleSum');
    const names = candidates.map(c => c.name);
    expect(names).not.toContain('triangleSum');
  });
});
