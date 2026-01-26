import { describe, test, expect } from 'vitest';
import { TCEnv, createTCEnv, MetaVar } from './term';
import { TTKTerm, mkConst, mkVar, mkApp, mkPi, mkLambda, mkSort, mkLet, TTKClause, mkULit } from './kernel';

describe('zonkTerm', () => {
  // Helper to create a TCEnv with specific metaVars and levelMetas
  function createZonkEnv(
    metaVars: Map<string, MetaVar>,
    levelMetas: Map<string, TTKTerm> = new Map()
  ): TCEnv<TTKTerm> {
    const env = createTCEnv({ options: { mode: 'check' } });
    // Create a new TCEnv with our custom metaVars and levelMetas
    return new (TCEnv as any)(
      env.context,
      env.definitions,
      metaVars,
      env.constraints,
      env.indexPath,
      env.valueStack,
      mkConst('dummy'),
      levelMetas,
      env.options
    );
  }

  // Helper for Type 0
  const type0 = mkSort(mkULit(0));
  const type1 = mkSort(mkULit(1));

  describe('Meta substitution', () => {
    test('solved meta is replaced with its solution', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?m1', {
        ctx: [],
        type: type0,
        solution: mkConst('Nat')
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = { tag: 'Meta', id: '?m1' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkConst('Nat'));
    });

    test('unsolved meta remains unchanged', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?m1', {
        ctx: [],
        type: type0,
        solution: undefined
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = { tag: 'Meta', id: '?m1' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(term);
    });

    test('unknown meta remains unchanged', () => {
      const env = createZonkEnv(new Map());
      const term: TTKTerm = { tag: 'Meta', id: '?unknown' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(term);
    });

    test('nested meta substitution - meta solved to another meta', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?m1', {
        ctx: [],
        type: type0,
        solution: { tag: 'Meta', id: '?m2' }
      });
      metaVars.set('?m2', {
        ctx: [],
        type: type0,
        solution: mkConst('Bool')
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = { tag: 'Meta', id: '?m1' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkConst('Bool'));
    });
  });

  describe('Level meta substitution', () => {
    test('meta solved via levelMetas is replaced', () => {
      const levelMetas = new Map<string, TTKTerm>();
      levelMetas.set('?u1', mkULit(1));

      const env = createZonkEnv(new Map(), levelMetas);
      const term: TTKTerm = { tag: 'Meta', id: '?u1' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkULit(1));
    });

    test('metaVars takes precedence when meta exists in both', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?u1', {
        ctx: [],
        type: type0,
        solution: mkConst('FromMetaVars')
      });

      const levelMetas = new Map<string, TTKTerm>();
      levelMetas.set('?u1', mkULit(42));

      const env = createZonkEnv(metaVars, levelMetas);
      const term: TTKTerm = { tag: 'Meta', id: '?u1' };

      // The current implementation checks metaVars first, then levelMetas
      // This test documents current behavior
      const result = env.zonkTerm(term);
      // metaVars is checked first in the code
      expect(result).toEqual(mkConst('FromMetaVars'));
    });
  });

  describe('Hole substitution', () => {
    test('Hole solved via levelMetas is replaced', () => {
      const levelMetas = new Map<string, TTKTerm>();
      levelMetas.set('hole:u', mkULit(2));

      const env = createZonkEnv(new Map(), levelMetas);
      const term: TTKTerm = { tag: 'Hole', id: 'hole:u' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkULit(2));
    });

    test('Hole solved via metaVars is replaced', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('hole:x', {
        ctx: [],
        type: type0,
        solution: mkConst('SolvedHole')
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = { tag: 'Hole', id: 'hole:x' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkConst('SolvedHole'));
    });

    test('unsolved Hole remains unchanged', () => {
      const env = createZonkEnv(new Map());
      const term: TTKTerm = { tag: 'Hole', id: 'hole:unsolved' };

      const result = env.zonkTerm(term);
      expect(result).toEqual(term);
    });
  });

  describe('Structural terms', () => {
    test('Var is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term = mkVar(3);

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkVar(3));
    });

    test('Const is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term = mkConst('SomeConst');

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkConst('SomeConst'));
    });

    test('Sort is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term = mkSort(mkULit(1));

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkSort(mkULit(1)));
    });

    test('ULevel is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term: TTKTerm = { tag: 'ULevel' };

      const result = env.zonkTerm(term);
      expect(result).toEqual({ tag: 'ULevel' });
    });

    test('ULit is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term = mkULit(5);

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkULit(5));
    });

    test('UOmega is unchanged', () => {
      const env = createZonkEnv(new Map());
      const term: TTKTerm = { tag: 'UOmega' };

      const result = env.zonkTerm(term);
      expect(result).toEqual({ tag: 'UOmega' });
    });
  });

  describe('App zonking', () => {
    test('zonks both fn and arg', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?fn', {
        ctx: [],
        type: type0,
        solution: mkConst('Identity')
      });
      metaVars.set('?arg', {
        ctx: [],
        type: type0,
        solution: mkConst('Zero')
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = mkApp({ tag: 'Meta', id: '?fn' }, { tag: 'Meta', id: '?arg' });

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkApp(mkConst('Identity'), mkConst('Zero')));
    });

    test('nested App zonking', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?x', {
        ctx: [],
        type: type0,
        solution: mkConst('X')
      });

      const env = createZonkEnv(metaVars);
      // f (g ?x)
      const term = mkApp(mkConst('f'), mkApp(mkConst('g'), { tag: 'Meta', id: '?x' }));

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkApp(mkConst('f'), mkApp(mkConst('g'), mkConst('X'))));
    });
  });

  describe('Binder zonking', () => {
    test('zonks Pi domain and body', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?dom', {
        ctx: [],
        type: type1,
        solution: mkConst('Nat')
      });
      metaVars.set('?bod', {
        ctx: [],
        type: type0,
        solution: mkConst('Bool')
      });

      const env = createZonkEnv(metaVars);
      const term = mkPi({ tag: 'Meta', id: '?dom' }, { tag: 'Meta', id: '?bod' }, 'x');

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkPi(mkConst('Nat'), mkConst('Bool'), 'x'));
    });

    test('zonks Lam domain and body', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?dom', {
        ctx: [],
        type: type1,
        solution: mkConst('Nat')
      });

      const env = createZonkEnv(metaVars);
      const term = mkLambda({ tag: 'Meta', id: '?dom' }, mkVar(0), 'x');

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkLambda(mkConst('Nat'), mkVar(0), 'x'));
    });

    test('zonks Let domain, defVal, and body', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?dom', {
        ctx: [],
        type: type1,
        solution: mkConst('Nat')
      });
      metaVars.set('?val', {
        ctx: [],
        type: type0,
        solution: mkConst('Zero')
      });
      metaVars.set('?bod', {
        ctx: [],
        type: type0,
        solution: mkApp(mkConst('Succ'), mkVar(0))
      });

      const env = createZonkEnv(metaVars);
      // mkLet(name, defType, defVal, body)
      const term = mkLet(
        'x',
        { tag: 'Meta', id: '?dom' },
        { tag: 'Meta', id: '?val' },
        { tag: 'Meta', id: '?bod' }
      );

      const result = env.zonkTerm(term);
      expect(result).toEqual(mkLet(
        'x',
        mkConst('Nat'),
        mkConst('Zero'),
        mkApp(mkConst('Succ'), mkVar(0))
      ));
    });
  });

  describe('Annot zonking', () => {
    test('zonks both term and type', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?t', {
        ctx: [],
        type: type0,
        solution: mkConst('Zero')
      });
      metaVars.set('?T', {
        ctx: [],
        type: type1,
        solution: mkConst('Nat')
      });

      const env = createZonkEnv(metaVars);
      const term: TTKTerm = {
        tag: 'Annot',
        term: { tag: 'Meta', id: '?t' },
        type: { tag: 'Meta', id: '?T' }
      };

      const result = env.zonkTerm(term);
      expect(result).toEqual({
        tag: 'Annot',
        term: mkConst('Zero'),
        type: mkConst('Nat')
      });
    });
  });

  describe('Match zonking', () => {
    test('zonks scrutinee', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?scrut', {
        ctx: [],
        type: mkConst('Nat'),
        solution: mkConst('Zero')
      });

      const env = createZonkEnv(metaVars);
      const clauses: TTKClause[] = [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: mkConst('True')
        }
      ];
      const term: TTKTerm = {
        tag: 'Match',
        scrutinee: { tag: 'Meta', id: '?scrut' },
        clauses
      };

      const result = env.zonkTerm(term);
      expect(result.tag).toBe('Match');
      if (result.tag === 'Match') {
        expect(result.scrutinee).toEqual(mkConst('Zero'));
      }
    });

    test('zonks clause rhs', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?result', {
        ctx: [],
        type: mkConst('Bool'),
        solution: mkConst('True')
      });

      const env = createZonkEnv(metaVars);
      const clauses: TTKClause[] = [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: { tag: 'Meta', id: '?result' }
        }
      ];
      const term: TTKTerm = {
        tag: 'Match',
        scrutinee: mkConst('n'),
        clauses
      };

      const result = env.zonkTerm(term);
      expect(result.tag).toBe('Match');
      if (result.tag === 'Match') {
        expect(result.clauses[0].rhs).toEqual(mkConst('True'));
      }
    });

    test('zonks multiple clauses', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?r1', {
        ctx: [],
        type: mkConst('Nat'),
        solution: mkConst('Zero')
      });
      metaVars.set('?r2', {
        ctx: [],
        type: mkConst('Nat'),
        solution: mkApp(mkConst('Succ'), mkVar(0))
      });

      const env = createZonkEnv(metaVars);
      const clauses: TTKClause[] = [
        {
          patterns: [{ tag: 'PCtor', name: 'Zero', args: [] }],
          rhs: { tag: 'Meta', id: '?r1' }
        },
        {
          patterns: [{ tag: 'PCtor', name: 'Succ', args: [{ tag: 'PVar', name: 'n' }] }],
          rhs: { tag: 'Meta', id: '?r2' }
        }
      ];
      const term: TTKTerm = {
        tag: 'Match',
        scrutinee: mkVar(0),
        clauses
      };

      const result = env.zonkTerm(term);
      expect(result.tag).toBe('Match');
      if (result.tag === 'Match') {
        expect(result.clauses[0].rhs).toEqual(mkConst('Zero'));
        expect(result.clauses[1].rhs).toEqual(mkApp(mkConst('Succ'), mkVar(0)));
      }
    });
  });

  describe('Complex nested terms', () => {
    test('deeply nested metas all get zonked', () => {
      const metaVars = new Map<string, MetaVar>();
      metaVars.set('?A', {
        ctx: [],
        type: type1,
        solution: mkConst('Nat')
      });
      metaVars.set('?B', {
        ctx: [],
        type: type1,
        solution: mkConst('Bool')
      });
      metaVars.set('?x', {
        ctx: [],
        type: mkConst('Nat'),
        solution: mkConst('Zero')
      });

      const env = createZonkEnv(metaVars);
      // (\(a : ?A) => \(b : ?B) => ?x) : (?A -> ?B -> ?A)
      const term = mkApp(
        mkLambda(
          { tag: 'Meta', id: '?A' },
          mkLambda(
            { tag: 'Meta', id: '?B' },
            { tag: 'Meta', id: '?x' },
            'b'
          ),
          'a'
        ),
        mkConst('arg')
      );

      const result = env.zonkTerm(term);
      const expected = mkApp(
        mkLambda(
          mkConst('Nat'),
          mkLambda(
            mkConst('Bool'),
            mkConst('Zero'),
            'b'
          ),
          'a'
        ),
        mkConst('arg')
      );
      expect(result).toEqual(expected);
    });
  });
});
