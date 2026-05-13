/**
 * Tests for record type conversion and type checking.
 */

import { describe, test, expect } from 'vitest';
import { TTKRecordDef, mkPi, mkVar, mkConst, mkApp, mkSort, TTKTerm, mkULit } from './kernel';
import { recordToInductiveDefinition, buildRecordConstructorType, buildRecordType, generateProjections } from './record';

// Helper to create a simple Type_0 sort
const Type0: TTKTerm = mkSort(mkULit(0));

describe('Record to Inductive Conversion', () => {
  describe('buildRecordType', () => {
    test('empty params returns result sort', () => {
      const result = buildRecordType([], Type0);
      expect(result.tag).toBe('Sort');
    });

    test('single param creates Pi type', () => {
      const result = buildRecordType(
        [{ name: 'A', type: Type0 }],
        Type0
      );
      expect(result.tag).toBe('Binder');
      if (result.tag === 'Binder') {
        expect(result.binderKind.tag).toBe('BPi');
        expect(result.name).toBe('A');
        expect(result.domain.tag).toBe('Sort');
        expect(result.body.tag).toBe('Sort');
      }
    });

    test('multiple params creates nested Pis', () => {
      const result = buildRecordType(
        [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        Type0
      );
      // Should be: (A : Type) → (B : Type) → Type
      expect(result.tag).toBe('Binder');
      if (result.tag === 'Binder') {
        expect(result.binderKind.tag).toBe('BPi');
        expect(result.name).toBe('A');
        expect(result.body.tag).toBe('Binder');
        if (result.body.tag === 'Binder') {
          expect(result.body.binderKind.tag).toBe('BPi');
          expect(result.body.name).toBe('B');
          expect(result.body.body.tag).toBe('Sort');
        }
      }
    });
  });

  describe('buildRecordConstructorType', () => {
    test('Point: no params, two fields', () => {
      // record Point where
      //   x : Nat
      //   y : Nat
      // Constructor: (x : Nat) → (y : Nat) → Point
      const result = buildRecordConstructorType(
        'Point',
        [],
        [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      );

      // Should be: (x : Nat) → (y : Nat) → Point
      expect(result.tag).toBe('Binder');
      if (result.tag === 'Binder') {
        expect(result.binderKind.tag).toBe('BPi');
        expect(result.name).toBe('x');
        expect(result.body.tag).toBe('Binder');
        if (result.body.tag === 'Binder') {
          expect(result.body.binderKind.tag).toBe('BPi');
          expect(result.body.name).toBe('y');
          expect(result.body.body.tag).toBe('Const');
          if (result.body.body.tag === 'Const') {
            expect(result.body.body.name).toBe('Point');
          }
        }
      }
    });

    test('Pair: two params, two dependent fields', () => {
      // record Pair (A : Type) (B : Type) where
      //   fst : A      -- A is at index 1 in param context
      //   snd : B      -- B is at index 0 in param context
      // Constructor: (A : Type) → (B : Type) → (fst : A) → (snd : B) → Pair A B
      const result = buildRecordConstructorType(
        'Pair',
        [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        [
          { name: 'fst', type: mkVar(1) }, // A in param context (1 because B is 0)
          { name: 'snd', type: mkVar(0) }  // B in param context
        ]
      );

      // Should be: (A : Type) → (B : Type) → (fst : A) → (snd : B) → Pair A B
      // where A and B in field types are shifted appropriately
      expect(result.tag).toBe('Binder');
      if (result.tag === 'Binder') {
        expect(result.binderKind.tag).toBe('BPi');
        expect(result.name).toBe('A');
        expect(result.body.tag).toBe('Binder');
        if (result.body.tag === 'Binder') {
          expect(result.body.binderKind.tag).toBe('BPi');
          expect(result.body.name).toBe('B');
          expect(result.body.body.tag).toBe('Binder');
          if (result.body.body.tag === 'Binder') {
            expect(result.body.body.binderKind.tag).toBe('BPi');
            expect(result.body.body.name).toBe('fst');
            expect(result.body.body.body.tag).toBe('Binder');
            if (result.body.body.body.tag === 'Binder') {
              expect(result.body.body.body.binderKind.tag).toBe('BPi');
              expect(result.body.body.body.name).toBe('snd');
              // Return type should be Pair A B
              const returnType = result.body.body.body.body;
              expect(returnType.tag).toBe('App');
            }
          }
        }
      }
    });
  });

  describe('recordToInductiveDefinition', () => {
    test('simple Point record', () => {
      const record: TTKRecordDef = {
        name: 'Point',
        constructorName: 'Mk#Point',
        type: Type0,
        params: [],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.name).toBe('Point');
      expect(inductive.type.tag).toBe('Sort');
      expect(inductive.constructors.length).toBe(1);
      expect(inductive.constructors[0].name).toBe('Mk#Point');
      expect(inductive.indexPositions).toEqual([]);
      expect(inductive.recordInfo).toBeDefined();
      expect(inductive.recordInfo?.fieldNames).toEqual(['x', 'y']);
      expect(inductive.recordInfo?.projections).toEqual(['Point.x', 'Point.y']);
      expect(inductive.recordInfo?.isEtaExpandable).toBe(true);
    });

    test('parameterized Pair record', () => {
      const record: TTKRecordDef = {
        name: 'Pair',
        constructorName: 'MkPair',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'fst', type: mkVar(1) },
          { name: 'snd', type: mkVar(0) }
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.name).toBe('Pair');
      expect(inductive.constructors.length).toBe(1);
      expect(inductive.constructors[0].name).toBe('MkPair');

      // namedArgMap is NOT set for the record TYPE - all arguments can be passed positionally
      expect(inductive.namedArgMap).toBeUndefined();

      // namedArgMap IS set for the constructor - all params get auto-inserted holes in applications
      // This is because record params are always inferrable from context/return type
      expect(inductive.constructors[0].namedArgMap).toEqual(new Map([['A', 0], ['B', 1]]));

      // Check record info
      expect(inductive.recordInfo?.fieldNames).toEqual(['fst', 'snd']);
      expect(inductive.recordInfo?.projections).toEqual(['Pair.fst', 'Pair.snd']);
    });

    test('record with implicit field', () => {
      const record: TTKRecordDef = {
        name: 'ImplicitTest',
        constructorName: 'Mk#ImplicitTest',
        type: Type0,
        params: [],
        fields: [
          { name: 'hidden', type: Type0, implicit: true },
          { name: 'visible', type: mkVar(0) }
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.recordInfo?.implicitFields).toEqual([0]); // First field is implicit
    });

    test('custom constructor name is preserved', () => {
      const record: TTKRecordDef = {
        name: 'MyRecord',
        constructorName: 'CustomCtor',
        type: Type0,
        params: [],
        fields: []
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.constructors[0].name).toBe('CustomCtor');
    });

    test('empty record creates unit-like inductive', () => {
      const record: TTKRecordDef = {
        name: 'Empty',
        constructorName: 'Mk#Empty',
        type: Type0,
        params: [],
        fields: []
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.name).toBe('Empty');
      expect(inductive.constructors.length).toBe(1);
      // Constructor type should just be Empty (no args)
      expect(inductive.constructors[0].type.tag).toBe('Const');
      expect(inductive.recordInfo?.fieldNames).toEqual([]);
    });

    test('record with many fields', () => {
      const record: TTKRecordDef = {
        name: 'Many',
        constructorName: 'Mk#Many',
        type: Type0,
        params: [],
        fields: [
          { name: 'a', type: mkConst('Nat') },
          { name: 'b', type: mkConst('Nat') },
          { name: 'c', type: mkConst('Nat') },
          { name: 'd', type: mkConst('Nat') },
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.recordInfo?.fieldNames).toEqual(['a', 'b', 'c', 'd']);
      expect(inductive.recordInfo?.projections).toEqual([
        'Many.a', 'Many.b', 'Many.c', 'Many.d'
      ]);
    });

    test('multiple implicit fields tracked correctly', () => {
      const record: TTKRecordDef = {
        name: 'MultiImplicit',
        constructorName: 'Mk#MultiImplicit',
        type: Type0,
        params: [],
        fields: [
          { name: 'a', type: Type0, implicit: true },
          { name: 'b', type: mkConst('Nat') },
          { name: 'c', type: Type0, implicit: true },
          { name: 'd', type: mkConst('Nat') },
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.recordInfo?.implicitFields).toEqual([0, 2]); // a and c are implicit
    });

    test('index positions always empty for records', () => {
      const record: TTKRecordDef = {
        name: 'Test',
        constructorName: 'Mk#Test',
        type: mkPi(Type0, Type0, 'A'),
        params: [{ name: 'A', type: Type0 }],
        fields: [{ name: 'value', type: mkVar(0) }]
      };

      const inductive = recordToInductiveDefinition(record);

      // Records have no indices, only parameters
      expect(inductive.indexPositions).toEqual([]);
    });

    test('eta expandable flag is true by default', () => {
      const record: TTKRecordDef = {
        name: 'Test',
        constructorName: 'Mk#Test',
        type: Type0,
        params: [],
        fields: []
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.recordInfo?.isEtaExpandable).toBe(true);
    });
  });

  describe('Constructor Type Structure', () => {
    test('constructor type has correct number of arguments', () => {
      // 2 params + 3 fields = 5 Pi binders
      const record: TTKRecordDef = {
        name: 'Test',
        constructorName: 'Mk#Test',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') },
          { name: 'z', type: mkConst('Nat') }
        ]
      };

      const inductive = recordToInductiveDefinition(record);
      const ctorType = inductive.constructors[0].type;

      // Count binders
      let count = 0;
      let current: TTKTerm = ctorType;
      while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
        count++;
        current = current.body;
      }
      expect(count).toBe(5); // A, B, x, y, z
    });

    test('constructor return type is applied record', () => {
      const record: TTKRecordDef = {
        name: 'Pair',
        constructorName: 'Mk#Pair',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'fst', type: mkVar(1) },
          { name: 'snd', type: mkVar(0) }
        ]
      };

      const inductive = recordToInductiveDefinition(record);
      const ctorType = inductive.constructors[0].type;

      // Navigate to return type (skip all Pi binders)
      let current: TTKTerm = ctorType;
      while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
        current = current.body;
      }

      // Return type should be App(App(Pair, A), B)
      expect(current.tag).toBe('App');
      if (current.tag === 'App') {
        expect(current.fn.tag).toBe('App');
        if (current.fn.tag === 'App') {
          expect(current.fn.fn.tag).toBe('Const');
          if (current.fn.fn.tag === 'Const') {
            expect(current.fn.fn.name).toBe('Pair');
          }
        }
      }
    });
  });

  describe('Named Argument Maps', () => {
    // Note: namedArgMap is intentionally NOT set for records.
    // All arguments (params and fields) can be passed positionally.
    // Named argument syntax for records (like {fst := ..., snd := ...}) will be
    // handled separately as record literals in the future.

    test('namedArgMap not set for record types (allows positional params)', () => {
      const record: TTKRecordDef = {
        name: 'Test',
        constructorName: 'Mk#Test',
        type: mkPi(Type0, mkPi(Type0, mkPi(Type0, Type0, 'C'), 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 },
          { name: 'C', type: Type0 }
        ],
        fields: []
      };

      const inductive = recordToInductiveDefinition(record);

      // namedArgMap is undefined, allowing all type parameters to be passed positionally
      expect(inductive.namedArgMap).toBeUndefined();
    });

    test('namedArgMap set for constructor params (but fields are positional)', () => {
      const record: TTKRecordDef = {
        name: 'Test',
        constructorName: 'Mk#Test',
        type: mkPi(Type0, Type0, 'A'),
        params: [{ name: 'A', type: Type0 }],
        fields: [
          { name: 'x', type: mkVar(0) },
          { name: 'y', type: mkVar(0) },
          { name: 'z', type: mkVar(0) }
        ]
      };

      const inductive = recordToInductiveDefinition(record);

      // namedArgMap includes all params - they get auto-inserted holes in applications
      // Fields are still positional (not in namedArgMap)
      expect(inductive.constructors[0].namedArgMap).toEqual(new Map([['A', 0]]));
    });

    test('no named arg map when no params or fields', () => {
      const record: TTKRecordDef = {
        name: 'Empty',
        constructorName: 'Mk#Empty',
        type: Type0,
        params: [],
        fields: []
      };

      const inductive = recordToInductiveDefinition(record);

      expect(inductive.namedArgMap).toBeUndefined();
      expect(inductive.constructors[0].namedArgMap).toBeUndefined();
    });
  });

  describe('Projection Generation', () => {
    test('generates projections for simple record', () => {
      const record: TTKRecordDef = {
        name: 'Point',
        constructorName: 'MkPoint',
        type: Type0,
        params: [],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      };

      const projections = generateProjections(record);

      expect(projections).toHaveLength(2);
      expect(projections[0].name).toBe('Point.x');
      expect(projections[1].name).toBe('Point.y');
    });

    test('projection type for simple record is correct', () => {
      const record: TTKRecordDef = {
        name: 'Point',
        constructorName: 'MkPoint',
        type: Type0,
        params: [],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      };

      const projections = generateProjections(record);
      const xProj = projections[0];

      // Point.x : Point → Nat
      // Should be: (r : Point) → Nat
      expect(xProj.type.tag).toBe('Binder');
      if (xProj.type.tag === 'Binder') {
        expect(xProj.type.binderKind.tag).toBe('BPi');
        expect(xProj.type.name).toBe('r');
        // Domain is Point
        expect(xProj.type.domain.tag).toBe('Const');
        if (xProj.type.domain.tag === 'Const') {
          expect(xProj.type.domain.name).toBe('Point');
        }
        // Codomain is Nat
        expect(xProj.type.body.tag).toBe('Const');
        if (xProj.type.body.tag === 'Const') {
          expect(xProj.type.body.name).toBe('Nat');
        }
      }
    });

    test('projection value for simple record is a lambda with match', () => {
      const record: TTKRecordDef = {
        name: 'Point',
        constructorName: 'MkPoint',
        type: Type0,
        params: [],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      };

      const projections = generateProjections(record);
      const xProj = projections[0];

      // Point.x = λ r. match r with { MkPoint x y => x }
      expect(xProj.value.tag).toBe('Binder');
      if (xProj.value.tag === 'Binder') {
        expect(xProj.value.binderKind.tag).toBe('BLam');
        expect(xProj.value.name).toBe('r');
        expect(xProj.value.body.tag).toBe('Match');
        if (xProj.value.body.tag === 'Match') {
          expect(xProj.value.body.clauses).toHaveLength(1);
          const clause = xProj.value.body.clauses[0];
          expect(clause.patterns[0].tag).toBe('PCtor');
          if (clause.patterns[0].tag === 'PCtor') {
            expect(clause.patterns[0].name).toBe('MkPoint');
            expect(clause.patterns[0].args).toHaveLength(2);
          }
          // RHS should target the x field's constructor position.
          expect(clause.rhs.tag).toBe('Var');
          if (clause.rhs.tag === 'Var') {
            expect(clause.rhs.index).toBe(0);
          }
        }
      }
    });

    test('second field projection returns correct variable', () => {
      const record: TTKRecordDef = {
        name: 'Point',
        constructorName: 'MkPoint',
        type: Type0,
        params: [],
        fields: [
          { name: 'x', type: mkConst('Nat') },
          { name: 'y', type: mkConst('Nat') }
        ]
      };

      const projections = generateProjections(record);
      const yProj = projections[1];

      // Point.y should target the y field's constructor position
      expect(yProj.value.tag).toBe('Binder');
      if (yProj.value.tag === 'Binder' && yProj.value.body.tag === 'Match') {
        const clause = yProj.value.body.clauses[0];
        expect(clause.rhs.tag).toBe('Var');
        if (clause.rhs.tag === 'Var') {
          expect(clause.rhs.index).toBe(0);
        }
      }
    });

    test('generates projections for parameterized record', () => {
      const record: TTKRecordDef = {
        name: 'Pair',
        constructorName: 'MkPair',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'fst', type: mkVar(1) }, // A
          { name: 'snd', type: mkVar(0) }  // B
        ]
      };

      const projections = generateProjections(record);

      expect(projections).toHaveLength(2);
      expect(projections[0].name).toBe('Pair.fst');
      expect(projections[1].name).toBe('Pair.snd');
    });

    test('parameterized projection type has param binders', () => {
      const record: TTKRecordDef = {
        name: 'Pair',
        constructorName: 'MkPair',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'fst', type: mkVar(1) },
          { name: 'snd', type: mkVar(0) }
        ]
      };

      const projections = generateProjections(record);
      const fstProj = projections[0];

      // Pair.fst : (A : Type) → (B : Type) → Pair A B → A
      // Count the Pi binders
      let piCount = 0;
      let current: any = fstProj.type;
      const names: string[] = [];
      while (current.tag === 'Binder' && current.binderKind.tag === 'BPi') {
        piCount++;
        names.push(current.name);
        current = current.body;
      }
      expect(piCount).toBe(3); // A, B, r
      expect(names).toEqual(['A', 'B', 'r']);
    });

    test('parameterized projection value has param lambdas', () => {
      const record: TTKRecordDef = {
        name: 'Pair',
        constructorName: 'MkPair',
        type: mkPi(Type0, mkPi(Type0, Type0, 'B'), 'A'),
        params: [
          { name: 'A', type: Type0 },
          { name: 'B', type: Type0 }
        ],
        fields: [
          { name: 'fst', type: mkVar(1) },
          { name: 'snd', type: mkVar(0) }
        ]
      };

      const projections = generateProjections(record);
      const fstProj = projections[0];

      // Pair.fst = λ A. λ B. λ p. match p with { MkPair a b f s => f }
      // Count the lambda binders
      let lamCount = 0;
      let current: any = fstProj.value;
      while (current.tag === 'Binder' && current.binderKind.tag === 'BLam') {
        lamCount++;
        current = current.body;
      }
      expect(lamCount).toBe(3); // A, B, r

      // The inner body should be a Match
      expect(current.tag).toBe('Match');
      if (current.tag === 'Match') {
        const clause = current.clauses[0];
        // Pattern should have 4 args: 2 params + 2 fields
        if (clause.patterns[0].tag === 'PCtor') {
          expect(clause.patterns[0].args).toHaveLength(4);
        }
        // RHS for fst should target the fst field's constructor position
        expect(clause.rhs.tag).toBe('Var');
        if (clause.rhs.tag === 'Var') {
          expect(clause.rhs.index).toBe(0);
        }
      }
    });

    test('empty record generates no projections', () => {
      const record: TTKRecordDef = {
        name: 'Unit',
        constructorName: 'MkUnit',
        type: Type0,
        params: [],
        fields: []
      };

      const projections = generateProjections(record);
      expect(projections).toHaveLength(0);
    });
  });
});
