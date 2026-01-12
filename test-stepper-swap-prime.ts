import { PatternElabStepper } from './src/types/pattern-elab-stepper';
import { parsePattern } from './src/parser/tt-parser';
import type { TTKClause, TTKTerm } from './src/types/tt-kernel';

// Parse the clause: swap' a f = \x y => f y x
// After parsing with pattern context, this becomes:
// patterns: [PVar('a'), PVar('f')]
// rhs: λ(x:?). λ(y:?). ((#2 #0 #1))  // f y x in context [y, x, f, a]

const patterns = [
  parsePattern('a'),
  parsePattern('f')
];

// Build the RHS manually: \x => \y => f y x
// In the pattern context [f, a], we need:
// f = #0, a = #1
// But the RHS will be typed in a context where x and y are added
// So in [y, x, f, a]: f = #2, y = #0, x = #1
const rhs: TTKTerm = {
  tag: 'Binder',
  name: 'x',
  binderKind: { tag: 'BLam' },
  domain: { tag: 'Hole', id: '_x_type', type: { tag: 'Sort', level: 0 }, context: [] },
  body: {
    tag: 'Binder',
    name: 'y',
    binderKind: { tag: 'BLam' },
    domain: { tag: 'Hole', id: '_y_type', type: { tag: 'Sort', level: 0 }, context: [] },
    body: {
      tag: 'App',
      fn: {
        tag: 'App',
        fn: { tag: 'Var', index: 2 },  // f in context [y, x, f, a]
        arg: { tag: 'Var', index: 0 }  // y
      },
      arg: { tag: 'Var', index: 1 }  // x
    }
  }
};

const clause: TTKClause = { patterns: patterns as any, rhs };

// Function type: (A : Type) -> (f : A -> A -> A) -> (A -> A -> A)
// After extracting argTypes:
// argTypes[0] = Type
// argTypes[1] = (#0 -> (#0 -> #0))  where #0 refers to A from Pi context
// Return type = (#1 -> (#1 -> #1))  where #1 refers to A (skipping f)

const argTypes: TTKTerm[] = [
  { tag: 'Sort', level: 0 },  // Type for A
  {  // (A -> A -> A) for f, where A is #0 in Pi context
    tag: 'Binder',
    name: '_',
    binderKind: { tag: 'BPi' },
    domain: { tag: 'Var', index: 0 },  // A
    body: {
      tag: 'Binder',
      name: '_',
      binderKind: { tag: 'BPi' },
      domain: { tag: 'Var', index: 1 },  // A (shifted)
      body: { tag: 'Var', index: 2 }  // A (shifted)
    }
  }
];

const returnType: TTKTerm = {  // (A -> A -> A)
  tag: 'Binder',
  name: '_',
  binderKind: { tag: 'BPi' },
  domain: { tag: 'Var', index: 1 },  // A (skipping f)
  body: {
    tag: 'Binder',
    name: '_',
    binderKind: { tag: 'BPi' },
    domain: { tag: 'Var', index: 2 },  // A (shifted, skipping x)
    body: { tag: 'Var', index: 3 }  // A (shifted, skipping y, x)
  }
};

const stepper = new PatternElabStepper(clause, argTypes, returnType, [], new Map());

console.log('=== Stepping through swap\' ===\n');
let step = 0;
while (!stepper.isDone() && step < 50) {
  const record = stepper.step();
  console.log(`Step ${step}: [${record.category}] ${record.description}`);
  step++;
}

const final = stepper.getState();
console.log('\n=== Final state ===');
console.log('Phase:', final.phase.tag);
if (final.phase.tag === 'Error') {
  console.log('Error:', final.phase.message);
}
