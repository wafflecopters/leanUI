import { elabToKernel } from './types/tt-elab';
import { inferType, extendContext, contextToNames } from './types/tt-typecheck';
import { TTKTerm, TTKContext, prettyPrint } from './types/tt-kernel';
import { mkType, mkPi, mkVar, mkConst, mkApp } from './types/tt-core';

// Build the Equal type manually: (A: Type) -> A -> A -> Type
// Equal : (A: Type) -> A -> A -> Type
const Type = mkType(1);  // Sort 1 = Type
const EqualType = mkPi(
  Type,  // A : Type
  mkPi(
    mkVar(0),  // first A argument (uses de Bruijn index 0 = A)
    mkPi(
      mkVar(1),  // second A argument (de Bruijn index 1 = A after binding the first arg)
      Type,  // result type
      '_'
    ),
    '_'
  ),
  'A'
);

console.log('Equal type:', prettyPrint(elabToKernel(EqualType) as TTKTerm));

// Now build refl: (A : Type) -> (x : A) -> Equal A x x
const EqualConst = mkConst('Equal', EqualType);

// refl : (A : Type) -> (x : A) -> Equal A x x
// In the body, after binding A (idx 1) and x (idx 0):
//   Equal A x x = App(App(App(Equal, Var 1), Var 0), Var 0)
const reflType = mkPi(
  Type,  // A : Type
  mkPi(
    mkVar(0),  // x : A (where A is at index 0)
    mkApp(mkApp(mkApp(EqualConst, mkVar(1)), mkVar(0)), mkVar(0)),  // Equal A x x
    'x'
  ),
  'A'
);

console.log('refl type:', prettyPrint(elabToKernel(reflType) as TTKTerm));

// Now try to type-check refl with Equal in context
const inductiveType = elabToKernel(EqualType) as TTKTerm;
const ctorType = elabToKernel(reflType) as TTKTerm;

const ctx: TTKContext = [{ name: 'Equal', type: inductiveType }];
console.log('\nContext:', ctx.map(b => `${b.name} : ${prettyPrint(b.type)}`));

console.log('\nTrying to infer type of refl constructor...');
try {
  const result = inferType(ctorType, ctx);
  console.log('Result:', prettyPrint(result));
} catch (e: any) {
  console.error('Error:', e.message);
}

// Let's trace step by step
console.log('\n--- Step by step trace ---');

// The ctorType is: (A : Type) -> (x : A) -> Equal A x x
// When we infer its type, we should:
// 1. Check that Type is a type (yes, Type : Type 1)
// 2. In extended context [A : Type], check (x : A) -> Equal A x x
//    - Check that A (Var 0) is a type - but A is a TYPE, not a Type!

console.log('\nStep 1: ctorType.domain (should be Type):', prettyPrint((ctorType as any).domain));
console.log('Step 1: ctorType.domain type:', (ctorType as any).domain.tag);

if (ctorType.tag === 'Binder') {
  const extCtx = extendContext(ctx, 'A', ctorType.domain);
  console.log('\nAfter binding A, context:', extCtx.map(b => `${b.name} : ${prettyPrint(b.type, contextToNames(extCtx))}`));

  // Now the body is: (x : A) -> Equal A x x
  // where A is at index 0
  const body = ctorType.body;
  console.log('\nBody (x : A) -> Equal A x x:', prettyPrint(body, contextToNames(extCtx)));

  if (body.tag === 'Binder') {
    console.log('Body.domain (should be A = Var 0):', prettyPrint(body.domain, contextToNames(extCtx)));
    console.log('Body.domain type:', body.domain.tag);

    // Try to infer the type of body.domain (which is A = Var 0)
    console.log('\nInferring type of body.domain...');
    try {
      const domainType = inferType(body.domain, extCtx);
      console.log('domain type:', prettyPrint(domainType, contextToNames(extCtx)));
    } catch (e: any) {
      console.error('Error inferring domain type:', e.message);
    }

    // Now let's look at the return type: Equal A x x
    const extCtx2 = extendContext(extCtx, 'x', body.domain);
    console.log('\nAfter binding x, context:', extCtx2.map(b => `${b.name} : ${prettyPrint(b.type, contextToNames(extCtx2))}`));

    const returnType = body.body;
    console.log('\nReturn type (Equal A x x):', prettyPrint(returnType, contextToNames(extCtx2)));

    // Let's trace the application structure
    // returnType should be: App(App(App(Equal, A), x), x)
    console.log('\nReturn type structure:');
    let app = returnType;
    let depth = 0;
    while (app.tag === 'App') {
      console.log(`  ${'  '.repeat(depth)}App.arg:`, prettyPrint(app.arg, contextToNames(extCtx2)));
      app = app.fn;
      depth++;
    }
    console.log(`  ${'  '.repeat(depth)}head:`, prettyPrint(app, contextToNames(extCtx2)), `(${app.tag})`);

    // Now try to infer the type of the return type
    console.log('\nInferring type of return type (Equal A x x)...');
    try {
      const returnTypeType = inferType(returnType, extCtx2);
      console.log('Return type type:', prettyPrint(returnTypeType, contextToNames(extCtx2)));
    } catch (e: any) {
      console.error('Error:', e.message);
    }

    // Let's trace the Equal application step by step
    console.log('\n--- Tracing Equal A step by step ---');
    // Equal is a Const with type (A: Type) -> A -> A -> Type
    // In context [x : A, A : Type, Equal : ...]
    // When we apply Equal to A (which is Var 1), we need:
    //   - Equal has type (A: Type) -> A -> A -> Type
    //   - A (Var 1) should have type Type
    // After application, result type should be: A -> A -> Type
    // But with A substituted, it becomes: (Var 1) -> (Var 1) -> Type

    // Let's check Equal's type in this context
    console.log('\nEqual in context extCtx2:');
    // Equal is at index 2 now (x is 0, A is 1, Equal is 2)
    // But wait - Equal is a Const, not a Var!
    console.log('Equal should be looked up as Const...');

    // The head of the application is Equal (Const)
    // returnType = App(App(App(Equal, A), x), x)
    // Let's find Equal
    let head = returnType;
    while (head.tag === 'App') head = head.fn;
    console.log('Head of application:', head.tag, head.tag === 'Const' ? (head as any).name : '');

    if (head.tag === 'Const') {
      console.log('Equal Const type:', prettyPrint((head as any).type, []));
      console.log('\nTrying to infer type of Equal...');
      try {
        const equalType = inferType(head, extCtx2);
        console.log('Equal inferred type:', prettyPrint(equalType, contextToNames(extCtx2)));
      } catch (e: any) {
        console.error('Error:', e.message);
      }
    }

    // Now let's trace the application Equal A step by step
    console.log('\n--- Checking Equal A application ---');
    // returnType = App(App(App(Equal, A), x), x)
    // innerApp1 = App(Equal, A)
    // innerApp2 = App(innerApp1, x)
    // returnType = App(innerApp2, x)

    // Extract App(Equal, A)
    const app3 = returnType as any;
    const app2 = app3.fn as any;
    const app1 = app2.fn as any;  // This is App(Equal, A)

    console.log('App1 (Equal A):', prettyPrint(app1, contextToNames(extCtx2)));
    console.log('App1.fn (Equal):', prettyPrint(app1.fn, contextToNames(extCtx2)));
    console.log('App1.arg (A):', prettyPrint(app1.arg, contextToNames(extCtx2)));

    // When we infer the type of App(Equal, A):
    // 1. Infer type of Equal -> (A : Type) -> A -> A -> Type
    // 2. Check that A has type Type (the domain of the Pi)
    // 3. Substitute A into the body: A -> A -> Type becomes... what?

    console.log('\nInferring type of Equal...');
    const equalInferredType = inferType(app1.fn, extCtx2);
    console.log('Equal type:', prettyPrint(equalInferredType, contextToNames(extCtx2)));

    // The domain should be Type
    if (equalInferredType.tag === 'Binder' && equalInferredType.binderKind.tag === 'BPi') {
      console.log('Domain of Equal (should be Type):', prettyPrint(equalInferredType.domain, contextToNames(extCtx2)));
      console.log('Domain tag:', equalInferredType.domain.tag);

      // Try checking A against the domain
      console.log('\nChecking that A has type', prettyPrint(equalInferredType.domain, contextToNames(extCtx2)));
      console.log('A is:', prettyPrint(app1.arg, contextToNames(extCtx2)), '(type:', app1.arg.tag, ')');

      const argType = inferType(app1.arg, extCtx2);
      console.log('Type of A:', prettyPrint(argType, contextToNames(extCtx2)));

      // Now try inferring the type of Equal A (app1)
      console.log('\n--- Inferring type of Equal A ---');
      try {
        const equalAType = inferType(app1, extCtx2);
        console.log('Type of (Equal A):', prettyPrint(equalAType, contextToNames(extCtx2)));

        // This should be: A -> A -> Type (after substituting A for the first arg)
        // Now let's try the second application: (Equal A) x
        console.log('\n--- Checking (Equal A) x ---');
        console.log('app2:', prettyPrint(app2, contextToNames(extCtx2)));
        console.log('app2.fn:', prettyPrint(app2.fn, contextToNames(extCtx2)));
        console.log('app2.arg:', prettyPrint(app2.arg, contextToNames(extCtx2)));

        // The type of (Equal A) should be A -> A -> Type
        // When we apply to x : A, we should check that x : A matches the domain A
        if (equalAType.tag === 'Binder' && equalAType.binderKind.tag === 'BPi') {
          console.log('\nDomain of (Equal A) (expected type for x):', prettyPrint(equalAType.domain, contextToNames(extCtx2)));
          console.log('Domain tag:', equalAType.domain.tag);

          // x should have type A
          console.log('x is:', prettyPrint(app2.arg, contextToNames(extCtx2)));
          const xType = inferType(app2.arg, extCtx2);
          console.log('Type of x:', prettyPrint(xType, contextToNames(extCtx2)));
        }

        // Try the full second application
        const equalAXType = inferType(app2, extCtx2);
        console.log('\nType of (Equal A x):', prettyPrint(equalAXType, contextToNames(extCtx2)));

      } catch (e: any) {
        console.error('Error inferring Equal A:', e.message);
      }
    }
  }
}
