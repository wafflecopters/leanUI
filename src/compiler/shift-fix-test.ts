import { parseExpr } from '../parser/parser';

// Test countLeadingImplicitParams logic
const type = parseExpr('{a b : Nat} -> (p q : Leq a b) -> Equal p q');
console.log('Parsed type:', JSON.stringify(type, null, 2));

function countLeadingImplicitParams(type: any): number {
  let count = 0;
  let current = type;

  while (true) {
    if (current.tag === 'Binder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      console.log(`Binder ${current.name}: named=${isNamed}`);
      if (!isNamed) break;
      count++;
      current = current.body;
    } else if (current.tag === 'MultiBinder' && current.binderKind.tag === 'BPiTT') {
      const isNamed = !!(current as any).named;
      console.log(`MultiBinder ${current.names}: named=${isNamed}`);
      if (!isNamed) break;
      count += current.names.length;
      current = current.body;
    } else {
      break;
    }
  }

  return count;
}

const implicitCount = countLeadingImplicitParams(type);
console.log('Implicit parameter count:', implicitCount);
console.log('Expected: 2 (for {a b})');
