import { describe, expect, test } from 'vitest';
import { createTCEnv } from './term';
import { TTKTerm } from './kernel';

describe('replaceHolesWithMetas', () => {
  test('holes inside match clauses inherit clause binder context', () => {
    const env = createTCEnv({ options: { mode: 'check' } });
    const term: TTKTerm = {
      tag: 'Match',
      scrutinee: { tag: 'Const', name: 'scrutinee' },
      clauses: [{
        patterns: [],
        namedPatterns: [{ name: 'named', pattern: { tag: 'PVar', name: 'named' } }],
        rhs: { tag: 'Hole', id: 'goal' },
      }],
    };

    const result = env.replaceHolesWithMetas(term);
    expect(result.term.tag).toBe('Match');
    if (result.term.tag !== 'Match') return;

    const rhs = result.term.clauses[0].rhs;
    expect(rhs.tag).toBe('Meta');
    if (rhs.tag !== 'Meta') return;

    const holeMeta = result.env.metaVars.get(rhs.id);
    expect(holeMeta).toBeDefined();
    expect(holeMeta?.ctx).toHaveLength(1);

    const typeMetaId = Array.from(result.env.metaVars.keys()).find(id => id !== rhs.id);
    expect(typeMetaId).toBeDefined();
    expect(typeMetaId ? result.env.metaVars.get(typeMetaId)?.ctx.length : undefined).toBe(1);
  });
});
