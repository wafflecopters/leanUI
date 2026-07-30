import { describe, expect, test } from 'vitest';
import { ProseItem, ProseItemKind } from './proof-prose';
import {
  buildProseGoalLead,
  findLastInteractiveGoalStepIndex,
  findNextHoleNodeId,
  proseItemCanAnchorInteractiveGoal,
  proseItemShowsVisibleGoal,
  visibleLatexLength,
} from './prose-view-helpers';

function makeItem(nodeId: number, kind: ProseItemKind, isCursor = false): ProseItem {
  return { nodeId, kind, isCursor, depth: 0 };
}

describe('prose-view-helpers', () => {
  test('proseItemShowsVisibleGoal tracks only prose-visible goal kinds', () => {
    expect(proseItemShowsVisibleGoal({ tag: 'intro', latex: '', goalLatex: 'A' })).toBe(true);
    expect(proseItemShowsVisibleGoal({ tag: 'have', name: 'h', expr: 'x', goalLatex: 'B' })).toBe(true);
    expect(proseItemShowsVisibleGoal({ tag: 'apply', name: 'f', subgoalLatex: ['C'] })).toBe(true);
    expect(proseItemShowsVisibleGoal({ tag: 'apply', name: 'f', subgoalLatex: ['C', 'D'] })).toBe(false);
    expect(proseItemShowsVisibleGoal({ tag: 'calcChain', steps: [] })).toBe(true);
    expect(proseItemShowsVisibleGoal({ tag: 'fold', name: 'foo', goalLatex: 'E' })).toBe(false);
    expect(proseItemShowsVisibleGoal({ tag: 'exact', exprLatex: 'proof', solved: true, goalLatex: 'F' })).toBe(false);
  });

  test('proseItemCanAnchorInteractiveGoal matches goal-bearing cursor steps', () => {
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'unfold', name: 'foo' })).toBe(true);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'rewrite', name: 'bar' })).toBe(true);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'simp', lemmas: [], stepCount: 0 })).toBe(true);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'intro', latex: '', goalLatex: 'A' })).toBe(true);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'intro', latex: '' })).toBe(false);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'apply', name: 'f' })).toBe(true);
    expect(proseItemCanAnchorInteractiveGoal({ tag: 'have', name: 'h', expr: 'x' })).toBe(false);
  });

  test('findLastInteractiveGoalStepIndex stops at structural boundaries', () => {
    const beforeBoundary = [
      makeItem(1, { tag: 'intro', latex: '', goalLatex: 'A' }),
      makeItem(2, { tag: 'caseHeader', labelLatex: 'Zero', isBaseCase: true }),
      makeItem(3, { tag: 'hole', goalLatex: 'B' }, true),
    ];
    expect(findLastInteractiveGoalStepIndex(beforeBoundary)).toBe(-1);

    const withAnchor = [
      makeItem(4, { tag: 'have', name: 'h', expr: 'x', goalLatex: 'A' }),
      makeItem(5, { tag: 'apply', name: 'f', subgoalLatex: ['B'] }),
      makeItem(6, { tag: 'hole', goalLatex: 'C' }, true),
    ];
    expect(findLastInteractiveGoalStepIndex(withAnchor)).toBe(1);
  });

  test('findNextHoleNodeId stops at structural boundaries', () => {
    const items = [
      makeItem(7, { tag: 'intro', latex: '', goalLatex: 'A' }),
      makeItem(8, { tag: 'hole', goalLatex: 'B' }),
      makeItem(9, { tag: 'inductionHeader', scrutinee: 'n' }),
      makeItem(10, { tag: 'hole', goalLatex: 'C' }),
    ];
    expect(findNextHoleNodeId(items, 0)).toBe(8);
    expect(findNextHoleNodeId(items, 2)).toBe(10);
    expect(findNextHoleNodeId(items, 1)).toBeUndefined();
  });

  test('buildProseGoalLead chooses lead text and inline threshold', () => {
    expect(buildProseGoalLead(undefined)).toBeNull();
    expect(buildProseGoalLead('Nat', true)).toEqual({
      goalLatex: 'Nat',
      lead: 'We must choose a value of type',
      inline: true,
    });
    expect(buildProseGoalLead('A'.repeat(31), false)).toEqual({
      goalLatex: 'A'.repeat(31),
      lead: 'We must show',
      inline: false,
    });
  });

  test('inline threshold measures VISIBLE glyphs, not latex markup', () => {
    // `ℝ` renders as one glyph but its latex is 31 chars of htmlId wrapper —
    // it must inline. (The regression: every goal rendered as a display block.)
    expect(visibleLatexLength('\\htmlId{subexpr:/}{\\mathbb{R} }')).toBe(2);
    expect(buildProseGoalLead('\\htmlId{subexpr:/}{\\mathbb{R} }')!.inline).toBe(true);
    // `0 < ε/2` with nested wrappers stays inline too.
    const eps = '\\htmlId{subexpr:/}{0 < \\htmlId{subexpr:/1}{\\frac{\\varepsilon}{2}}}';
    expect(buildProseGoalLead(eps)!.inline).toBe(true);
    // A genuinely long formula (>30 visible glyphs) still breaks out to display mode.
    expect(visibleLatexLength('|f(g(x)) - f(g(x_0))| < \\varepsilon \\wedge |g(x) - g(x_0)| < \\delta_1')).toBeGreaterThan(30);
    expect(buildProseGoalLead('|f(g(x)) - f(g(x_0))| < \\varepsilon \\wedge |g(x) - g(x_0)| < \\delta_1')!.inline).toBe(false);
    // The row being edited expands regardless of length.
    expect(buildProseGoalLead('\\mathbb{R}', false, 30, true)!.inline).toBe(false);
  });
});
