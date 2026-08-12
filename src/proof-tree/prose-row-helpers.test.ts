import { describe, expect, test } from 'vitest';
import { splitAnonTuple, existsBinderFromLatex, firstExplicitArg,
  describeApplyProse,
  describeExactProse,
  describeInductionHeader,
  describeRewriteReference,
  extractLemmaAndArgs,
} from './prose-row-helpers';

describe('prose-row-helpers', () => {
  test('extractLemmaAndArgs keeps top-level identifiers and drops nested expressions', () => {
    expect(
      extractLemmaAndArgs(
        'limitExt (\\x => body) (diffQuot g x0) x0 (chainAlgId g f x0 Lg) h',
      ),
    ).toEqual({
      lemma: 'limitExt',
      simpleArgs: ['h'],
    });
  });

  test('describeRewriteReference uses equation mode when unified equation is present', () => {
    expect(
      describeRewriteReference({
        tag: 'rewrite',
        name: 'addComm',
        equationLatex: 'a + b = b + a',
        reverse: true,
      }),
    ).toEqual({
      mode: 'equation',
      theoremName: 'addComm',
      arrowSuffix: ' (←)',
      equationLatex: 'a + b = b + a',
    });
  });

  test('describeRewriteReference falls back to extracted lemma name', () => {
    expect(
      describeRewriteReference({
        tag: 'rewrite',
        name: 'limitExt (\\x => body) h',
      }),
    ).toEqual({
      mode: 'lemma',
      theoremName: 'limitExt',
      arrowSuffix: '',
    });
  });

  test('describeApplyProse recognizes exact-proof compact form', () => {
    expect(
      describeApplyProse({
        tag: 'apply',
        name: 'foo',
        proofExprs: ['δF', 'MkPair(posF, h)'],
      }),
    ).toEqual({
      mode: 'proofExprs',
      proofExprs: ['δF', 'MkPair(posF, h)'],
    });
  });

  test('describeApplyProse distinguishes constructor phrasing and subgoal count', () => {
    expect(
      describeApplyProse({
        tag: 'apply',
        name: 'constructor',
        subgoalLatex: ['A'],
        appliedArgsLatex: ['x'],
      }),
    ).toEqual({
      mode: 'singleSubgoal',
      phrase: 'constructor',
      constructorPhrase: 'by definition',
      appliedArgs: ['x'],
      subgoals: ['A'],
    });

    expect(
      describeApplyProse({
        tag: 'apply',
        name: 'leTrans',
        subgoalLatex: ['A', 'B'],
        appliedArgsLatex: ['h1', 'h2'],
      }),
    ).toEqual({
      mode: 'multiSubgoals',
      phrase: 'theorem',
      theoremName: 'leTrans',
      appliedArgs: ['h1', 'h2'],
      subgoals: ['A', 'B'],
    });
  });

  test('describeInductionHeader chooses cases vs induction wording', () => {
    expect(
      describeInductionHeader({
        tag: 'inductionHeader',
        scrutinee: 'n',
        isCases: true,
      }),
    ).toEqual({
      lead: 'By cases on',
      punctuation: ':',
    });

    expect(
      describeInductionHeader({
        tag: 'inductionHeader',
        scrutinee: 'n',
      }),
    ).toEqual({
      lead: 'We proceed by induction on',
      punctuation: '.',
    });
  });

  test('describeExactProse picks lead, latex source, and error state', () => {
    expect(
      describeExactProse({
        tag: 'exact',
        exprLatex: 'foo\\,x',
        proofExprLatex: 'f(x)',
        solved: true,
        isValueType: true,
      }),
    ).toEqual({
      mode: 'solved',
      lead: 'Take',
      displayLatex: 'f(x)',
    });

    expect(
      describeExactProse({
        tag: 'exact',
        exprLatex: 'limitExt h',
        solved: false,
        error: 'type mismatch',
      }),
    ).toEqual({
      mode: 'error',
      lead: 'By',
      displayLatex: '\\textsf{limitExt}',
      error: 'type mismatch',
    });
  });
});
  test('an anonymous-constructor exact reads as a choice: Take ⟨…⟩', () => {
    const d = describeExactProse({
      tag: 'exact', exprLatex: '⟨vs, h, hind⟩', solved: true,
    } as never);
    expect(d.mode).toBe('solved');
    expect((d as { lead: string }).lead).toBe('Take');
  });

describe('exists-witness tuples', () => {
  test('splitAnonTuple splits top-level commas only', () => {
    expect(splitAnonTuple('⟨[], h, nilIndependent⟩')).toEqual(['[]', 'h', 'nilIndependent']);
    expect(splitAnonTuple('⟨a, ⟨b, c⟩⟩')).toEqual(['a', '⟨b, c⟩']);
    expect(splitAnonTuple('plainTerm')).toBeNull();
  });

  test('existsBinderFromLatex finds the binder, null otherwise', () => {
    expect(existsBinderFromLatex('{\\exists {\\operatorname{bs}},{X}}')).toBe('bs');
    expect(existsBinderFromLatex('0 < x')).toBeNull();
  });
});

describe('firstExplicitArg — what a citation is applied to', () => {
  test('a parenthesized first argument comes back without its parens', () => {
    expect(firstExplicitArg('ih (pre ++ post) (lengthDropLt v pre post vs hvs) h')).toBe('pre ++ post');
  });

  test('a bare-identifier first argument', () => {
    expect(firstExplicitArg('ih ws hw')).toBe('ws');
  });

  test('a bare name has no argument', () => {
    expect(firstExplicitArg('assumption_h')).toBeNull();
    expect(firstExplicitArg('⟨a, b⟩')).toBeNull();
  });

  test('unbalanced parens fail closed', () => {
    expect(firstExplicitArg('ih (pre ++ post')).toBeNull();
  });
});
