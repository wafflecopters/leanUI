/**
 * Parse a Lean tactic block into a ProofNode tree (inverse of proofTreeToLean).
 *
 * Seeds the structured editor from the user's actual Lean proof, so the WYSIWYG
 * shows the existing proof (then the user edits it structurally). This is a
 * pragmatic, indentation-aware parser for the common tactic forms the editor
 * produces and round-trips: intro, exact, rw, simp, unfold, apply, have,
 * suffices, induction/cases … with | ctor params => …, and `sorry` holes.
 *
 * Anything unrecognized becomes an `exact <verbatim>` node so no proof text is
 * silently dropped — it remains visible and editable.
 */
import {
  type ProofNode,
  type CaseNode,
  mkHole,
  mkIntros,
  mkExact,
  mkUnfold,
  mkRewrite,
  mkSimp,
  mkApply,
  mkHave,
  mkSuffices,
  mkInduction,
  mkCase,
  splitCaseParams,
} from '../proof-tree/proof-tree';

interface Line {
  indent: number;
  text: string;
}

function lex(block: string): Line[] {
  const out: Line[] = [];
  for (const raw of block.split('\n')) {
    const trimmedEnd = raw.replace(/\s+$/, '');
    if (trimmedEnd.trim() === '') continue; // skip blank lines
    const indent = trimmedEnd.length - trimmedEnd.trimStart().length;
    out.push({ indent, text: trimmedEnd.trim() });
  }
  return out;
}

/** Parse a chain of sibling tactics at >= `minIndent`, returning a linked ProofNode. */
function parseSeq(lines: Line[], pos: { i: number }, minIndent: number): ProofNode {
  // Collect the consecutive lines at exactly this block's indent (the first one
  // sets the level). Returns the head of the chain; chained tactics nest via
  // their `child`.
  if (pos.i >= lines.length || lines[pos.i].indent < minIndent) {
    return mkHole();
  }
  const level = lines[pos.i].indent;
  return parseChainAt(lines, pos, level);
}

function parseChainAt(lines: Line[], pos: { i: number }, level: number): ProofNode {
  if (pos.i >= lines.length || lines[pos.i].indent !== level) {
    return mkHole();
  }
  const line = lines[pos.i];
  pos.i++;
  const node = parseTactic(lines, pos, level, line.text);
  return node;
}

/** Build the continuation (next sibling at the same level) as a ProofNode. */
function continuation(lines: Line[], pos: { i: number }, level: number): ProofNode {
  if (pos.i < lines.length && lines[pos.i].indent === level) {
    return parseChainAt(lines, pos, level);
  }
  return mkHole();
}

/** Split a `rw [...]` rule list on commas, respecting `←` prefixes. */
function splitRwRules(inner: string): string[] {
  return inner
    .split(',')
    .map((s) => s.trim())
    .filter((s) => s.length > 0);
}

function parseTactic(lines: Line[], pos: { i: number }, level: number, text: string): ProofNode {
  // sorry / hole
  if (text === 'sorry' || text === 'admit') return mkHole();

  // intro a b c   (also `intros`)
  let m = text.match(/^intros?\b\s*(.*)$/);
  if (m) {
    const names = m[1].trim().length ? m[1].trim().split(/\s+/) : [];
    return mkIntros(names, continuation(lines, pos, level));
  }

  // exact <expr>
  m = text.match(/^exact\s+(.*)$/);
  if (m) return mkExact(m[1].trim());

  // Terminal/closing tactics with no args — printed verbatim (NOT `exact <tac>`).
  if (/^(rfl|omega|decide|native_decide|ring|ring_nf|trivial|assumption|ac_rfl|norm_num|simp_all|done)\b\s*$/.test(text)) {
    return mkExact(text.trim(), true);
  }

  // `constructor` opens the goal's constructor and leaves its fields as
  // subgoals (e.g. Limit.mk's eps_delta; DPair's body + witness) — a CHAINING
  // tactic, not a terminal one. `·` bullet branches following it are its
  // subgoal proofs (the printer's multi-subgoal form); otherwise the plain
  // continuation is its single subgoal.
  if (/^constructor\s*$/.test(text)) {
    const branches = parseRewriteBullets(lines, pos, level);
    if (branches.length > 0) return mkApply('constructor', branches, true);
    return mkApply('constructor', [continuation(lines, pos, level)], true);
  }

  // conv in (pat) => rw [lemma]  — a subterm-scoped rewrite.
  m = text.match(/^conv\s+in\s+\((.*)\)\s*=>\s*rw\s*\[\s*(.*?)\s*\]\s*$/);
  if (m) {
    const pattern = m[1].trim();
    const reverse = m[2].startsWith('←') || m[2].startsWith('<-');
    const name = m[2].replace(/^(←|<-)\s*/, '').trim();
    return mkRewrite(name, continuation(lines, pos, level), reverse, undefined, undefined, undefined, pattern);
  }

  // rw [..]  /  rw [← ..]
  m = text.match(/^rw\s*\[\s*(.*?)\s*\]\s*$/);
  if (m) {
    const rules = splitRwRules(m[1]);
    // A single-lemma `rw` followed by `·` bullets is a CONDITIONAL rewrite: the
    // first bullet proves the rewritten goal, the rest its side goals (premises).
    if (rules.length === 1) {
      const saved = pos.i;
      const branches = parseRewriteBullets(lines, pos, level);
      if (branches.length >= 2) {
        const reverse = rules[0].startsWith('←') || rules[0].startsWith('<-');
        const name = rules[0].replace(/^(←|<-)\s*/, '').trim();
        const [main, ...sides] = branches;
        return mkRewrite(name, main, reverse, undefined, undefined, undefined, undefined, sides);
      }
      pos.i = saved; // not the bulleted form — fall through to plain handling
    }
    // `rw [a, ← b, c]` is multiple rewrites; model as a chain of RewriteNodes so
    // each lemma is an editable step and the whole list round-trips.
    const cont = continuation(lines, pos, level);
    let chain = cont;
    for (let r = rules.length - 1; r >= 0; r--) {
      const reverse = rules[r].startsWith('←') || rules[r].startsWith('<-');
      const name = rules[r].replace(/^(←|<-)\s*/, '').trim();
      chain = mkRewrite(name, chain, reverse);
    }
    return rules.length > 0 ? chain : mkRewrite('', cont, false);
  }

  // simp [..]  /  simp only [..]  /  simp
  m = text.match(/^simp\b\s*(only\b)?\s*(?:\[\s*(.*?)\s*\])?\s*$/);
  if (m) {
    const only = !!m[1];
    const lemmas = m[2] ? m[2].split(',').map((s) => s.trim()).filter(Boolean) : [];
    return mkSimp(lemmas, [], continuation(lines, pos, level), only);
  }

  // unfold <name…>  (Lean allows several space-separated names)
  m = text.match(/^unfold\s+(.+?)\s*$/);
  if (m) return mkUnfold(m[1], continuation(lines, pos, level));

  // apply <name>  (children = subsequent deeper lines as one continuation)
  m = text.match(/^apply\s+(.*)$/);
  if (m) {
    // Subgoals appear as following siblings; treat the next sibling chain as the
    // single child proof (apply with one continuation covers the common case).
    return mkApply(m[1].trim(), [continuation(lines, pos, level)]);
  }

  // have h : T := by   |   have h := expr   |   have h : T := expr
  m = text.match(/^have\s+(\S+)\s*(?::\s*(.*?))?\s*:=\s*(by)?\s*(.*)$/);
  if (m) {
    const name = m[1];
    const typeExpr = m[2]?.trim();
    const isBy = m[3] === 'by';
    const tailExpr = m[4]?.trim() ?? '';
    if (isBy) {
      const sub = parseSeq(lines, pos, level + 1);
      return mkHave(name, '', continuation(lines, pos, level), typeExpr, sub);
    }
    return mkHave(name, tailExpr, continuation(lines, pos, level), typeExpr);
  }

  // suffices h : T by  ...
  m = text.match(/^suffices\s+(\S+)\s*:\s*(.*?)\s*by\s*$/);
  if (m) {
    const by = parseSeq(lines, pos, level + 1);
    return mkSuffices(m[1], m[2].trim(), continuation(lines, pos, level), by);
  }

  // induction x with   |   cases x with
  m = text.match(/^(induction|cases)\s+(\S+)\s+with\s*$/);
  if (m) {
    const isCases = m[1] === 'cases';
    const scrutinee = m[2];
    const cases: CaseNode[] = [];
    // Case alternatives are `| ctor params => …` lines at the induction's indent
    // or deeper (our printer aligns them with `induction`; Lean also allows them
    // indented further).
    while (pos.i < lines.length && lines[pos.i].indent >= level && lines[pos.i].text.startsWith('|')) {
      cases.push(parseCase(lines, pos));
    }
    return mkInduction(scrutinee, cases, isCases);
  }

  // Bare `induction x` / `cases x` (no `with`) followed by `·` bullet cases —
  // the form our printer uses when constructor names aren't known. Each `·` (or
  // `.`) bullet at this indent or deeper starts a case body.
  m = text.match(/^(induction|cases)\s+(\S+)\s*$/);
  if (m) {
    const isCases = m[1] === 'cases';
    const scrutinee = m[2];
    const cases: CaseNode[] = [];
    while (
      pos.i < lines.length &&
      lines[pos.i].indent >= level &&
      (lines[pos.i].text === '·' || lines[pos.i].text === '.' || lines[pos.i].text.startsWith('· ') || lines[pos.i].text.startsWith('. '))
    ) {
      cases.push(parseBulletCase(lines, pos));
    }
    // No bullets parsed → keep the bare `induction x` verbatim.
    if (cases.length === 0) return mkExact(text, true);
    return mkInduction(scrutinee, cases, isCases);
  }

  // Fallback: an unrecognized tactic. Keep it as a RAW exact so it prints
  // verbatim (valid Lean) rather than the invalid `exact <tactic>`.
  return mkExact(text, true);
}

function parseCase(lines: Line[], pos: { i: number }): CaseNode {
  const line = lines[pos.i];
  pos.i++;
  const caseLevel = line.indent;
  // `| ctor p1 p2 => [inline tactic]`
  const m = line.text.match(/^\|\s*(\S+)((?:\s+\S+)*?)\s*=>\s*(.*)$/);
  const ctor = m ? m[1] : line.text.replace(/^\|\s*/, '');
  const params = m && m[2].trim().length ? m[2].trim().split(/\s+/) : [];
  const inline = m ? m[3].trim() : '';

  let body: ProofNode;
  if (inline.length > 0) {
    // Inline body: parse it as a single tactic (may itself chain on next lines
    // only if deeper — rare; treat as standalone).
    const innerPos = { i: 0 };
    const innerLines: Line[] = [{ indent: caseLevel + 2, text: inline }];
    body = parseChainAt(innerLines, innerPos, caseLevel + 2);
  } else {
    body = parseSeq(lines, pos, caseLevel + 1);
  }
  // `| succ a a_ih =>` binds both the ctor arg and the induction hypothesis;
  // keep them apart so the label shows `succ a` (not `succ (a, a_ih)`).
  const { args, ihNames } = splitCaseParams(params);
  const node = mkCase(ctor, body, ctor, args);
  return ihNames.length ? { ...node, ihNames } : node;
}

/** Parse a `·` bullet case body. Bullet may be `·` alone (body on next lines)
 *  or `· <inline tactic>`. Label is a placeholder (no constructor name known). */
function parseBulletCase(lines: Line[], pos: { i: number }): CaseNode {
  const line = lines[pos.i];
  pos.i++;
  const caseLevel = line.indent;
  const inline = line.text.replace(/^[·.]\s*/, '').trim();
  let body: ProofNode;
  if (inline.length > 0) {
    const innerPos = { i: 0 };
    body = parseChainAt([{ indent: caseLevel + 2, text: inline }], innerPos, caseLevel + 2);
  } else {
    body = parseSeq(lines, pos, caseLevel + 1);
  }
  // No constructor name (bullet form) — label is a display placeholder only.
  return mkCase('case', body);
}

/** Is this line a `·`/`.` bullet at the given indent? */
function isBulletLine(line: Line, level: number): boolean {
  return line.indent === level &&
    (line.text === '·' || line.text === '.' ||
      line.text.startsWith('· ') || line.text.startsWith('. '));
}

/** Collect consecutive `·` bullet branch bodies at `level` (their bodies live on
 *  following lines indented deeper, or inline after the bullet). Used for a
 *  conditional rewrite's main + side-goal branches. */
function parseRewriteBullets(lines: Line[], pos: { i: number }, level: number): ProofNode[] {
  const branches: ProofNode[] = [];
  while (pos.i < lines.length && isBulletLine(lines[pos.i], level)) {
    const line = lines[pos.i];
    pos.i++;
    const bulletLevel = line.indent;
    const inline = line.text.replace(/^[·.]\s*/, '').trim();
    if (inline.length > 0) {
      const innerPos = { i: 0 };
      branches.push(parseChainAt([{ indent: bulletLevel + 2, text: inline }], innerPos, bulletLevel + 2));
    } else {
      branches.push(parseSeq(lines, pos, bulletLevel + 1));
    }
  }
  return branches;
}

/**
 * Parse a Lean tactic block (the text after `by`) into a ProofNode tree.
 * Returns a single hole for an empty block.
 */
export function leanTacticsToTree(block: string): ProofNode {
  const lines = lex(block);
  if (lines.length === 0) return mkHole();
  const pos = { i: 0 };
  return parseSeq(lines, pos, lines[0].indent);
}
