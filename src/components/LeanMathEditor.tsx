import { useMemo } from 'react';
import { MathEditor } from './MathEditor';
import type { MathEditorState } from '../math-editor/types';
import type { TaggedText } from '../lean/types';
import { codeWithInfosToMathRow } from '../lean/codeWithInfos';

/**
 * Interactive structured math editor seeded from a Lean expression.
 *
 * Converts Lean's tagged pretty-print (`CodeWithInfos`) into the math editor's
 * MathRow model and hands it to the real `MathEditor` — so the user gets the
 * full structured WYSIWYG editing experience (cursor, keyboard, fractions,
 * sub/superscripts, navigation) over a real Lean expression. The editor itself
 * is reused verbatim; only the seed is Lean-derived.
 */
export function LeanMathEditor({
  tagged,
  active = false,
  onChange,
}: {
  tagged?: TaggedText;
  active?: boolean;
  onChange?: (state: MathEditorState) => void;
}) {
  const initialState = useMemo<MathEditorState | undefined>(() => {
    if (!tagged) return undefined;
    const root = codeWithInfosToMathRow(tagged);
    if (root.children.length === 0) return undefined;
    return {
      root,
      cursor: { path: [], offset: root.children.length },
      commandBuffer: null,
      textBuffer: null,
    };
  }, [tagged]);

  if (!initialState) return null;

  return (
    <MathEditor
      // Remount when the underlying Lean expression changes, so a fresh
      // analyze result reseeds the editor rather than stacking on stale state.
      key={initialState.root.id}
      initialState={initialState}
      active={active}
      onChange={onChange}
      showTypeInference={false}
      containerStyle={{ border: 'none', borderRadius: 0, backgroundColor: 'transparent' }}
    />
  );
}
