import React from 'react';

export function TextEditorRenderOptions({
  showNamedArgsWithLabels,
  showNamedParamsWithBraces,
  setShowNamedArgsWithLabels,
  setShowNamedParamsWithBraces,
}: {
  showNamedArgsWithLabels: boolean;
  showNamedParamsWithBraces: boolean;
  setShowNamedArgsWithLabels: React.Dispatch<React.SetStateAction<boolean>>;
  setShowNamedParamsWithBraces: React.Dispatch<React.SetStateAction<boolean>>;
}) {
  return (
    <span style={{ marginLeft: 'auto', display: 'flex', gap: '16px', fontSize: '11px', color: '#8b949e' }}>
      <label style={{ display: 'flex', alignItems: 'center', gap: '4px', cursor: 'pointer' }}>
        <input
          type="checkbox"
          checked={showNamedArgsWithLabels}
          onChange={(e) => setShowNamedArgsWithLabels(e.target.checked)}
          style={{ cursor: 'pointer' }}
        />
        Show named args as {'{A:=...}'}
      </label>
      <label style={{ display: 'flex', alignItems: 'center', gap: '4px', cursor: 'pointer' }}>
        <input
          type="checkbox"
          checked={showNamedParamsWithBraces}
          onChange={(e) => setShowNamedParamsWithBraces(e.target.checked)}
          style={{ cursor: 'pointer' }}
        />
        Show named params as {'{A : Type}'}
      </label>
    </span>
  );
}
