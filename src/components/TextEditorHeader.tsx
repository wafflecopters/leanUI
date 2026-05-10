import React from 'react';

const styles = {
  header: {
    padding: '16px 20px',
    color: '#c9d1d9',
    borderBottom: '1px solid #30363d',
    flexShrink: 0,
    display: 'flex' as const,
    justifyContent: 'space-between' as const,
    alignItems: 'center' as const,
  },
  title: {
    margin: 0,
    marginBottom: '4px',
    fontSize: '18px',
    fontWeight: 600,
  },
  subtitle: {
    margin: 0,
    fontSize: '13px',
    color: '#8b949e',
  },
  controls: {
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  },
  button: {
    background: '#21262d',
    color: '#c9d1d9',
    border: '1px solid #30363d',
    borderRadius: '6px',
    padding: '6px 12px',
    fontSize: '13px',
    cursor: 'pointer',
    whiteSpace: 'nowrap' as const,
  },
  activeButton: {
    background: '#238636',
    color: '#ffffff',
    border: '1px solid #238636',
  },
  menuContainer: {
    position: 'relative' as const,
  },
  menu: {
    position: 'absolute' as const,
    right: 0,
    top: '100%',
    marginTop: '4px',
    background: '#161b22',
    border: '1px solid #30363d',
    borderRadius: '6px',
    overflow: 'hidden',
    zIndex: 100,
    minWidth: '180px',
    boxShadow: '0 8px 24px rgba(0,0,0,0.4)',
  },
  menuItem: {
    padding: '8px 16px',
    cursor: 'pointer',
    fontSize: '13px',
    color: '#c9d1d9',
    borderBottom: '1px solid #21262d',
  },
};

export interface TextEditorPreset {
  name: string;
  code: string;
}

export function TextEditorHeader({
  presets,
  showWYSIWYG,
  presetMenuOpen,
  onToggleWYSIWYG,
  onTogglePresetMenu,
  onLoadPreset,
}: {
  presets: TextEditorPreset[];
  showWYSIWYG: boolean;
  presetMenuOpen: boolean;
  onToggleWYSIWYG: () => void;
  onTogglePresetMenu: () => void;
  onLoadPreset: (presetName: string) => void;
}) {
  return (
    <div style={styles.header}>
      <div>
        <h2 style={styles.title}>Text Editor</h2>
        <p style={styles.subtitle}>Edit code and view compilation results</p>
      </div>
      <div style={styles.controls}>
        <button
          onClick={onToggleWYSIWYG}
          style={{
            ...styles.button,
            ...(showWYSIWYG ? styles.activeButton : {}),
          }}
        >
          {showWYSIWYG ? 'Hide WYSIWYG' : 'Show WYSIWYG'}
        </button>
        <div style={styles.menuContainer}>
          <button onClick={onTogglePresetMenu} style={styles.button}>
            Load Preset ▾
          </button>
          {presetMenuOpen && (
            <div style={styles.menu}>
              {presets.map((preset) => (
                <div
                  key={preset.name}
                  onClick={() => onLoadPreset(preset.name)}
                  style={styles.menuItem}
                  onMouseEnter={(event) => {
                    event.currentTarget.style.background = '#30363d';
                  }}
                  onMouseLeave={(event) => {
                    event.currentTarget.style.background = 'transparent';
                  }}
                >
                  {preset.name}
                </div>
              ))}
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
