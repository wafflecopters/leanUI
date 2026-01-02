import { useState, useEffect } from 'react';
import { BrowserRouter, Routes, Route, useNavigate, useLocation } from 'react-router-dom';
import { EnhancedProofWorkspace } from './components/EnhancedProofWorkspace';
import { InductiveTypeEditor } from './components/InductiveTypeEditor';
import { RecordEditor } from './components/RecordEditor';
import { TextEditorPage } from './components/TextEditorPage';

interface LeanAST {
  [key: string]: any;
}

function AppContent() {
  const navigate = useNavigate();
  const location = useLocation();
  const [mode, setMode] = useState<'ast' | 'proof' | 'inductive' | 'record' | 'text-editor'>('proof');

  // Sync URL to mode state on mount and when URL changes
  useEffect(() => {
    const path = location.pathname;
    if (path === '/text-editor') setMode('text-editor');
    else if (path === '/inductive') setMode('inductive');
    else if (path === '/record') setMode('record');
    else if (path === '/ast') setMode('ast');
    else if (path === '/') setMode('proof');
  }, [location.pathname]);

  // Helper to change mode and update URL
  const handleModeChange = (newMode: typeof mode) => {
    setMode(newMode);
    if (newMode === 'proof') navigate('/');
    else if (newMode === 'text-editor') navigate('/text-editor');
    else if (newMode === 'inductive') navigate('/inductive');
    else if (newMode === 'record') navigate('/record');
    else if (newMode === 'ast') navigate('/ast');
  };
  const [ast, setAst] = useState<LeanAST | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [term, setTerm] = useState(`-- Sum formula: 1 + 2 + ... + n = n(n+1)/2
def sum_range (n : Nat) : Nat := 
  match n with
  | 0 => 0
  | k + 1 => sum_range k + (k + 1)

theorem sum_formula (n : Nat) : 2 * sum_range n = n * (n + 1) := by
  induction n with
  | zero => 
    simp [sum_range]
  | succ k ih =>
    simp [sum_range]
    rw [Nat.mul_add, ih]
    ring`);

  const fetchLeanAST = async () => {
    setLoading(true);
    setError(null);
    try {
      const response = await fetch('/api/lean/elaborate', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ term }),
      });

      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }

      const data = await response.json();
      setAst(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Unknown error');
    } finally {
      setLoading(false);
    }
  };

  if (mode === 'text-editor') {
    return (
      <div>
        <div style={{
          padding: '10px 20px',
          backgroundColor: '#161b22',
          borderBottom: '1px solid #30363d',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center'
        }}>
          <h1 style={{ margin: 0, fontSize: '24px', color: '#c9d1d9' }}>Lean UI - TT Text Editor</h1>
          <div style={{ display: 'flex', gap: '8px' }}>
            <button
              onClick={() => handleModeChange('proof')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#238636',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Proof Assistant
            </button>
            <button
              onClick={() => handleModeChange('inductive')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#1f6feb',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Inductive Types
            </button>
            <button
              onClick={() => handleModeChange('record')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#8957e5',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Records
            </button>
            <button
              onClick={() => handleModeChange('ast')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#6e7681',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              AST Viewer
            </button>
          </div>
        </div>
        <TextEditorPage />
      </div>
    );
  }

  if (mode === 'inductive') {
    return (
      <div>
        <div style={{
          padding: '10px 20px',
          backgroundColor: '#f8f9fa',
          borderBottom: '1px solid #e9ecef',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center'
        }}>
          <h1 style={{ margin: 0, fontSize: '24px' }}>Lean UI - Inductive Type Editor</h1>
          <div style={{ display: 'flex', gap: '8px' }}>
            <button
              onClick={() => handleModeChange('proof')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#007acc',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Proof Assistant
            </button>
            <button
              onClick={() => handleModeChange('text-editor')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#da3633',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Text Editor
            </button>
            <button
              onClick={() => handleModeChange('record')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#2e7d32',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Records
            </button>
            <button
              onClick={() => handleModeChange('ast')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#6c757d',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              AST Viewer
            </button>
          </div>
        </div>
        <InductiveTypeEditor />
      </div>
    );
  }

  if (mode === 'record') {
    return (
      <div>
        <div style={{
          padding: '10px 20px',
          backgroundColor: '#f8f9fa',
          borderBottom: '1px solid #e9ecef',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center'
        }}>
          <h1 style={{ margin: 0, fontSize: '24px' }}>Lean UI - Record Editor</h1>
          <div style={{ display: 'flex', gap: '8px' }}>
            <button
              onClick={() => handleModeChange('proof')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#007acc',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Proof Assistant
            </button>
            <button
              onClick={() => handleModeChange('text-editor')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#da3633',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Text Editor
            </button>
            <button
              onClick={() => handleModeChange('inductive')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#28a745',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Inductive Types
            </button>
            <button
              onClick={() => handleModeChange('ast')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#6c757d',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              AST Viewer
            </button>
          </div>
        </div>
        <RecordEditor />
      </div>
    );
  }

  if (mode === 'proof') {
    return (
      <div>
        <div style={{
          padding: '10px 20px',
          backgroundColor: '#f8f9fa',
          borderBottom: '1px solid #e9ecef',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center'
        }}>
          <h1 style={{ margin: 0, fontSize: '24px' }}>Lean UI - Enhanced Proof Assistant</h1>
          <div style={{ display: 'flex', gap: '8px' }}>
            <button
              onClick={() => handleModeChange('text-editor')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#da3633',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Text Editor
            </button>
            <button
              onClick={() => handleModeChange('inductive')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#28a745',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Inductive Types
            </button>
            <button
              onClick={() => handleModeChange('record')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#2e7d32',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              Records
            </button>
            <button
              onClick={() => handleModeChange('ast')}
              style={{
                padding: '6px 12px',
                backgroundColor: '#6c757d',
                color: 'white',
                border: 'none',
                borderRadius: '4px',
                cursor: 'pointer'
              }}
            >
              AST Viewer
            </button>
          </div>
        </div>
        <EnhancedProofWorkspace />
      </div>
    );
  }

  return (
    <div style={{ padding: '20px', fontFamily: 'monospace' }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: '20px' }}>
        <h1>Lean UI - AST Viewer</h1>
        <div style={{ display: 'flex', gap: '8px' }}>
          <button
            onClick={() => handleModeChange('proof')}
            style={{
              padding: '6px 12px',
              backgroundColor: '#007acc',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer'
            }}
          >
            Proof Assistant
          </button>
          <button
            onClick={() => handleModeChange('text-editor')}
            style={{
              padding: '6px 12px',
              backgroundColor: '#da3633',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer'
            }}
          >
            Text Editor
          </button>
          <button
            onClick={() => handleModeChange('inductive')}
            style={{
              padding: '6px 12px',
              backgroundColor: '#28a745',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer'
            }}
          >
            Inductive Types
          </button>
          <button
            onClick={() => handleModeChange('record')}
            style={{
              padding: '6px 12px',
              backgroundColor: '#2e7d32',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer'
            }}
          >
            Records
          </button>
        </div>
      </div>

      <p style={{ color: '#666', fontSize: '14px' }}>
        Enter a Lean term to elaborate and view its AST structure
      </p>

      <div style={{ marginBottom: '10px' }}>
        <textarea
          value={term}
          onChange={(e) => setTerm(e.target.value)}
          placeholder="Enter Lean term..."
          style={{
            width: '100%',
            height: '200px',
            fontFamily: 'monospace',
            fontSize: '14px',
            padding: '8px',
            border: '1px solid #ccc',
            borderRadius: '4px'
          }}
        />
      </div>

      <button onClick={fetchLeanAST} disabled={loading}>
        {loading ? 'Processing...' : 'Elaborate Lean Term'}
      </button>

      {error && (
        <div style={{ color: 'red', marginTop: '10px' }}>
          Error: {error}
        </div>
      )}

      {ast && (
        <div style={{ marginTop: '20px' }}>
          <h2>AST Result:</h2>
          <pre style={{
            background: '#f5f5f5',
            padding: '10px',
            borderRadius: '4px',
            overflow: 'auto',
            maxHeight: '500px'
          }}>
            {JSON.stringify(ast, null, 2)}
          </pre>
        </div>
      )}
    </div>
  );
}

function App() {
  return (
    <BrowserRouter>
      <Routes>
        <Route path="*" element={<AppContent />} />
      </Routes>
    </BrowserRouter>
  );
}

export default App;