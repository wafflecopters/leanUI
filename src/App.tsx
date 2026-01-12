import { useState, useEffect } from 'react';
import { BrowserRouter, Routes, Route, useNavigate, useLocation } from 'react-router-dom';
import { EnhancedProofWorkspace } from './components/EnhancedProofWorkspace';
import { InductiveTypeEditor } from './components/InductiveTypeEditor';
import { RecordEditor } from './components/RecordEditor';
import { TextEditorPage } from './components/TextEditorPage';
import { TmpDebugPage } from './components/TmpDebugPage';

function AppContent() {
  const navigate = useNavigate();
  const location = useLocation();
  const [mode, setMode] = useState<'proof' | 'inductive' | 'record' | 'text-editor'>('proof');

  // Sync URL to mode state on mount and when URL changes
  useEffect(() => {
    const path = location.pathname;
    if (path === '/text-editor') setMode('text-editor');
    else if (path === '/inductive') setMode('inductive');
    else if (path === '/record') setMode('record');
    else if (path === '/') setMode('proof');
  }, [location.pathname]);

  // Helper to change mode and update URL
  const handleModeChange = (newMode: typeof mode) => {
    setMode(newMode);
    if (newMode === 'proof') navigate('/');
    else if (newMode === 'text-editor') navigate('/text-editor');
    else if (newMode === 'inductive') navigate('/inductive');
    else if (newMode === 'record') navigate('/record');
  };

  const headerButtonStyle = mode === 'text-editor' ? {
    backgroundColor: '#161b22',
    borderBottom: '1px solid #30363d',
    color: '#c9d1d9',
  } : {
    backgroundColor: '#f8f9fa',
    borderBottom: '1px solid #e9ecef',
    color: '#0d1117',
  }

  const headerButtons = (
    <div style={{
      ...headerButtonStyle,
      padding: '10px 20px',
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
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            color: 'white',
          }}
        >
          Text Editor
        </button>
        <button
          onClick={() => handleModeChange('inductive')}
          style={{
            padding: '6px 12px',
            backgroundColor: '#28a745',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            color: 'white',
          }}
        >
          Inductive Types
        </button>
        <button
          onClick={() => handleModeChange('record')}
          style={{
            padding: '6px 12px',
            backgroundColor: '#2e7d32',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            color: 'white',
          }}
        >
          Records
        </button>
      </div>
    </div>
  );

  const body =
    mode === 'proof' ? <EnhancedProofWorkspace /> :
      mode === 'inductive' ? <InductiveTypeEditor /> :
        mode === 'record' ? <RecordEditor /> :
          mode === 'text-editor' ? <TextEditorPage /> :
            null;

  return (
    <div>
      {headerButtons}
      {body}
    </div>
  );
}

function App() {
  return (
    <BrowserRouter>
      <Routes>
        <Route path="/tmp-debug" element={<TmpDebugPage />} />
        <Route path="*" element={<AppContent />} />
      </Routes>
    </BrowserRouter>
  );
}

export default App;