import { BrowserRouter, Route, Routes } from 'react-router-dom';
import { TextEditorPage } from './components/TextEditorPage';
import { LeanEditorPage } from './components/LeanEditorPage';

export function AppRoutes() {
  return (
    <Routes>
      {/* Lean is now THE editor (default). The legacy TT/TTK page stays at
          /tt-legacy for reference during the migration; removed in M5. */}
      <Route path="/" element={<LeanEditorPage />} />
      <Route path="/lean" element={<LeanEditorPage />} />
      <Route path="/tt-legacy" element={<TextEditorPage />} />
      <Route path="/text-editor" element={<TextEditorPage />} />
      <Route path="*" element={<LeanEditorPage />} />
    </Routes>
  );
}

function App() {
  return (
    <BrowserRouter>
      <AppRoutes />
    </BrowserRouter>
  );
}

export default App;
