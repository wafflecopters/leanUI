import { BrowserRouter, Route, Routes } from 'react-router-dom';
import { LeanEditorPage } from './components/LeanEditorPage';

export function AppRoutes() {
  return (
    <Routes>
      {/* Lean IS the editor. The legacy TT/TTK page (and the whole TT engine
          behind it) was deleted in M5 — every route lands here. */}
      <Route path="/" element={<LeanEditorPage />} />
      <Route path="/lean" element={<LeanEditorPage />} />
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
