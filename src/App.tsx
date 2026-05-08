import { BrowserRouter, Route, Routes } from 'react-router-dom';
import { TextEditorPage } from './components/TextEditorPage';

export function AppRoutes() {
  return (
    <Routes>
      <Route path="/text-editor" element={<TextEditorPage />} />
      <Route path="*" element={<TextEditorPage />} />
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
