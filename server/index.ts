import express from 'express';
import cors from 'cors';
import { checkLeanSource, analyzeLeanSource } from './lean-bridge';

const app = express();
const port = Number(process.env.LEAN_BRIDGE_PORT ?? process.env.PORT ?? 3457);

app.use(cors());
app.use(express.json({ limit: '4mb' }));

app.get('/api/health', (_req, res) => {
  res.json({ status: 'ok' });
});

// Milestone 1: run source through real Lean and return diagnostics.
app.post('/api/check', async (req, res) => {
  const source: unknown = req.body?.source;
  const mathlib: boolean = req.body?.mathlib === true;
  if (typeof source !== 'string') {
    res.status(400).json({ error: 'Expected { source: string }' });
    return;
  }
  try {
    const result = await checkLeanSource(source, { mathlib });
    res.json(result);
  } catch (e) {
    res.status(500).json({ error: e instanceof Error ? e.message : String(e) });
  }
});

// Richer analysis: diagnostics + tactic goal states (for goal-at-cursor).
app.post('/api/analyze', async (req, res) => {
  const source: unknown = req.body?.source;
  const mathlib: boolean = req.body?.mathlib === true;
  if (typeof source !== 'string') {
    res.status(400).json({ error: 'Expected { source: string }' });
    return;
  }
  try {
    const result = await analyzeLeanSource(source, { mathlib });
    res.json(result);
  } catch (e) {
    res.status(500).json({ error: e instanceof Error ? e.message : String(e) });
  }
});

app.listen(port, () => {
  console.log(`Lean bridge running on http://localhost:${port}`);
}).on('error', (err) => {
  console.error(`Lean bridge failed to bind port ${port}:`, err.message);
  process.exit(1);
});
