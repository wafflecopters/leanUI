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
// `priority: true` (goal/display refreshes) jumps the analyze queue ahead of
// background suggestion trials, so the visible goal state never starves.
// `{prefix, body}` (instead of / alongside `source`) opts into the prefix-olean
// fast path: the unchanged prefix compiles once, requests only elaborate `body`.
app.post('/api/analyze', async (req, res) => {
  const rawSource: unknown = req.body?.source;
  const prefix: unknown = req.body?.prefix;
  const body: unknown = req.body?.body;
  const mathlib: boolean = req.body?.mathlib === true;
  const priority: boolean = req.body?.priority === true;
  const hasSplit = typeof prefix === 'string' && typeof body === 'string';
  const source = typeof rawSource === 'string' ? rawSource : hasSplit ? `${prefix}\n${body}` : null;
  if (source === null) {
    res.status(400).json({ error: 'Expected { source: string } or { prefix, body }' });
    return;
  }
  try {
    const result = await analyzeLeanSource(source, {
      mathlib,
      priority,
      ...(hasSplit ? { prefix: prefix as string, body: body as string } : {}),
    });
    // One-line request log — ground truth for "why was X slow" reports.
    console.log(
      `[analyze] pri=${priority ? 1 : 0} prefix=${hasSplit ? 1 : 0} ${result.durationMs}ms${result.bridgeError ? ' ERR' : ''}`,
    );
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
