import express from 'express';
import cors from 'cors';
import { LeanService } from './lean-service';

const app = express();
const port = 3001;

app.use(cors());
app.use(express.json());

const leanService = new LeanService();

// Initialize Lean service
leanService.start().catch(console.error);

app.post('/api/lean/elaborate', async (req, res) => {
  try {
    const { term } = req.body;
    
    if (!term) {
      return res.status(400).json({ error: 'Term is required' });
    }

    const result = await leanService.elaborate(term);
    res.json(result);
  } catch (error) {
    console.error('Elaboration error:', error);
    res.status(500).json({ 
      error: error instanceof Error ? error.message : 'Unknown error' 
    });
  }
});

app.get('/api/health', (req, res) => {
  res.json({ status: 'ok', lean: leanService ? 'running' : 'stopped' });
});

process.on('SIGINT', () => {
  console.log('Shutting down...');
  leanService.stop();
  process.exit(0);
});

process.on('SIGTERM', () => {
  console.log('Shutting down...');
  leanService.stop();
  process.exit(0);
});

app.listen(port, () => {
  console.log(`Server running on http://localhost:${port}`);
});

export default app;