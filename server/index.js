const express = require('express');
const cors = require('cors');
const bodyParser = require('body-parser');
const { spawn } = require('child_process');
const fs = require('fs-extra');
const path = require('path');
const { v4: uuidv4 } = require('uuid');

const app = express();
const port = process.env.PORT || 3001;

// Middleware
app.use(cors());
app.use(bodyParser.json());

// Lean project directory for temporary files
const LEAN_PROJECT_DIR = path.join(__dirname, 'lean_projects');
fs.ensureDirSync(LEAN_PROJECT_DIR);

// Base Lean project template with mathlib for calculus
const LEAN_PROJECT_TEMPLATE = {
  'lean-toolchain': 'leanprover/lean4:stable',
  'lakefile.lean': `import Lake
open Lake DSL

package leanui {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LeanUI {
  -- add library configuration options here
}`,
  'LeanUI/Basic.lean': `-- Basic calculus setup for LeanUI
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Setup for our mathematical workspace
variable {f : ℝ → ℝ} {c : ℝ} {x : ℝ}

-- Example theorem we want to prove
theorem deriv_const_mul (hf : Differentiable ℝ f) :
  deriv (fun x => c * f x) = fun x => c * deriv f x := by
  simp [deriv_const_mul, hf]`
};

// Create a new Lean project
async function createLeanProject(projectId) {
  const projectPath = path.join(LEAN_PROJECT_DIR, projectId);

  try {
    await fs.ensureDir(projectPath);

    // Write lean-toolchain file
    await fs.writeFile(
      path.join(projectPath, 'lean-toolchain'),
      LEAN_PROJECT_TEMPLATE['lean-toolchain']
    );

    // Write lakefile
    await fs.writeFile(
      path.join(projectPath, 'lakefile.lean'),
      LEAN_PROJECT_TEMPLATE['lakefile.lean']
    );

    // Create LeanUI directory and basic file
    await fs.ensureDir(path.join(projectPath, 'LeanUI'));
    await fs.writeFile(
      path.join(projectPath, 'LeanUI', 'Basic.lean'),
      LEAN_PROJECT_TEMPLATE['LeanUI/Basic.lean']
    );

    return projectPath;
  } catch (error) {
    console.error('Error creating Lean project:', error);
    throw error;
  }
}

// Execute Lean command in a project
function executeLeanCommand(projectPath, command, args = []) {
  return new Promise((resolve, reject) => {
    // Ensure elan environment is available
    const env = {
      ...process.env,
      PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}`
    };

    const leanProcess = spawn(command, args, {
      cwd: projectPath,
      env: env,
      stdio: ['pipe', 'pipe', 'pipe']
    });

    let stdout = '';
    let stderr = '';

    leanProcess.stdout.on('data', (data) => {
      stdout += data.toString();
    });

    leanProcess.stderr.on('data', (data) => {
      stderr += data.toString();
    });

    leanProcess.on('close', (code) => {
      resolve({
        code,
        stdout,
        stderr,
        success: code === 0
      });
    });

    leanProcess.on('error', (error) => {
      reject(error);
    });

    // Set timeout for long-running commands
    setTimeout(() => {
      leanProcess.kill();
      reject(new Error('Command timeout'));
    }, 30000);
  });
}

// API Routes

// Health check
app.get('/health', (req, res) => {
  res.json({ status: 'ok', timestamp: new Date().toISOString() });
});

// Create new Lean session
app.post('/api/lean/session', async (req, res) => {
  try {
    const sessionId = uuidv4();

    // Check if Lean is available first
    try {
      await executeLeanCommand('.', 'lean', ['--version']);
    } catch (leanError) {
      // Lean not available yet
      res.json({
        success: false,
        sessionId,
        error: 'Lean 4 is still installing. Please wait and try again.',
        leanInstalling: true
      });
      return;
    }

    const projectPath = await createLeanProject(sessionId);

    // Initialize the project with lake (with longer timeout)
    console.log('Initializing Lean project...');
    const initResult = await executeLeanCommand(projectPath, 'lake', ['update']);

    res.json({
      success: true,
      sessionId,
      projectPath,
      initResult: {
        stdout: initResult.stdout,
        stderr: initResult.stderr,
        success: initResult.success
      }
    });
  } catch (error) {
    console.error('Error creating session:', error);
    res.json({
      success: false,
      error: error.message,
      leanInstalling: error.message.includes('timeout') || error.message.includes('Command timeout')
    });
  }
});

// Parse and check Lean expression
app.post('/api/lean/check', async (req, res) => {
  try {
    const { sessionId, expression, assumptions = [] } = req.body;

    if (!sessionId || !expression) {
      return res.status(400).json({
        success: false,
        error: 'Missing sessionId or expression'
      });
    }

    const projectPath = path.join(LEAN_PROJECT_DIR, sessionId);

    if (!await fs.pathExists(projectPath)) {
      return res.status(404).json({
        success: false,
        error: 'Session not found'
      });
    }

    // Create a temporary file with the expression to check
    const tempFileName = `Check_${Date.now()}.lean`;
    const tempFilePath = path.join(projectPath, 'LeanUI', tempFileName);

    // Build the Lean code with assumptions and expression
    let leanCode = `import LeanUI.Basic\n\n`;

    // Add assumptions
    if (assumptions.length > 0) {
      leanCode += '-- Assumptions\n';
      assumptions.forEach(assumption => {
        leanCode += `variable ${assumption}\n`;
      });
      leanCode += '\n';
    }

    // Add the expression to check
    leanCode += `-- Expression to check\n`;
    leanCode += `#check ${expression}\n`;
    leanCode += `#print ${expression}\n`;

    await fs.writeFile(tempFilePath, leanCode);

    // Run lean on the file
    const checkResult = await executeLeanCommand(
      projectPath,
      'lean',
      [tempFilePath]
    );

    // Parse the output for type information
    const typeInfo = parseTypeInfo(checkResult.stdout);
    const errors = parseErrors(checkResult.stderr);

    // Clean up temp file
    await fs.remove(tempFilePath);

    res.json({
      success: checkResult.success,
      expression,
      typeInfo,
      errors,
      output: {
        stdout: checkResult.stdout,
        stderr: checkResult.stderr
      }
    });

  } catch (error) {
    console.error('Error checking expression:', error);
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// Clean up session
app.delete('/api/lean/session/:sessionId', async (req, res) => {
  try {
    const { sessionId } = req.params;
    const projectPath = path.join(LEAN_PROJECT_DIR, sessionId);

    if (await fs.pathExists(projectPath)) {
      await fs.remove(projectPath);
    }

    res.json({ success: true, message: 'Session cleaned up' });
  } catch (error) {
    console.error('Error cleaning up session:', error);
    res.status(500).json({
      success: false,
      error: error.message
    });
  }
});

// Helper functions to parse Lean output
function parseTypeInfo(stdout) {
  const lines = stdout.split('\n');
  const typeInfo = [];

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line.includes(':')) {
      const match = line.match(/([^:]+):\s*(.+)/);
      if (match) {
        typeInfo.push({
          expression: match[1].trim(),
          type: match[2].trim()
        });
      }
    }
  }

  return typeInfo;
}

function parseErrors(stderr) {
  const lines = stderr.split('\n');
  const errors = [];

  for (const line of lines) {
    if (line.includes('error:') || line.includes('warning:')) {
      errors.push(line.trim());
    }
  }

  return errors;
}

// Start server
app.listen(port, () => {
  console.log(`LeanUI server running on port ${port}`);
  console.log(`Health check: http://localhost:${port}/health`);
});