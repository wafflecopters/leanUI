import { defineConfig } from '@rsbuild/core';
import { pluginReact } from '@rsbuild/plugin-react';
import { pluginTypeCheck } from '@rsbuild/plugin-type-check';

// Lean bridge port — keep in sync with server/index.ts (default 3457, env-overridable).
const leanBridgePort = process.env.LEAN_BRIDGE_PORT ?? '3457';

export default defineConfig({
  plugins: [
    pluginReact(),
    pluginTypeCheck({
      tsCheckerOptions: {
        typescript: {
          configFile: './tsconfig.build.json',
        },
      },
    }),
  ],
  html: {
    template: './src/index.html',
  },
  source: {
    entry: {
      index: './src/main.tsx',
    },
  },
  server: {
    proxy: {
      '/api': {
        target: `http://localhost:${leanBridgePort}`,
        changeOrigin: true,
      },
    },
  },
});