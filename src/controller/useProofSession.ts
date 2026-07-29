/**
 * React adapter for `ProofSession`.
 *
 * This is the whole React part of the proof editor: create a session, keep it
 * fed with the current file, subscribe to it, tear it down. Every decision —
 * which tactics to try, what Lean said, what the user may do next — happens in
 * the controller, which knows nothing about React.
 *
 * Two details that are easy to get wrong, and were:
 *
 *   - The session is created in an EFFECT and owned by state, not built during
 *     render. React 18's StrictMode mounts, unmounts and remounts every effect
 *     in development; a session created during render would be disposed by that
 *     simulated unmount and never rebuilt, leaving the panel wired to a dead
 *     controller that silently ignores every request.
 *
 *   - It is created once per DECLARATION and then *fed* new source text, rather
 *     than rebuilt whenever the source changes. Rebuilding would mint fresh
 *     proof-node ids on every write-back, so the goal map (keyed by id) would
 *     match nothing and the view would blank on each edit the user made.
 */
import { useEffect, useRef, useState, useSyncExternalStore } from 'react';
import type { LeanDeclaration } from '../lean/types';
import { httpAnalyzer } from './analyzer';
import { ProofSession, ProofSessionError } from './session';
import type { SessionState } from './types';

export interface UseProofSessionArgs {
  source: string;
  declarations: readonly LeanDeclaration[];
  declName: string;
  mathlib?: boolean;
  /** Only the card the user is working on runs Lean round-trips. */
  active?: boolean;
  onSourceChange?: (next: string) => void;
}

export interface UseProofSessionResult {
  session: ProofSession | null;
  state: SessionState | null;
  /** Set when the declaration can't host an interactive proof. */
  error?: string;
  /** True before the session exists (one frame) — distinct from "can't". */
  starting: boolean;
}

export function useProofSession(args: UseProofSessionArgs): UseProofSessionResult {
  const { source, declarations, declName, mathlib, active = false, onSourceChange } = args;

  // Values the session is created with. Held in refs so the creation effect can
  // stay keyed on the declaration alone without capturing stale text.
  const latest = useRef({ source, declarations, mathlib, onSourceChange });
  latest.current = { source, declarations, mathlib, onSourceChange };

  const [session, setSession] = useState<ProofSession | null>(null);
  const [error, setError] = useState<string | undefined>(undefined);

  useEffect(() => {
    let created: ProofSession;
    try {
      created = ProofSession.open({
        analyze: httpAnalyzer,
        source: latest.current.source,
        declarations: latest.current.declarations,
        declName,
        mathlib: latest.current.mathlib,
        autoRefresh: false, // enabled below, once the card is the active one
        onSourceChange: (next) => latest.current.onSourceChange?.(next),
      });
    } catch (e) {
      setError(e instanceof ProofSessionError ? e.message : String(e));
      setSession(null);
      return;
    }
    setError(undefined);
    setSession(created);
    return () => {
      created.dispose();
      setSession((s) => (s === created ? null : s));
    };
  }, [declName]);

  // Feed the session the current file. It ignores an update that doesn't change
  // its own proof, so our write-backs never re-seed the tree.
  useEffect(() => {
    session?.setSource(source, declarations);
  }, [session, source, declarations]);

  // Lean runs only for the active card; activating one refreshes it.
  useEffect(() => {
    if (!session) return;
    session.setAutoRefresh(active);
    // Never swallow a failure: a rejected refresh would leave the busy flags on
    // and the panel spinning with nothing to explain why.
    if (active) session.refresh().catch((e) => console.error('[proof session] refresh failed', e));
  }, [session, active]);

  const state = useSyncExternalStore(
    (onChange) => session?.subscribe(onChange) ?? (() => {}),
    () => session?.getState() ?? null,
    () => session?.getState() ?? null,
  );

  return { session, state, error, starting: session === null && error === undefined };
}
