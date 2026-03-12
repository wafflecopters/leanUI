/**
 * InteractiveGoalView — renders a goal with clickable subterms.
 *
 * Uses KaTeX \htmlId annotations to make each Pi binder and the body
 * individually selectable. Clicking a subterm highlights it and triggers
 * the onSelectPath callback.
 *
 * Follows the overlay pattern from MathJaxExpressionRenderer.tsx.
 */

import React, { useRef, useEffect, useCallback } from 'react';
import katex from 'katex';
import { GoalPath, InteractiveGoal } from '../proof-tree/interactive-goal';

export interface InteractiveGoalViewProps {
  readonly goal: InteractiveGoal;
  readonly selectedPath: GoalPath | null;
  readonly onSelectPath: (path: GoalPath | null) => void;
  readonly style?: React.CSSProperties;
}

/** Parse a goal element ID into a GoalPath. */
function parseGoalId(id: string): GoalPath | null {
  const str = id.replace('goal-', '');
  if (str === 'root') return [];
  if (str === 'body') return [-1] as unknown as GoalPath; // Special sentinel for body
  const parts = str.split('-').map(Number);
  if (parts.some(isNaN)) return null;
  return parts;
}

function pathsEqual(a: GoalPath | null, b: GoalPath | null): boolean {
  if (a === null || b === null) return a === b;
  if (a.length !== b.length) return false;
  return a.every((v, i) => v === b[i]);
}

export function InteractiveGoalView({ goal, selectedPath, onSelectPath, style }: InteractiveGoalViewProps) {
  const containerRef = useRef<HTMLDivElement>(null);

  // Render KaTeX
  useEffect(() => {
    if (!containerRef.current) return;
    try {
      katex.render(goal.latex, containerRef.current, {
        displayMode: false,
        throwOnError: false,
        trust: (context) => ['\\htmlId', '\\htmlClass', '\\textcolor'].includes(context.command),
        strict: false,
      });
    } catch {
      containerRef.current.textContent = goal.latex;
    }
  }, [goal.latex]);

  // Create overlays for click interaction
  useEffect(() => {
    if (!containerRef.current) return;

    const container = containerRef.current;

    // Disable default KaTeX pointer events
    const katexEl = container.querySelector('.katex') as HTMLElement | null;
    if (katexEl) {
      katexEl.style.pointerEvents = 'none';
      katexEl.style.userSelect = 'none';
    }

    // Remove existing overlays
    container.querySelectorAll('.goal-overlay').forEach(el => el.remove());

    // Find all goal-annotated elements
    const goalElements = container.querySelectorAll('[id^="goal-"]');

    goalElements.forEach(element => {
      const path = parseGoalId(element.id);
      if (path === null) return;
      // Skip the root element — we only want individual binders and body
      if (path.length === 0) return;

      const rect = element.getBoundingClientRect();
      const containerRect = container.getBoundingClientRect();

      const overlay = document.createElement('div');
      overlay.className = 'goal-overlay';
      overlay.style.position = 'absolute';
      overlay.style.left = `${rect.left - containerRect.left}px`;
      overlay.style.top = `${rect.top - containerRect.top}px`;
      overlay.style.width = `${rect.width}px`;
      overlay.style.height = `${rect.height}px`;
      overlay.style.cursor = 'pointer';
      overlay.style.zIndex = '10';
      overlay.style.borderRadius = '2px';
      overlay.dataset.goalPath = path.join('-');

      // Hover effect
      overlay.addEventListener('mouseenter', () => {
        overlay.style.backgroundColor = 'rgba(88, 166, 255, 0.12)';
      });
      overlay.addEventListener('mouseleave', () => {
        overlay.style.backgroundColor = '';
      });

      // Click handler
      overlay.addEventListener('click', (e) => {
        e.stopPropagation();
        // Toggle: click same → deselect
        if (pathsEqual(selectedPath, path)) {
          onSelectPath(null);
        } else {
          onSelectPath(path);
        }
      });

      container.appendChild(overlay);
    });

    return () => {
      container.querySelectorAll('.goal-overlay').forEach(el => el.remove());
    };
  }, [goal.latex, selectedPath, onSelectPath]);

  // Apply selection highlighting
  useEffect(() => {
    if (!containerRef.current) return;
    const container = containerRef.current;

    // Clear all highlights
    container.querySelectorAll('[id^="goal-"]').forEach(el => {
      (el as HTMLElement).style.backgroundColor = '';
      (el as HTMLElement).style.borderRadius = '';
    });

    // Apply highlight to selected
    if (selectedPath !== null) {
      const id = selectedPath.length === 0
        ? 'goal-root'
        : (selectedPath[0] === -1 ? 'goal-body' : `goal-${selectedPath.join('-')}`);
      const el = container.querySelector(`#${id}`) as HTMLElement | null;
      if (el) {
        el.style.backgroundColor = 'rgba(88, 166, 255, 0.25)';
        el.style.borderRadius = '2px';
      }
    }
  }, [selectedPath, goal.latex]);

  // Click outside to deselect
  const handleContainerClick = useCallback(() => {
    onSelectPath(null);
  }, [onSelectPath]);

  return (
    <div
      ref={containerRef}
      onClick={handleContainerClick}
      style={{
        position: 'relative',
        padding: '4px 8px',
        backgroundColor: '#0d1117',
        borderRadius: '4px',
        border: '1px solid #21262d',
        wordBreak: 'break-word' as const,
        cursor: 'default',
        ...style,
      }}
    />
  );
}
