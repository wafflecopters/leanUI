/**
 * InteractiveGoalView — renders a goal with clickable subterms.
 *
 * Uses KaTeX \htmlId annotations to make each subterm
 * individually selectable. Clicking a subterm highlights it and triggers
 * the onSelectPath callback.
 *
 * Hover shows an outline of what would be selected.
 * Nested subterms are handled via z-index by bounding-rect area
 * (smaller = higher z-index = clickable over larger parents).
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

/** Extract the goal ID from an element's id attribute, skipping the root. */
function extractGoalId(elementId: string): string | null {
  if (!elementId.startsWith('goal-')) return null;
  // Skip root — we don't want to select the entire goal
  if (elementId === 'goal-root') return null;
  return elementId;
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
      const goalId = extractGoalId(element.id);
      if (goalId === null) return;

      const rect = element.getBoundingClientRect();
      const containerRect = container.getBoundingClientRect();

      // Skip zero-size elements
      if (rect.width < 1 || rect.height < 1) return;

      const overlay = document.createElement('div');
      overlay.className = 'goal-overlay';
      overlay.style.position = 'absolute';
      overlay.style.left = `${rect.left - containerRect.left}px`;
      overlay.style.top = `${rect.top - containerRect.top}px`;
      overlay.style.width = `${rect.width}px`;
      overlay.style.height = `${rect.height}px`;
      overlay.style.cursor = 'pointer';
      overlay.style.borderRadius = '2px';
      overlay.dataset.goalId = goalId;

      // Z-index by area: smaller overlays (inner subterms) get higher z-index
      const area = rect.width * rect.height;
      overlay.style.zIndex = String(10 + Math.max(0, Math.round(10000 / Math.max(area, 1))));

      // Hover: outline around what would be selected
      overlay.addEventListener('mouseenter', () => {
        overlay.style.outline = '1.5px solid rgba(88, 166, 255, 0.5)';
        overlay.style.outlineOffset = '1px';
      });
      overlay.addEventListener('mouseleave', () => {
        overlay.style.outline = '';
        overlay.style.outlineOffset = '';
      });

      // Click handler — toggle selection
      overlay.addEventListener('click', (e) => {
        e.stopPropagation();
        if (selectedPath === goalId) {
          onSelectPath(null);
        } else {
          onSelectPath(goalId);
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
      const el = container.querySelector(`#${CSS.escape(selectedPath)}`) as HTMLElement | null;
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
