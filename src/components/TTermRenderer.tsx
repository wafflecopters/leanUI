/**
 * TTerm Renderer with Focus Support
 *
 * Renders a TTerm (type theory term) with LaTeX formatting and focus highlighting.
 * Supports clicking on sub-terms to change focus.
 */

import { useMemo, useEffect, useRef } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import { TTerm } from '../types/tt-core';
import { TermFocusPath } from '../utils/termNavigation';

interface TTermRendererProps {
  term: TTerm;
  focusPath?: TermFocusPath;
  onFocusChange?: (newPath: TermFocusPath) => void;
  isActive?: boolean;
  readonly?: boolean;
  inline?: boolean;
}

/**
 * Convert TTerm to LaTeX with unique IDs for each sub-term.
 * This enables click-to-focus functionality.
 */
function ttermToLaTeX(term: TTerm, path: TermFocusPath = []): string {
  const pathId = path.join('-') || 'root';

  switch (term.tag) {
    case 'Var':
      return `\\htmlId{expr-${pathId}}{\\texttt{@${term.index}}}`;

    case 'Sort':
      return `\\htmlId{expr-${pathId}}{\\text{Type}_{${term.level}}}`;

    case 'Binder':
      if (term.binderKind.tag === 'BPi') {
        const domainLatex = ttermToLaTeX(term.domain, [...path, 'domain']);
        const bodyLatex = ttermToLaTeX(term.body, [...path, 'body']);

        // If name is empty, just show "domain -> body"
        if (term.name === '') {
          return `\\htmlId{expr-${pathId}}{${domainLatex} \\to ${bodyLatex}}`;
        }

        // Otherwise show "(name : domain) -> body"
        return `\\htmlId{expr-${pathId}}{(${term.name} : ${domainLatex}) \\to ${bodyLatex}}`;
      } else if (term.binderKind.tag === 'BLam') {
        const bodyLatex = ttermToLaTeX(term.body, [...path, 'body']);
        return `\\htmlId{expr-${pathId}}{\\lambda ${term.name}. ${bodyLatex}}`;
      } else if (term.binderKind.tag === 'BLet') {
        const defValLatex = ttermToLaTeX(term.binderKind.defVal, [...path, 'domain']);
        const bodyLatex = ttermToLaTeX(term.body, [...path, 'body']);
        return `\\htmlId{expr-${pathId}}{\\text{let } ${term.name} := ${defValLatex} \\text{ in } ${bodyLatex}}`;
      }
      return `\\htmlId{expr-${pathId}}{\\texttt{?binder}}`;

    case 'App':
      const fnLatex = ttermToLaTeX(term.fn, [...path, 'fn']);
      const argLatex = ttermToLaTeX(term.arg, [...path, 'arg']);
      return `\\htmlId{expr-${pathId}}{(${fnLatex} \\ ${argLatex})}`;

    case 'Const':
      return `\\htmlId{expr-${pathId}}{\\texttt{${term.name}}}`;

    case 'Hole':
      // Escape underscores in hole IDs for LaTeX
      const escapedId = term.id.replace(/_/g, '\\_');
      return `\\htmlId{expr-${pathId}}{\\texttt{?${escapedId}}}`;

    case 'Annot':
      const termLatex = ttermToLaTeX(term.term, [...path, 'term']);
      const typeLatex = ttermToLaTeX(term.type, [...path, 'type']);
      return `\\htmlId{expr-${pathId}}{(${termLatex} : ${typeLatex})}`;
  }
}

export function TTermRenderer({
  term,
  focusPath = [],
  onFocusChange,
  isActive = true,
  readonly = false,
  inline = false,
}: TTermRendererProps) {
  const containerRef = useRef<HTMLDivElement>(null);

  // Convert TTerm to LaTeX
  const latex = useMemo(() => ttermToLaTeX(term), [term]);

  // Render KaTeX
  useEffect(() => {
    if (!containerRef.current) return;

    try {
      katex.render(latex, containerRef.current, {
        displayMode: !inline,
        throwOnError: false,
        trust: (context) => context.command === '\\htmlId',
        strict: false,
      });

      // Set up click handlers (only when readonly changes)
      if (!readonly && onFocusChange) {
        const allElements = containerRef.current.querySelectorAll('[id^="expr-"]');
        allElements.forEach(element => {
          const id = element.id;
          const pathStr = id.replace('expr-', '');
          const newPath: TermFocusPath = pathStr === 'root' ? [] : pathStr.split('-') as TermFocusPath;

          (element as HTMLElement).style.cursor = 'pointer';
          (element as HTMLElement).onclick = (e) => {
            e.stopPropagation();
            onFocusChange(newPath);
          };
        });
      }
    } catch (error) {
      console.error('KaTeX rendering error:', error);
      if (containerRef.current) {
        containerRef.current.textContent = `Error rendering: ${error}`;
      }
    }
  }, [latex, readonly, inline, onFocusChange]);

  // Apply focus highlighting
  useEffect(() => {
    if (!containerRef.current) return;

    const focusPathId = focusPath.join('-') || 'root';
    const allElements = containerRef.current.querySelectorAll('[id^="expr-"]');

    // Clear all highlighting
    allElements.forEach(el => {
      (el as HTMLElement).style.backgroundColor = '';
      (el as HTMLElement).style.borderRadius = '';
      (el as HTMLElement).style.outline = '';
      (el as HTMLElement).style.outlineOffset = '';
    });

    // Only apply focus highlight and hover effects if active (not readonly)
    if (!readonly) {
      const focusedElement = containerRef.current.querySelector(`#expr-${focusPathId}`);
      if (focusedElement) {
        (focusedElement as HTMLElement).style.backgroundColor = 'rgba(0, 122, 204, 0.3)';
        (focusedElement as HTMLElement).style.borderRadius = '2px';
        (focusedElement as HTMLElement).style.outline = '1px solid transparent';
        (focusedElement as HTMLElement).style.outlineOffset = '1px';
      }

      // Add hover effects
      if (onFocusChange) {
        allElements.forEach(element => {
          const pathStr = element.id.replace('expr-', '');

          (element as HTMLElement).onmouseenter = () => {
            if (pathStr !== focusPathId) {
              (element as HTMLElement).style.backgroundColor = 'rgba(255, 193, 7, 0.2)';
            }
          };

          (element as HTMLElement).onmouseleave = () => {
            if (pathStr !== focusPathId) {
              (element as HTMLElement).style.backgroundColor = '';
            }
          };
        });
      }
    }
  }, [focusPath, readonly, onFocusChange]);

  return (
    <div
      ref={containerRef}
      style={{
        opacity: isActive ? 1 : 0.6,
        padding: inline ? '2px 4px' : '8px 12px',
      }}
    />
  );
}
