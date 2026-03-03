/**
 * SplitPane — a draggable split between two (or more) children.
 *
 * Supports horizontal and vertical splits with pixel or percent sizing.
 * Adapted from puzzlets2 editor for inline-style usage (no Tailwind).
 */

import { useRef, useState, useEffect, useCallback, type ReactNode } from 'react';

export interface PaneSize {
  size: number;
  mode: 'pixels' | 'percent';
}

interface SplitPaneProps {
  direction: 'horizontal' | 'vertical';
  children: ReactNode[];
  /** Preferred sizes for each pane. Unspecified entries split remaining space equally. */
  paneSizes?: (PaneSize | undefined)[];
  /** Divider thickness in px (default 3) */
  dividerSize?: number;
  /** Style applied to the outer container */
  style?: React.CSSProperties;
}

/**
 * Convert a paneSizes spec into normalized fractions summing to 1.
 * `availablePx` is the container dimension minus all dividers.
 */
function computeFractions(
  specs: (PaneSize | undefined)[] | undefined,
  count: number,
  availablePx: number,
): number[] {
  if (!specs || specs.length === 0) {
    return Array.from({ length: count }, () => 1 / count);
  }

  const raw: (number | undefined)[] = [];
  for (let i = 0; i < count; i++) {
    const spec = specs[i];
    if (!spec) {
      raw.push(undefined);
    } else if (spec.mode === 'percent') {
      raw.push(spec.size / 100);
    } else {
      raw.push(availablePx > 0 ? spec.size / availablePx : spec.size);
    }
  }

  const definedSum = raw.reduce<number>((sum, v) => sum + (v ?? 0), 0);
  const undefinedCount = raw.filter(v => v === undefined).length;

  if (undefinedCount === 0) {
    const scale = definedSum > 0 ? 1 / definedSum : 1;
    return raw.map(v => v! * scale);
  }

  const remaining = Math.max(1 - definedSum, 0);
  const eachUndefined = remaining / undefinedCount;
  return raw.map(v => v ?? eachUndefined);
}

function paneSizesKey(specs: (PaneSize | undefined)[] | undefined): string {
  if (!specs) return '';
  return specs.map(s => (s ? `${s.size}:${s.mode}` : '_')).join(',');
}

export default function SplitPane({
  direction,
  children,
  paneSizes,
  dividerSize = 3,
  style,
}: SplitPaneProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const count = children.length;
  const [sizes, setSizes] = useState<number[]>(() =>
    computeFractions(paneSizes, count, 0),
  );
  const [dragIndex, setDragIndex] = useState<number | null>(null);

  const isHorizontal = direction === 'horizontal';
  const totalDividerPx = (count - 1) * dividerSize;

  const getAvailablePx = useCallback((): number => {
    if (!containerRef.current) return 0;
    const rect = containerRef.current.getBoundingClientRect();
    return (isHorizontal ? rect.width : rect.height) - totalDividerPx;
  }, [isHorizontal, totalDividerPx]);

  // Recompute fractions when paneSizes prop changes
  const sizesKey = paneSizesKey(paneSizes);
  useEffect(() => {
    const availablePx = getAvailablePx();
    setSizes(computeFractions(paneSizes, count, availablePx));
  }, [sizesKey, count]); // eslint-disable-line react-hooks/exhaustive-deps

  // Also recompute pixel-based sizes when the container resizes
  const hasPixelSizes = paneSizes?.some(s => s?.mode === 'pixels') ?? false;
  useEffect(() => {
    if (!hasPixelSizes || !containerRef.current || typeof ResizeObserver === 'undefined') return;
    const observer = new ResizeObserver(() => {
      const availablePx = getAvailablePx();
      setSizes(computeFractions(paneSizes, count, availablePx));
    });
    observer.observe(containerRef.current);
    return () => observer.disconnect();
  }, [hasPixelSizes, sizesKey, count, getAvailablePx]); // eslint-disable-line react-hooks/exhaustive-deps

  useEffect(() => {
    if (dragIndex === null) return;

    const onMouseMove = (e: MouseEvent) => {
      if (!containerRef.current) return;
      const rect = containerRef.current.getBoundingClientRect();
      const pos = isHorizontal ? e.clientX - rect.left : e.clientY - rect.top;
      const available = (isHorizontal ? rect.width : rect.height) - totalDividerPx;
      if (available <= 0) return;

      const dividerOffset = dragIndex * dividerSize + dividerSize / 2;
      const posFrac = (pos - dividerOffset) / available;

      setSizes(prev => {
        const next = [...prev];
        const pairSum = prev[dragIndex] + prev[dragIndex + 1];
        const leftEdge = prev.slice(0, dragIndex).reduce((a, b) => a + b, 0);

        const minFrac = 0.02;
        const newLeft = Math.min(
          Math.max(posFrac - leftEdge, minFrac),
          pairSum - minFrac,
        );
        next[dragIndex] = newLeft;
        next[dragIndex + 1] = pairSum - newLeft;
        return next;
      });
    };

    const onMouseUp = () => setDragIndex(null);

    document.addEventListener('mousemove', onMouseMove);
    document.addEventListener('mouseup', onMouseUp);
    return () => {
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    };
  }, [dragIndex, isHorizontal, count, dividerSize, totalDividerPx]);

  const cursorStyle = isHorizontal ? 'col-resize' : 'row-resize';
  const sizeProp = isHorizontal ? 'width' : 'height';

  const elements: ReactNode[] = [];
  for (let i = 0; i < count; i++) {
    elements.push(
      <div
        key={`pane-${i}`}
        style={{
          [sizeProp]: `calc(${sizes[i] * 100}% - ${totalDividerPx * sizes[i]}px)`,
          overflow: 'hidden',
          display: 'flex',
          flexDirection: 'column',
          pointerEvents: dragIndex !== null ? 'none' : undefined,
        }}
      >
        {children[i]}
      </div>,
    );

    if (i < count - 1) {
      const dividerIdx = i;
      elements.push(
        <div
          key={`div-${i}`}
          style={{
            [sizeProp]: dividerSize,
            cursor: cursorStyle,
            flexShrink: 0,
            backgroundColor: dragIndex === dividerIdx ? '#5b8def' : '#30363d',
            transition: 'background-color 0.15s',
          }}
          onMouseEnter={(e) => { if (dragIndex === null) e.currentTarget.style.backgroundColor = '#5b8def'; }}
          onMouseLeave={(e) => { if (dragIndex === null) e.currentTarget.style.backgroundColor = '#30363d'; }}
          onMouseDown={(e) => {
            e.preventDefault();
            setDragIndex(dividerIdx);
          }}
        />,
      );
    }
  }

  return (
    <div
      ref={containerRef}
      style={{
        display: 'flex',
        flexDirection: isHorizontal ? 'row' : 'column',
        height: '100%',
        width: '100%',
        overflow: 'hidden',
        ...(dragIndex !== null ? { cursor: cursorStyle } : {}),
        ...style,
      }}
    >
      {elements}
    </div>
  );
}
