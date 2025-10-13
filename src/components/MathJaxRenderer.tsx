import { useEffect, useRef } from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';

interface MathJaxRendererProps {
  tex: string;
  style?: React.CSSProperties;
}

export function MathJaxRenderer({ tex, style }: MathJaxRendererProps) {
  const mathRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (mathRef.current) {
      try {
        katex.render(tex, mathRef.current, {
          displayMode: true,
          throwOnError: false
        });
      } catch (err: any) {
        console.error('KaTeX rendering error:', err);
        mathRef.current.innerHTML = `<span style="color: red;">LaTeX Error: ${tex}</span>`;
      }
    }
  }, [tex]);

  return <div ref={mathRef} style={style} />;
}