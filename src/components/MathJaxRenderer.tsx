import { useEffect, useRef } from 'react';

declare global {
  interface Window {
    MathJax: any;
  }
}

interface MathJaxRendererProps {
  tex: string;
  style?: React.CSSProperties;
}

export function MathJaxRenderer({ tex, style }: MathJaxRendererProps) {
  const mathRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const loadMathJax = () => {
      if (!window.MathJax) {
        // Configure MathJax before loading
        window.MathJax = {
          tex: {
            inlineMath: [['$', '$']],
            displayMath: [['$$', '$$']],
          },
          chtml: {
            fontURL: 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/output/chtml/fonts/woff-v2'
          },
          startup: {
            ready: () => {
              window.MathJax.startup.defaultReady();
              renderMath();
            }
          }
        };

        // Load MathJax from CDN
        const script = document.createElement('script');
        script.src = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js';
        script.async = true;
        document.head.appendChild(script);
      } else {
        renderMath();
      }
    };

    const renderMath = () => {
      if (mathRef.current && window.MathJax && window.MathJax.typesetPromise) {
        mathRef.current.innerHTML = `$$${tex}$$`;
        window.MathJax.typesetPromise([mathRef.current]).catch((err: any) => {
          console.error('MathJax rendering error:', err);
        });
      }
    };

    loadMathJax();
  }, [tex]);

  return <div ref={mathRef} style={style} />;
}