/**
 * Hypotheses Section - Simplified
 */

import { Assumption } from '../types/enhanced-focus';
import { useNavigation } from '../contexts/NavigationContext';
import { MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';

interface HypothesesSectionProps {
  hypotheses: Assumption[];
  onUpdateHypothesis: (id: string, updated: Assumption) => void;
  onDeleteHypothesis: (id: string) => void;
}

export function HypothesesSection({
  hypotheses,
}: HypothesesSectionProps) {
  const navigation = useNavigation();

  // Check if 'Hypotheses' is in the navigation path
  const isInFocusChain = navigation.state.navigationPath.includes('Hypotheses');

  return (
    <div>
      {/* Focus indicator */}
      <div style={{ padding: '8px', fontSize: '18px' }}>
        {isInFocusChain ? '✓' : '✗'}
      </div>

      {/* List of hypotheses */}
      <div>
        {hypotheses.map((hypothesis, index) => (
          <div key={hypothesis.id} style={{ padding: '4px 8px', display: 'flex', alignItems: 'center', gap: '8px' }}>
            {isInFocusChain && (
              <span style={{ fontFamily: 'monospace', fontSize: '12px', color: '#999', minWidth: '20px' }}>
                {index}
              </span>
            )}
            <MathJaxExpressionRendererRaw expression={hypothesis.expression} readonly />
          </div>
        ))}
      </div>
    </div>
  );
}
