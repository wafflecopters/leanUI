/**
 * Hypotheses Section - Simplified
 */

import { Assumption } from '../types/enhanced-focus';
import { useNavigation } from '../contexts/NavigationContext';
import { MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
import { useArrayItemSelection } from '../hooks/useArrayItemSelection';
import { useRef, useEffect } from 'react';

interface HypothesesSectionProps {
  hypotheses: Assumption[];
  onUpdateHypothesis: (id: string, updated: Assumption) => void;
  onDeleteHypothesis: (id: string) => void;
}

export function HypothesesSection({
  hypotheses,
}: HypothesesSectionProps) {
  const navigation = useNavigation();
  const updateMetadataRef = useRef(navigation.updateMetadata);

  // Keep ref up to date
  useEffect(() => {
    updateMetadataRef.current = navigation.updateMetadata;
  });

  // Check if 'Hypotheses' is in the navigation path (but NOT in Editor sub-path)
  const isInFocusChain = navigation.state.navigationPath.includes('Hypotheses');
  const isActive = navigation.state.navigationPath[0] === 'Hypotheses' &&
                   navigation.state.navigationPath[1] !== 'Editor';

  // Array item selection (with apostrophe multi-digit mode)
  const {
    selectedIndex,
    isInMultiDigitMode,
    multiDigitBuffer,
  } = useArrayItemSelection({
    arrayLength: hypotheses.length,
    isActive,
    onSelectionChange: (index) => {
      // Update navigation metadata with selected hypothesis
      updateMetadataRef.current({
        selectedHypothesisId: index !== null ? hypotheses[index]?.id : null,
        selectedHypothesisIndex: index,
      });
    },
  });

  return (
    <div>
      {/* Focus indicator */}
      <div style={{ padding: '8px', fontSize: '18px', display: 'flex', alignItems: 'center', gap: '8px' }}>
        <span>{isInFocusChain ? '✓' : '✗'}</span>
        {isInMultiDigitMode && (
          <span style={{
            fontSize: '12px',
            backgroundColor: '#ffd700',
            color: '#000',
            padding: '2px 6px',
            borderRadius: '3px',
            fontFamily: 'monospace',
            fontWeight: 'bold'
          }}>
            '{multiDigitBuffer}_
          </span>
        )}
      </div>

      {/* List of hypotheses */}
      <div>
        {hypotheses.map((hypothesis, index) => {
          const isSelected = selectedIndex === index;

          return (
            <div
              key={hypothesis.id}
              style={{
                padding: '4px 8px',
                display: 'flex',
                alignItems: 'center',
                gap: '8px',
                backgroundColor: isSelected ? '#e6f3ff' : 'transparent',
                border: isSelected ? '2px solid #2845a7' : '2px solid transparent',
                borderRadius: '4px',
                transition: 'all 0.2s ease',
              }}
            >
              {isInFocusChain && (
                <span style={{
                  fontFamily: 'monospace',
                  fontSize: '12px',
                  color: isSelected ? '#2845a7' : '#999',
                  minWidth: '20px',
                  fontWeight: isSelected ? 'bold' : 'normal',
                }}>
                  {index}
                </span>
              )}
              <MathJaxExpressionRendererRaw expression={hypothesis.expression} readonly />
            </div>
          );
        })}
      </div>
    </div>
  );
}
