/**
 * Hypotheses Section - Simplified
 */

import { Assumption } from '../types/enhanced-focus';
import { useNavigation } from '../contexts/NavigationContext';
import { MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
import { useEffect, useState } from 'react';

interface HypothesesSectionProps {
  hypotheses: Assumption[];
  onUpdateHypothesis: (id: string, updated: Assumption) => void;
  onDeleteHypothesis: (id: string) => void;
}

export function HypothesesSection({
  hypotheses,
  onUpdateHypothesis,
}: HypothesesSectionProps) {
  const navigation = useNavigation();

  // Derive everything from navigation path
  const navPath = navigation.state.navigationPath;
  const isInFocusChain = navPath[0] === 'Hypotheses';
  const isActive = navPath.length === 1 && navPath[0] === 'Hypotheses';

  // Parse selected index from navigation path: ['Hypotheses', '0'] or ['Hypotheses', '0', 'EditName']
  const selectedIndex = navPath.length >= 2 && navPath[0] === 'Hypotheses' && /^\d+$/.test(navPath[1])
    ? parseInt(navPath[1], 10)
    : null;

  // Derive edit mode from navigation path
  const isEditingName = navPath[2] === 'EditName' || navPath[2] === 'SetName';
  const isEditingExpression = navPath[2] === 'EditExpression' || navPath[2] === 'SetExpression';
  const isClearMode = navPath[2]?.startsWith('Set'); // SetName or SetExpression

  // Local state for multi-digit mode only
  const [isInMultiDigitMode, setIsInMultiDigitMode] = useState(false);
  const [multiDigitBuffer, setMultiDigitBuffer] = useState('');

  // Get selected hypothesis
  const selectedHypothesis = selectedIndex !== null && selectedIndex < hypotheses.length
    ? hypotheses[selectedIndex]
    : null;

  // Keyboard handling for digit selection and arrow keys
  useEffect(() => {
    if (!isActive) {
      // Clear multi-digit mode when not active
      if (isInMultiDigitMode) {
        setIsInMultiDigitMode(false);
        setMultiDigitBuffer('');
      }
      return;
    }

    const handleKeyDown = (e: KeyboardEvent) => {
      // Don't handle if user is typing in an input
      const target = e.target as HTMLElement;
      if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA') {
        return;
      }

      // Arrow keys - cycle through items
      if (e.key === 'ArrowDown' || e.key === 'ArrowRight') {
        const newIndex = selectedIndex === null ? 0 : (selectedIndex + 1) % hypotheses.length;
        const hyp = hypotheses[newIndex];
        navigation.navigateTo(['Hypotheses', String(newIndex)]);
        // Update metadata immediately
        navigation.updateMetadata({
          selectedHypothesisId: hyp.id,
          selectedHypothesisIndex: newIndex,
          selectedHypothesisName: hyp.name,
        });
        e.preventDefault();
        return;
      }

      if (e.key === 'ArrowUp' || e.key === 'ArrowLeft') {
        const newIndex = selectedIndex === null ? hypotheses.length - 1 : (selectedIndex - 1 + hypotheses.length) % hypotheses.length;
        const hyp = hypotheses[newIndex];
        navigation.navigateTo(['Hypotheses', String(newIndex)]);
        // Update metadata immediately
        navigation.updateMetadata({
          selectedHypothesisId: hyp.id,
          selectedHypothesisIndex: newIndex,
          selectedHypothesisName: hyp.name,
        });
        e.preventDefault();
        return;
      }

      // Apostrophe - enter multi-digit mode
      if (e.key === "'" || e.key === 'Quote') {
        setIsInMultiDigitMode(true);
        setMultiDigitBuffer('');
        e.preventDefault();
        return;
      }

      // Escape - exit multi-digit mode
      if (e.key === 'Escape' && isInMultiDigitMode) {
        setIsInMultiDigitMode(false);
        setMultiDigitBuffer('');
        e.preventDefault();
        return;
      }

      // Digit keys
      if (/^[0-9]$/.test(e.key)) {
        const digit = e.key;

        if (isInMultiDigitMode) {
          // Multi-digit mode: accumulate digits
          const newBuffer = multiDigitBuffer + digit;
          setMultiDigitBuffer(newBuffer);

          // Try to navigate to the item
          const index = parseInt(newBuffer, 10);
          if (index >= 0 && index < hypotheses.length) {
            const hyp = hypotheses[index];
            navigation.navigateTo(['Hypotheses', String(index)]);
            // Update metadata immediately
            navigation.updateMetadata({
              selectedHypothesisId: hyp.id,
              selectedHypothesisIndex: index,
              selectedHypothesisName: hyp.name,
            });
          }
          // Don't exit multi-digit mode automatically
        } else {
          // Single digit mode: immediate selection
          const index = parseInt(digit, 10);
          if (index >= 0 && index < hypotheses.length) {
            const hyp = hypotheses[index];
            navigation.navigateTo(['Hypotheses', String(index)]);
            // Update metadata immediately
            navigation.updateMetadata({
              selectedHypothesisId: hyp.id,
              selectedHypothesisIndex: index,
              selectedHypothesisName: hyp.name,
            });
          }
        }

        e.preventDefault();
        return;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [isActive, selectedIndex, hypotheses, isInMultiDigitMode, multiDigitBuffer, navigation]);

  // Handle save
  const handleSave = (value: string) => {
    if (!selectedHypothesis) return;

    if (isEditingName) {
      // Note: No need to call rename callback because TTerm uses De Bruijn indices.
      // The name in a Binder is just for display/pretty-printing, not for variable references.
      onUpdateHypothesis(selectedHypothesis.id, {
        ...selectedHypothesis,
        name: value,
      });
    } else if (isEditingExpression) {
      // Parse the string into an ExpressionNode
      const typeNode = value.trim() === '' ? null : {
        id: `type-${selectedHypothesis.id}-${Date.now()}`,
        type: 'variable' as const,
        raw: value,
        children: [],
      };

      onUpdateHypothesis(selectedHypothesis.id, {
        ...selectedHypothesis,
        type: typeNode,
      });
    }

    // Pop navigation path back
    navigation.navigateTo(navigation.state.navigationPath.slice(0, -1));
  };

  // Handle cancel
  const handleCancel = () => {
    // Just pop navigation path back
    navigation.navigateTo(navigation.state.navigationPath.slice(0, -1));
  };

  return (
    <div>
      {/* Focus indicator */}
      <div style={{ padding: '8px', fontSize: '18px', display: 'flex', alignItems: 'center', gap: '8px' }}>
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
          const isEditingNameForThis = isSelected && isEditingName;
          const isEditingExpressionForThis = isSelected && isEditingExpression;

          // Derive initial value for input
          const initialValue = (() => {
            if (isEditingNameForThis) {
              return isClearMode ? '' : hypothesis.name;
            } else if (isEditingExpressionForThis) {
              return isClearMode ? '' : (hypothesis.type?.raw ?? '');
            }
            return '';
          })();

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
              {/* Index */}
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

              {/* Name - editable if in name edit mode */}
              {isEditingNameForThis ? (
                <>
                  <EditableInput
                    initialValue={hypothesis.name}
                    onSave={handleSave}
                    onCancel={handleCancel}
                    style={{ minWidth: '100px' }}
                  />
                  <span style={{ color: '#999' }}>:</span>
                  <MathJaxExpressionRendererRaw expression={hypothesis.type?.raw ?? '?'} readonly />
                </>
              ) : isEditingExpressionForThis ? (
                <>
                  <span style={{
                    fontFamily: 'monospace',
                    color: '#0066cc',
                    fontWeight: isSelected ? 'bold' : 'normal',
                  }}>
                    {hypothesis.name}
                  </span>
                  <span style={{ color: '#999' }}>:</span>
                  <EditableInput
                    initialValue={initialValue}
                    onSave={handleSave}
                    onCancel={handleCancel}
                    style={{ flex: 1, minWidth: '200px' }}
                  />
                </>
              ) : (
                <>
                  <span style={{
                    fontFamily: 'monospace',
                    color: '#0066cc',
                    fontWeight: isSelected ? 'bold' : 'normal',
                  }}>
                    {hypothesis.name}
                  </span>
                  <span style={{ color: '#999' }}>:</span>
                  <MathJaxExpressionRendererRaw expression={hypothesis.type?.raw ?? '?'} readonly />
                </>
              )}
            </div>
          );
        })}
      </div>
    </div>
  );
}

// Separate component for editable input to isolate state
function EditableInput({
  initialValue,
  onSave,
  onCancel,
  style,
}: {
  initialValue: string;
  onSave: (value: string) => void;
  onCancel: () => void;
  style?: React.CSSProperties;
}) {
  const [value, setValue] = useState(initialValue);

  return (
    <input
      autoFocus
      type="text"
      value={value}
      onChange={(e) => setValue(e.target.value)}
      onKeyDown={(e) => {
        if (e.key === 'Enter') {
          onSave(value);
          e.preventDefault();
        } else if (e.key === 'Escape') {
          onCancel();
          e.preventDefault();
        }
      }}
      style={{
        fontFamily: 'monospace',
        fontSize: '14px',
        padding: '2px 4px',
        border: '1px solid #2845a7',
        borderRadius: '2px',
        ...style,
      }}
    />
  );
}
