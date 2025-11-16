/**
 * Navigation Footer Component
 *
 * Displays the current keyboard navigation state at the bottom of the window.
 * Shows:
 * - Current input mode (Navigation/Typing)
 * - Navigation breadcrumb (e.g., "Navigation > Goals > Editor")
 * - Available keyboard shortcuts in current context
 */

import React from 'react';
import { useNavigation } from '../contexts/NavigationContext';
import { NavigationUtils } from '../types/commands';

export function NavigationFooter() {
  const { state, getAvailableCommands } = useNavigation();

  const availableCommands = getAvailableCommands();

  // Build breadcrumb text
  const breadcrumb = NavigationUtils.buildBreadcrumb(state.navigationPath);

  return (
    <div
      style={{
        position: 'fixed',
        bottom: 0,
        left: 0,
        right: 0,
        backgroundColor: '#f8f9fa',
        borderTop: '2px solid #dee2e6',
        padding: '8px 20px',
        display: 'flex',
        alignItems: 'center',
        gap: '24px',
        fontSize: '13px',
        fontFamily: 'system-ui, sans-serif',
        zIndex: 1000,
        boxShadow: '0 -2px 8px rgba(0, 0, 0, 0.05)',
      }}
    >
      {/* Breadcrumb */}
      <div style={{ display: 'flex', alignItems: 'center', gap: '8px', flex: 1 }}>
        <span style={{ fontWeight: 'bold', color: '#495057' }}>Path:</span>
        <span style={{ color: '#6c757d', fontFamily: 'monospace' }}>
          {breadcrumb}
        </span>
      </div>

      {/* Available shortcuts */}
      {availableCommands.length > 0 && (
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            gap: '12px',
            borderLeft: '1px solid #dee2e6',
            paddingLeft: '24px',
          }}
        >
          <span style={{ fontWeight: 'bold', color: '#495057', fontSize: '12px' }}>
            Available:
          </span>
          <div style={{ display: 'flex', gap: '8px', flexWrap: 'wrap' }}>
            {availableCommands.slice(0, 6).map(cmd => (
              <div
                key={cmd.id}
                style={{
                  display: 'flex',
                  alignItems: 'center',
                  gap: '4px',
                  padding: '2px 6px',
                  backgroundColor: 'white',
                  border: '1px solid #ced4da',
                  borderRadius: '3px',
                  fontSize: '11px',
                }}
                title={cmd.description}
              >
                <kbd
                  style={{
                    backgroundColor: '#e9ecef',
                    padding: '1px 4px',
                    borderRadius: '2px',
                    fontWeight: 'bold',
                    fontSize: '11px',
                    fontFamily: 'monospace',
                  }}
                >
                  {cmd.key}
                </kbd>
                <span style={{ color: '#6c757d' }}>{cmd.label}</span>
              </div>
            ))}
            {availableCommands.length > 6 && (
              <span style={{ color: '#adb5bd', fontSize: '11px' }}>
                +{availableCommands.length - 6} more
              </span>
            )}
          </div>
        </div>
      )}

      {/* Escape hint */}
      {state.navigationPath.length > 0 && (
        <div style={{ color: '#6c757d', fontSize: '12px' }}>
          Press <kbd style={{
            backgroundColor: '#e9ecef',
            padding: '2px 6px',
            borderRadius: '3px',
            fontWeight: 'bold',
            fontFamily: 'monospace',
          }}>ESC</kbd> to go back
        </div>
      )}
    </div>
  );
}

/**
 * Wrapper component that adds padding to prevent content from being obscured by the footer
 */
export function NavigationFooterSpacer({ children }: { children: React.ReactNode }) {
  return (
    <div style={{ paddingBottom: '48px' }}>
      {children}
    </div>
  );
}
