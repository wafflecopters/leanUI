/**
 * TTerm Renderer with Focus Support
 *
 * Renders a TTerm (type theory term) with focus highlighting and inline editing.
 * Supports navigating to sub-terms including binder names.
 *
 * For binders, the name is treated as child index 0, followed by domain and body.
 * When focused on a name, an inline text editor appears.
 */

import { useMemo, useCallback } from 'react';
import { TTerm } from '../compiler/surface';
import { TermFocusPath, isNamePath, setNameAtPath } from '../utils/termNavigation';
import { AutoSizingTextField } from './AutoSizingTextField';

interface TTermRendererProps {
  term: TTerm;
  focusPath?: TermFocusPath;
  onFocusChange?: (newPath: TermFocusPath) => void;
  onTermChange?: (newTerm: TTerm) => void;
  isActive?: boolean;
  readonly?: boolean;
  inline?: boolean;
}

/**
 * Check if two paths are equal.
 */
function pathsEqual(a: TermFocusPath, b: TermFocusPath): boolean {
  if (a.length !== b.length) return false;
  return a.every((step, i) => step === b[i]);
}

/**
 * Check if a path starts with another path (is a descendant).
 */
function pathStartsWith(path: TermFocusPath, prefix: TermFocusPath): boolean {
  if (path.length < prefix.length) return false;
  return prefix.every((step, i) => path[i] === step);
}

interface RenderContext {
  focusPath: TermFocusPath;
  onFocusChange?: (newPath: TermFocusPath) => void;
  onNameChange?: (path: TermFocusPath, newName: string) => void;
  readonly: boolean;
  /** Telescope of binder names (most recent first, index 0 = innermost binder) */
  telescope: string[];
}

/**
 * Render a clickable/focusable span for a sub-expression.
 */
function FocusableSpan({
  path,
  ctx,
  children,
  style,
}: {
  path: TermFocusPath;
  ctx: RenderContext;
  children: React.ReactNode;
  style?: React.CSSProperties;
}) {
  const isFocused = pathsEqual(ctx.focusPath, path);
  const isAncestor = pathStartsWith(ctx.focusPath, path) && !isFocused;

  const handleClick = useCallback((e: React.MouseEvent) => {
    e.stopPropagation();
    if (!ctx.readonly && ctx.onFocusChange) {
      ctx.onFocusChange(path);
    }
  }, [ctx, path]);

  return (
    <span
      onClick={handleClick}
      style={{
        cursor: ctx.readonly ? 'default' : 'pointer',
        backgroundColor: isFocused
          ? 'rgba(0, 122, 204, 0.3)'
          : isAncestor
            ? 'rgba(0, 122, 204, 0.1)'
            : undefined,
        borderRadius: '2px',
        padding: '0 1px',
        ...style,
      }}
    >
      {children}
    </span>
  );
}

/**
 * Render a binder name - either as static text or an inline editor when focused.
 */
function BinderName({
  name,
  path,
  ctx,
}: {
  name: string;
  path: TermFocusPath;
  ctx: RenderContext;
}) {
  const namePath: TermFocusPath = [...path, 'name'];
  const isFocused = pathsEqual(ctx.focusPath, namePath);

  if (isFocused && !ctx.readonly && ctx.onNameChange) {
    return (
      <AutoSizingTextField
        value={name}
        onChange={(newName) => ctx.onNameChange!(namePath, newName)}
        onSubmit={() => {
          // Move focus to domain after submitting name
          if (ctx.onFocusChange) {
            ctx.onFocusChange([...path, 'domain']);
          }
        }}
        onCancel={() => {
          // Move focus back to binder
          if (ctx.onFocusChange) {
            ctx.onFocusChange(path);
          }
        }}
        minWidth="1.5em"
        placeholder="_"
        style={{
          fontFamily: 'inherit',
          fontSize: 'inherit',
        }}
      />
    );
  }

  return (
    <FocusableSpan path={namePath} ctx={ctx}>
      {name || '_'}
    </FocusableSpan>
  );
}

/**
 * Create a new context with an extended telescope.
 */
function extendTelescope(ctx: RenderContext, name: string): RenderContext {
  return {
    ...ctx,
    telescope: [name, ...ctx.telescope],
  };
}

/**
 * Recursively render a TTerm.
 */
function renderTerm(term: TTerm, path: TermFocusPath, ctx: RenderContext): React.ReactNode {
  switch (term.tag) {
    case 'Var': {
      // Look up the name from the telescope using De Bruijn index
      const name = term.index < ctx.telescope.length
        ? ctx.telescope[term.index]
        : null;

      // Use name if available and non-empty, otherwise fall back to @index
      const displayName = name && name !== '' && name !== '_'
        ? name
        : `@${term.index}`;

      return (
        <FocusableSpan path={path} ctx={ctx}>
          <span style={{ fontFamily: 'monospace' }}>{displayName}</span>
        </FocusableSpan>
      );
    }

    case 'Sort':
      return (
        <FocusableSpan path={path} ctx={ctx}>
          <span>Type<sub>{term.level}</sub></span>
        </FocusableSpan>
      );

    case 'Binder': {
      // Extend telescope for body rendering
      const bodyCtx = extendTelescope(ctx, term.name);

      if (term.binderKind.tag === 'BPiTT') {
        // Pi binders always have domain
        const domainNode = renderTerm(term.domain!, [...path, 'domain'], ctx);
        const bodyNode = renderTerm(term.body, [...path, 'body'], bodyCtx);

        // If name is empty or '_', show as "domain → body" (non-dependent arrow)
        if (term.name === '' || term.name === '_') {
          return (
            <FocusableSpan path={path} ctx={ctx}>
              {domainNode} <span style={{ color: '#666' }}>→</span> {bodyNode}
            </FocusableSpan>
          );
        }

        // Named: "(name : domain) → body"
        return (
          <FocusableSpan path={path} ctx={ctx}>
            (<BinderName name={term.name} path={path} ctx={ctx} /> : {domainNode}) <span style={{ color: '#666' }}>→</span> {bodyNode}
          </FocusableSpan>
        );
      } else if (term.binderKind.tag === 'BLamTT') {
        const bodyNode = renderTerm(term.body, [...path, 'body'], bodyCtx);
        return (
          <FocusableSpan path={path} ctx={ctx}>
            λ<BinderName name={term.name} path={path} ctx={ctx} />. {bodyNode}
          </FocusableSpan>
        );
      } else if (term.binderKind.tag === 'BLetTT') {
        // For focus tracking, use 'domain' path for defVal (matches original design)
        const defValNode = renderTerm(term.binderKind.defVal, [...path, 'domain'], ctx);
        const bodyNode = renderTerm(term.body, [...path, 'body'], bodyCtx);
        // Only show type annotation if present
        const typeNode = term.domain !== undefined
          ? <> : {renderTerm(term.domain, [...path, 'type'], ctx)}</>
          : null;
        return (
          <FocusableSpan path={path} ctx={ctx}>
            <span style={{ fontWeight: 'bold' }}>let</span>{' '}
            <BinderName name={term.name} path={path} ctx={ctx} />{typeNode} = {defValNode}{' '}
            <span style={{ fontWeight: 'bold' }}>in</span> {bodyNode}
          </FocusableSpan>
        );
      }
      return <span style={{ color: 'red' }}>?binder</span>;
    }

    case 'App': {
      const fnNode = renderTerm(term.fn, [...path, 'fn'], ctx);
      const argNode = renderTerm(term.arg, [...path, 'arg'], ctx);
      return (
        <FocusableSpan path={path} ctx={ctx}>
          ({fnNode} {argNode})
        </FocusableSpan>
      );
    }

    case 'Const':
      return (
        <FocusableSpan path={path} ctx={ctx}>
          <span style={{ fontFamily: 'monospace' }}>{term.name}</span>
        </FocusableSpan>
      );

    case 'Hole':
      return (
        <FocusableSpan path={path} ctx={ctx}>
          <span style={{ color: '#e91e63', fontFamily: 'monospace' }}>?{term.id}</span>
        </FocusableSpan>
      );

    case 'Annot': {
      const termNode = renderTerm(term.term, [...path, 'term'], ctx);
      const typeNode = renderTerm(term.type, [...path, 'type'], ctx);
      return (
        <FocusableSpan path={path} ctx={ctx}>
          ({termNode} : {typeNode})
        </FocusableSpan>
      );
    }
  }
}

export function TTermRenderer({
  term,
  focusPath = [],
  onFocusChange,
  onTermChange,
  isActive = true,
  readonly = false,
  inline = false,
}: TTermRendererProps) {
  // Handle name changes
  const handleNameChange = useCallback((path: TermFocusPath, newName: string) => {
    if (onTermChange && isNamePath(path)) {
      const newTerm = setNameAtPath(term, path, newName);
      if (newTerm) {
        onTermChange(newTerm);
      }
    }
  }, [term, onTermChange]);

  const ctx: RenderContext = useMemo(() => ({
    focusPath,
    onFocusChange: readonly ? undefined : onFocusChange,
    onNameChange: readonly ? undefined : handleNameChange,
    readonly,
    telescope: [],  // Start with empty telescope (no binders in scope)
  }), [focusPath, onFocusChange, handleNameChange, readonly]);

  const rendered = useMemo(
    () => renderTerm(term, [], ctx),
    [term, ctx]
  );

  return (
    <div
      style={{
        opacity: isActive ? 1 : 0.6,
        padding: inline ? '2px 4px' : '8px 12px',
        fontFamily: 'serif',
        fontSize: '16px',
      }}
    >
      {rendered}
    </div>
  );
}
