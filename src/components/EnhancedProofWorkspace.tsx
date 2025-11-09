import { useState, useCallback, useEffect, useRef } from 'react';
import {
  ExpressionNode,
  FocusPath,
  EnhancedFocusRule,
  Assumption,
  ProofContext,
  getNodeAtPath,
  setNodeAtPath,
  astToString,
  ENHANCED_FOCUS_RULES,
  StructuredProof,
  createTransformationEquationElement,
  createCommentElement,
  LetElement,
  parseExpressionToAST,
  ProofElement
} from '../types/enhanced-focus';
import { MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
import { ExpressionInput } from './ExpressionRenderer';
import { ASTDebugPanel } from './ASTDebugPanel';
import { LetManager } from './LetManager';
import { TTViewer } from './TTViewer';
import { TTerm, createRootProofTerm, mkProp, TermDefinition, createRootTermDefinition, mkEq, mkType, mkHole, isNameUsed } from '../types/tt-core';
import {
  LetProofTerm,
  buildFullProofTerm,
  applyProofStep,
  expressionNodeToTTerm,
  startEqualityProof,
  applyEqualityStep
} from '../types/tt-bridge';
import { findHole, fillHoleWith } from '../types/tt-typecheck';

interface EnhancedProofStep {
  id: string;
  expression: ExpressionNode;
  focusPath: FocusPath;
  rule?: EnhancedFocusRule;
  ruleParams?: any;
  newAssumptions?: Assumption[];
  timestamp: number;
  description: string;
}

// Extended rule type that includes display properties and reverse flag
interface ExtendedRule extends EnhancedFocusRule {
  isReverse: boolean;
  displayName: string;
  displayDescription: string;
  applyRule: (node: ExpressionNode, expression: ExpressionNode, params?: any, ctx?: ProofContext) => {
    newNode: ExpressionNode;
    newAssumptions?: Assumption[];
  };
}

interface EnhancedRuleApplicationProps {
  rule: ExtendedRule;
  focusedNode: ExpressionNode | null;
  rootExpression: ExpressionNode;
  context: ProofContext;
  onApply: (rule: EnhancedFocusRule, params?: any) => void;
}

function EnhancedRuleApplication({ rule, focusedNode, onApply }: EnhancedRuleApplicationProps) {
  const [params, setParams] = useState<any>({});
  const [showParams, setShowParams] = useState(false);

  if (!focusedNode) {
    return null;
  }

  const isApplicable = true; // Already filtered in parent component

  const handleApply = () => {
    // Try to apply the rule first (it might not need params even if requiresParams is true)
    // Only show params dialog if application fails with "Need values for" error
    try {
      onApply(rule, showParams ? params : undefined);
      setShowParams(false);
      setParams({});
    } catch (error) {
      // If the error is about needing values, show the params dialog
      if (error instanceof Error && error.message.startsWith('Need values for')) {
        if (!showParams) {
          setShowParams(true);
          return;
        }
        // If params are already showing, re-throw the error
        throw error;
      }
      // For other errors, re-throw
      throw error;
    }
  };

  const handleParamChange = (paramName: string, value: string) => {
    setParams((prev: any) => ({ ...prev, [paramName]: value }));
  };

  if (!isApplicable) {
    return null;
  }

  const categoryColors = {
    equality: '#007acc',
    arithmetic: '#28a745',
    algebraic: '#ffc107',
    substitution: '#dc3545',
    introduction: '#6f42c1'
  };

  return (
    <div style={{
      margin: '6px 0',
      padding: '12px',
      border: '2px solid',
      borderColor: categoryColors[rule.category],
      borderRadius: '6px',
      backgroundColor: '#f9f9f9'
    }}>
      <div style={{ display: 'flex', justifyContent: 'flex-start', alignItems: 'flex-start', marginBottom: '8px', gap: '12px' }}>
        <button
          onClick={handleApply}
          style={{
            padding: '6px 14px',
            backgroundColor: categoryColors[rule.category],
            color: 'white',
            border: 'none',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '13px',
            fontWeight: 'bold',
            flexShrink: 0
          }}
        >
          {showParams ? 'Confirm' : 'Apply'}
        </button>
        <div style={{ flex: 1 }}>
          <div style={{ display: 'flex', alignItems: 'center', gap: '8px', marginBottom: '4px' }}>
            <strong style={{ color: categoryColors[rule.category] }}>{(rule as any).displayName}</strong>
            <span style={{
              fontSize: '10px',
              padding: '2px 6px',
              backgroundColor: categoryColors[rule.category],
              color: 'white',
              borderRadius: '10px',
              textTransform: 'uppercase',
              fontWeight: 'bold'
            }}>
              {rule.category}
            </span>
          </div>
        </div>
      </div>
      <div style={{ fontSize: '13px', color: '#666', marginBottom: '4px' }}>
        <MathJaxExpressionRendererRaw
          expression={(rule as any).displayDescription}
          readonly={true}
          inline={false}
        />
      </div>
      <div style={{ fontSize: '12px', color: '#888', fontFamily: 'monospace' }}>
        On: <span style={{ backgroundColor: '#e6f3ff', padding: '1px 4px', borderRadius: '2px' }}>
          {focusedNode.raw}
        </span>
      </div>

      {showParams && rule.requiresParams && rule.paramTemplate && (
        <div style={{ marginTop: '8px', padding: '8px', backgroundColor: '#f0f0f0', borderRadius: '4px' }}>
          {Object.entries(rule.paramTemplate).map(([paramName, description]) => (
            <div key={paramName} style={{ marginBottom: '6px' }}>
              <label style={{ fontSize: '12px', color: '#666', display: 'block', marginBottom: '2px' }}>
                {description}:
              </label>
              {paramName === 'expression' ? (
                <>
                  <ExpressionInput
                    value={params[paramName] || ''}
                    onChange={(value) => handleParamChange(paramName, value)}
                    placeholder={`Enter ${paramName}...`}
                    autoFocus={true}
                    onKeyPress={(e) => {
                      if (e.key === 'Enter' && params[paramName]?.trim()) {
                        handleApply();
                      }
                    }}
                  />
                  <div style={{ fontSize: '10px', color: '#999', marginTop: '2px' }}>
                    Press Enter or click Confirm to apply
                  </div>
                </>
              ) : (
                <input
                  type="text"
                  placeholder={`Enter ${paramName}...`}
                  value={params[paramName] || ''}
                  onChange={(e) => handleParamChange(paramName, e.target.value)}
                  onKeyPress={(e) => {
                    if (e.key === 'Enter' && params[paramName]?.trim()) {
                      handleApply();
                    }
                  }}
                  style={{
                    width: '100%',
                    padding: '4px 8px',
                    fontFamily: 'monospace',
                    border: '1px solid #ccc',
                    borderRadius: '4px',
                    fontSize: '12px'
                  }}
                />
              )}
            </div>
          ))}
        </div>
      )}
    </div>
  );
}


// EnhancedProofHistory component removed - not currently used but can be re-added if needed

export function EnhancedProofWorkspace() {
  // Start with null expression - proof area is empty initially
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode | null>(null);

  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [steps, setSteps] = useState<EnhancedProofStep[]>([]);

  // Track which proof context we're in (null = main proof, or an element id)
  const [activeProofContext, setActiveProofContext] = useState<string | null>(null);
  const [showASTDebug, setShowASTDebug] = useState(false);
  const [structuredProof, setStructuredProof] = useState<StructuredProof>({
    elements: [],
    metadata: {
      assumptions: [],
      goal: null  // Goal should be null initially, not currentExpression
    }
  });

  const { metadata } = structuredProof
  const { goal } = metadata

  const setGoal = useCallback((newGoal: ExpressionNode | null) => {
    setStructuredProof(current => {
      return {
        ...current,
        metadata: { ...current.metadata, goal: newGoal }
      }
    })
  }, [setStructuredProof])

  // State for claim insertion

  // State for let-bindings
  const [letBindings, setLetBindings] = useState<LetElement[]>([]);

  // ============================================================================
  // NEW ARCHITECTURE: Term Definition + Focused Hole
  // ============================================================================

  // Root term definition - replaces the awkward let-wrapper
  const [rootDefinition, setRootDefinition] = useState<TermDefinition>(() =>
    createRootTermDefinition('_root', [], mkProp(), 'proof', [])
  );

  // Which hole are we currently working on?
  const [focusedHole, setFocusedHole] = useState<string | null>('proof');

  // Get all available holes (for debugging/future use)
  // const availableHoles = extractHoles(rootDefinition.value);

  // Get the currently focused hole (if it exists)
  const currentHole = focusedHole ? findHole(rootDefinition.value, focusedHole) : null;

  // ============================================================================
  // OLD ARCHITECTURE (will be removed in Phase 9)
  // ============================================================================

  // Root TT term - the unified proof term model
  const [rootTerm, setRootTerm] = useState<TTerm>(() => {
    // Initialize with empty hypotheses and a Prop goal
    return createRootProofTerm([], mkProp(), 'proof', []);
  });

  // Update rootTerm and rootDefinition whenever hypotheses or goal change
  useEffect(() => {
    // Convert UI hypotheses to TT term format
    const ttHypotheses: Array<[string, TTerm]> = metadata.assumptions.map(h => {
      // Parse the hypothesis expression to extract type
      // Format is either "name : Type" or just "Type"
      const match = h.expression.match(/^\s*(\w+)\s*:\s*(.+)$/);
      let typeTerm: TTerm;

      if (match) {
        const typeStr = match[2].trim();
        // Check if this is a type hole reference (e.g., "?type_a")
        if (typeStr.startsWith('?')) {
          // Create a type hole: the hole's type is Type_1
          const typeHoleId = typeStr.substring(1); // Remove the '?'
          typeTerm = mkHole(typeHoleId, mkType(1), []);
        } else if (typeStr === 'Type') {
          typeTerm = mkType(1);
        } else if (typeStr === 'Prop') {
          typeTerm = mkProp();
        } else {
          // Named type (e.g., "ℝ")
          typeTerm = { tag: 'Const', name: typeStr, type: mkProp() };
        }
      } else {
        // No type specified, use Prop
        typeTerm = mkProp();
      }

      return [h.name, typeTerm];
    });

    // Build type context from hypotheses
    const typeContext = new Map<string, TTerm>();
    ttHypotheses.forEach(([name, type]) => {
      typeContext.set(name, type);
    });

    // Convert goal ExpressionNode to TT term properly, passing type context
    const goalTerm = goal ? expressionNodeToTTerm(goal, new Map(), typeContext) : mkProp();

    // OLD: Create updated root term (let-wrapper)
    const newRootTerm = createRootProofTerm(ttHypotheses, goalTerm, 'proof', []);
    setRootTerm(newRootTerm);

    // NEW: Create updated term definition
    const newDefinition = createRootTermDefinition('_root', ttHypotheses, goalTerm, 'proof', []);
    setRootDefinition(newDefinition);
    setFocusedHole('proof'); // Reset focus to initial hole
  }, [metadata.assumptions, goal]);

  // TT proof terms: Map from let-binding ID to its proof term
  const [letProofTerms, setLetProofTerms] = useState<Map<string, LetProofTerm>>(new Map());

  // Combined TT proof term for display (built from all let-bindings)
  const [_ttProofTerm, setTtProofTerm] = useState<TTerm | null>(null);

  const proofScrollRef = useRef<HTMLDivElement>(null);

  // Get the focused node in the current expression
  const focusedNode = currentExpression ? getNodeAtPath(currentExpression, focusPath) : null;

  // Auto-scroll to bottom when proof steps are added
  useEffect(() => {
    if (proofScrollRef.current) {
      proofScrollRef.current.scrollTop = proofScrollRef.current.scrollHeight;
    }
  }, [structuredProof.elements.length]);

  // Rebuild combined TT proof term when let-proof-terms change
  useEffect(() => {
    const proofs = Array.from(letProofTerms.values());
    if (proofs.length > 0) {
      const combined = buildFullProofTerm(proofs);
      setTtProofTerm(combined);
    } else {
      setTtProofTerm(null);
    }
  }, [letProofTerms]);

  // Debug info for development
  console.debug('Proof workspace state:', { steps: steps.length, elements: structuredProof.elements.length });

  // Helper: Update a let-binding's value in the root definition
  const updateLetValueInRootDefinition = useCallback((term: TTerm, letName: string, newValue: TTerm): TTerm => {
    // Recursively find and update the let-binding
    function updateInTerm(t: TTerm): TTerm {
      if (t.tag === 'Binder' && t.binderKind.tag === 'BLet' && t.name === letName) {
        // Found it! Update the defVal
        return {
          ...t,
          binderKind: { tag: 'BLet', defVal: newValue }
        };
      }

      if (t.tag === 'Binder') {
        // Recurse into body
        return {
          ...t,
          body: updateInTerm(t.body)
        };
      }

      // Not a binder, return unchanged
      return t;
    }

    return updateInTerm(term);
  }, []);

  // Handlers for let-bindings and hypotheses
  const handleAddLet = useCallback((letElement: LetElement) => {
    console.log('[ADD-LET] Starting, focusedHole:', focusedHole, 'editorMode:', letElement.editorMode.tag);

    // ====================================================================
    // Step 1: Initialize equality proof state if this is an equality proof
    // ====================================================================
    const isEqualityProof = letElement.editorMode.tag === 'equality-left' || letElement.editorMode.tag === 'equality-right';

    if (isEqualityProof && goal) {
      try {
        // Parse goal as equality A = B
        const goalStr = astToString(goal);
        const eqMatch = goalStr.match(/^(.+?)\s*=\s*(.+)$/);

        if (eqMatch) {
          const leftStr = eqMatch[1].trim();
          const rightStr = eqMatch[2].trim();

          // Convert to TT terms
          const leftTT = expressionNodeToTTerm(parseExpressionToAST(leftStr));
          const rightTT = expressionNodeToTTerm(parseExpressionToAST(rightStr));

          // Initialize equality proof state
          const direction = letElement.editorMode.tag === 'equality-left' ? 'left' : 'right';
          const eqState = startEqualityProof(leftTT, rightTT, direction);

          // Attach to let element
          letElement.equalityProofState = eqState;

          console.log('[ADD-LET] Created equality proof state:', {
            start: direction === 'left' ? leftStr : rightStr,
            target: direction === 'left' ? rightStr : leftStr,
            holeId: eqState.currentHoleId,
            direction
          });
        }
      } catch (error) {
        console.error('[ADD-LET] Failed to initialize equality proof state:', error);
      }
    }

    // ====================================================================
    // Step 2: Determine TT type and value for the let-binding
    // ====================================================================
    let letValueTT: TTerm;
    let letTypeTT: TTerm;

    if (letElement.equalityProofState) {
      // Equality proof: use the proof term (a Hole) as value
      letValueTT = letElement.equalityProofState.proofTerm;
      letTypeTT = mkEq(
        letElement.equalityProofState.startExpr,
        letElement.equalityProofState.targetExpr
      );
      console.log('[ADD-LET] Using equality proof term:', {
        proofTerm: letElement.equalityProofState.proofTerm,
        type: letTypeTT
      });
    } else {
      // Regular let: convert expression to TT
      letValueTT = expressionNodeToTTerm(letElement.value);
      letTypeTT = letElement.typeAnnotation
        ? { tag: 'Const' as const, name: letElement.typeAnnotation, type: mkProp() }
        : mkProp();
      console.log('[ADD-LET] Using regular value');
    }

    // ====================================================================
    // Step 3: Add to UI state
    // ====================================================================
    setLetBindings(prev => [...prev, letElement]);
    setStructuredProof(prev => ({
      ...prev,
      elements: [...prev.elements, letElement]
    }));

    // ====================================================================
    // Step 4: Nest the let-binding inside the focused hole
    // ====================================================================
    if (!focusedHole) {
      console.warn('[ADD-LET] No focused hole! Cannot add let to TT term.');
      return;
    }

    const newValue = fillHoleWith(
      rootDefinition.value,
      focusedHole,
      (holeType, holeContext) => {
        // Create a new hole after this let-binding
        const newHoleId = `after-${letElement.name}`;
        const newHole = {
          tag: 'Hole' as const,
          id: newHoleId,
          type: holeType,
          context: [...holeContext, { name: letElement.name, type: letTypeTT }]
        };

        // Create the let-binding that wraps the new hole
        return {
          tag: 'Binder' as const,
          name: letElement.name,
          binderKind: { tag: 'BLet' as const, defVal: letValueTT },
          domain: letTypeTT,
          body: newHole
        };
      }
    );

    setRootDefinition({ ...rootDefinition, value: newValue });

    // ====================================================================
    // Step 5: Update focus to the correct hole
    // ====================================================================
    const newFocus = letElement.equalityProofState
      ? letElement.equalityProofState.currentHoleId  // Focus on proof hole INSIDE let's value
      : `after-${letElement.name}`;                   // Focus on hole AFTER let

    console.log('[ADD-LET] Setting focus to:', newFocus);
    setFocusedHole(newFocus);
  }, [focusedHole, rootDefinition, goal]);

  const handleDeleteLet = useCallback((id: string) => {
    // Find the let-binding to delete
    const letBinding = letBindings.find(l => l.id === id);
    if (!letBinding) return;

    const varName = letBinding.name;

    // Check if this let-binding is used in the goal
    if (goal) {
      const typeContext = new Map<string, TTerm>();
      // Build type context (simplified - we'd need full context for complete check)
      const goalTerm = expressionNodeToTTerm(goal, new Map(), typeContext);
      if (isNameUsed(varName, goalTerm)) {
        alert(`Cannot delete let-binding "${varName}": it is used in the goal expression`);
        return;
      }
    }

    // Check if used in other let-bindings
    for (const otherLet of letBindings) {
      if (otherLet.id === id) continue; // Skip self

      // Check the name itself - if another let has the same name, it depends on this one
      if (otherLet.name === varName) continue; // Same name is OK (shadowing)

      // Check if the value expression uses this name
      // For now, do a simple string check on the raw expression
      if (otherLet.value.raw.includes(varName)) {
        alert(`Cannot delete let-binding "${varName}": it is used in "${otherLet.name}"`);
        return;
      }
    }

    // Check if used in root definition
    if (isNameUsed(varName, rootDefinition.type)) {
      alert(`Cannot delete let-binding "${varName}": it is used in the theorem type`);
      return;
    }

    if (isNameUsed(varName, rootDefinition.value)) {
      alert(`Cannot delete let-binding "${varName}": it is used in the proof term`);
      return;
    }

    // Safe to delete
    setLetBindings(prev => prev.filter(l => l.id !== id));

    // Also remove from structured proof
    setStructuredProof(prev => ({
      ...prev,
      elements: prev.elements.filter(e => e.id !== id)
    }));
  }, [letBindings, goal, rootDefinition]);

  const handleAddHypothesis = useCallback((hypothesis: Assumption) => {
    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: [...prev.metadata.assumptions, hypothesis]
      }
    }));
  }, []);

  const handleDeleteHypothesis = useCallback((id: string) => {
    // Find the hypothesis to delete
    const hypothesis = metadata.assumptions.find(h => h.id === id);
    if (!hypothesis) return;

    const varName = hypothesis.name;

    // Build type context for checking
    const typeContext = new Map<string, TTerm>();
    metadata.assumptions.forEach(h => {
      if (h.id === id) return; // Skip the one we're deleting
      const match = h.expression.match(/^\s*(\w+)\s*:\s*(.+)$/);
      if (match) {
        const name = match[1].trim();
        const typeStr = match[2].trim();
        if (typeStr.startsWith('?')) {
          const typeHoleId = typeStr.substring(1);
          typeContext.set(name, mkHole(typeHoleId, mkType(1), []));
        }
      }
    });

    // Check if variable is used in the goal
    if (goal) {
      const goalTerm = expressionNodeToTTerm(goal, new Map(), typeContext);
      if (isNameUsed(varName, goalTerm)) {
        alert(`Cannot delete hypothesis "${varName}": it is used in the goal expression`);
        return;
      }
    }

    // Check if used in root definition
    if (isNameUsed(varName, rootDefinition.type)) {
      alert(`Cannot delete hypothesis "${varName}": it is used in the theorem type`);
      return;
    }

    if (isNameUsed(varName, rootDefinition.value)) {
      alert(`Cannot delete hypothesis "${varName}": it is used in the proof term`);
      return;
    }

    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: prev.metadata.assumptions.filter(a => a.id !== id)
      }
    }));
  }, [metadata, goal, rootDefinition]);

  const handleUpdateHypothesis = useCallback((id: string, updatedHypothesis: Assumption) => {
    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: prev.metadata.assumptions.map(a => a.id === id ? updatedHypothesis : a)
      }
    }));
  }, []);

  const handleSetGoal = useCallback((goalStr: string) => {
    // Parse goal to AST immediately
    try {
      const goalExpr = parseExpressionToAST(goalStr);
      setGoal(goalExpr);
      const unboundVars = new Set<string>();

      // Reserved keywords in type theory that should not be treated as variables
      const reservedKeywords = new Set(['Type', 'Prop', 'Sort']);

      const extractVars = (node: ExpressionNode) => {
        if (node.type === 'variable' && typeof node.value === 'string') {
          const varName = node.value;

          // Skip reserved keywords
          if (reservedKeywords.has(varName)) {
            return;
          }

          // Check if it's not already a hypothesis or let-binding
          const isAlreadyBound =
            metadata.assumptions.some(h => h.name === varName) ||
            letBindings.some(l => l.name === varName);

          if (!isAlreadyBound) {
            unboundVars.add(varName);
          }
        }
        node.children?.forEach(extractVars);
      };

      extractVars(goalExpr);

      // Create hypotheses for each unbound variable
      unboundVars.forEach(varName => {
        const typeHoleId = `type_${varName}`;
        const hypothesis: Assumption = {
          id: crypto.randomUUID(),
          name: varName,
          expression: `${varName} : ?${typeHoleId}`,
          description: `Auto-generated from goal: ${varName} has unknown type ?${typeHoleId}`,
          introducedBy: 'auto',
          typeHoleId: typeHoleId  // Track the type hole ID
        };
        handleAddHypothesis(hypothesis);
      });
    } catch (error) {
      console.warn('Could not parse goal:', error);
      // On error, set goal to null
      setGoal(null);
    }

    // TODO: When we have a root TT term, update it using setGoalInRoot()
  }, [metadata.assumptions, letBindings, handleAddHypothesis]);

  // Handler to activate a let-binding for editing in the proof workspace
  const handleActivateLetEditor = useCallback((letId: string) => {
    const letBinding = letBindings.find(l => l.id === letId);
    if (!letBinding) return;

    // Set this as the active proof context
    setActiveProofContext(letId);

    // For equality modes, initialize with the starting expression
    if (letBinding.editorMode?.tag === 'equality-left' || letBinding.editorMode?.tag === 'equality-right') {
      const startExpr = (letBinding.editorMode as any).startExpr;
      if (startExpr) {
        setCurrentExpression(startExpr);
        setFocusPath([]);
      }
    }
  }, [letBindings]);

  // Keyboard navigation handler (unused - reserved for future keyboard shortcuts)
  // const handleKeyDown = useCallback((e: React.KeyboardEvent) => { ... }, []);

  const addStep = useCallback((rule: any, params?: any) => {
    if (!focusedNode || !currentExpression) {
      alert('No focused node to apply rule to');
      return;
    }

    try {
      const result = rule.applyRule(focusedNode, currentExpression, params, metadata);
      const newExpression = setNodeAtPath(currentExpression, focusPath, result.newNode);

      // Update the raw string of the new expression
      newExpression.raw = astToString(newExpression);

      const newStep: EnhancedProofStep = {
        id: crypto.randomUUID(),
        expression: newExpression,
        focusPath: [...focusPath],
        rule,
        ruleParams: params,
        newAssumptions: result.newAssumptions,
        timestamp: Date.now(),
        description: `Applied ${rule.displayName} to "${focusedNode.raw}"`
      };

      // Update the current expression
      setCurrentExpression(newExpression);
      setSteps(prev => [...prev, newStep]);

      // Create equation element for the transformation
      const equationElement = createTransformationEquationElement(
        currentExpression,   // previous expression (the one we transformed)
        newExpression,      // new expression (after transformation)
        rule.displayName,
        rule.id
      );

      // ====================================================================
      // NEW: Apply rule to focused hole using equality proof system
      // ====================================================================
      if (focusedHole && currentHole && currentHole.tag === 'Hole') {
        console.log('[RULE-APPLY] FocusedHole:', focusedHole, 'Rule:', rule.displayName);

        // Find the let-binding we're currently working on
        const activeLet = letBindings.find(l =>
          l.editorExpanded &&
          (l.editorMode.tag === 'equality-left' || l.editorMode.tag === 'equality-right')
        );

        console.log('[RULE-APPLY] Active let:', activeLet?.name, 'Has eqState:', !!activeLet?.equalityProofState);

        if (activeLet?.equalityProofState) {
          // We're in an equality proof! Apply the equality step
          console.log('[RULE-APPLY] Applying equality step to hole:', activeLet.equalityProofState.currentHoleId);

          // Convert new expression to TT term
          const newExprTT = expressionNodeToTTerm(newExpression);

          // Apply the equality step
          const newState = applyEqualityStep(
            activeLet.equalityProofState,
            rule.displayName,
            newExprTT
          );

          console.log('[RULE-APPLY] New equality state:', {
            currentExpr: newState.currentExpr,
            newHoleId: newState.currentHoleId,
            isComplete: newState.isComplete
          });

          // Update the let-binding with new state
          setLetBindings(prev => prev.map(l =>
            l.id === activeLet.id
              ? { ...l, equalityProofState: newState }
              : l
          ));

          // Update the root definition
          // Find the let-binding in the term and update its value
          const letName = activeLet.name;
          const newValue = updateLetValueInRootDefinition(
            rootDefinition.value,
            letName,
            newState.proofTerm
          );

          setRootDefinition({ ...rootDefinition, value: newValue });

          // Update focus to the new hole (or clear if complete)
          if (newState.isComplete) {
            console.log('[RULE-APPLY] Equality proof complete!');
            setFocusedHole(null);
          } else {
            console.log('[RULE-APPLY] Updating focus to new hole:', newState.currentHoleId);
            setFocusedHole(newState.currentHoleId);
          }
        } else {
          // Not an equality proof, use placeholder
          console.log('[RULE-APPLY] Non-equality rule application, filling hole:', focusedHole);

          const proofTerm = {
            tag: 'Const' as const,
            name: `${rule.displayName}_applied`,
            type: currentHole.type
          };

          const newValue = fillHoleWith(
            rootDefinition.value,
            focusedHole,
            () => proofTerm
          );

          setRootDefinition({ ...rootDefinition, value: newValue });
          setFocusedHole(null);
        }
      }

      // ====================================================================
      // OLD: Add transformation to proof elements (only if new system not active)
      // ====================================================================
      // If we're in an active proof context (proving a let-claim), add to that claim's proof
      // BUT: Only use old system if we're not using the new focused-hole system
      if (activeProofContext && !focusedHole) {
        setLetBindings(prev => prev.map(l => {
          if (l.id === activeProofContext && l.proofElements) {
            return {
              ...l,
              proofElements: [...l.proofElements, equationElement]
            };
          }
          return l;
        }));

        // UPDATE TT PROOF TERM for this step
        setLetProofTerms(prev => {
          const currentProof = prev.get(activeProofContext);
          if (currentProof) {
            console.log('[OLD ARCH] Applying proof step:', rule.displayName, 'to proof term');
            const updatedProof = applyProofStep(
              currentProof,
              currentExpression,
              newExpression,
              { name: rule.displayName, id: rule.id, params }
            );
            console.log('[OLD ARCH] Updated proof term:', updatedProof);
            const newMap = new Map(prev);
            newMap.set(activeProofContext, updatedProof);
            return newMap;
          }
          // Silently ignore - new system is handling this
          return prev;
        });
      } else if (!focusedHole) {
        // Otherwise add to global structured proof
        setStructuredProof(prev => ({
          ...prev,
          elements: [...prev.elements, equationElement]
        }));
      }
      console.log('Applied transformation:', rule.displayName);
      console.log('  New expression:', astToString(newExpression));

      // Add new assumptions to context
      if (result.newAssumptions && result.newAssumptions.length > 0) {
        // Update structured proof metadata
        setStructuredProof(prev => ({
          ...prev,
          metadata: {
            ...prev.metadata,
            assumptions: [...prev.metadata.assumptions, ...result.newAssumptions!]
          }
        }));
      }

    } catch (error) {
      console.error('Error applying rule:', error);
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      const focusedNodeStr = focusedNode ? astToString(focusedNode) : 'unknown expression';
      alert(`Error applying rule "${rule.displayName}" to "${focusedNodeStr}":\n\n${errorMessage}`);
    }
  }, [currentExpression, focusPath, focusedNode, metadata]);

  const addComment = useCallback((content: string, commentType: 'explanation' | 'assumption' | 'goal' | 'strategy' = 'explanation') => {
    const commentElement = createCommentElement(content, commentType);
    setStructuredProof(prev => ({
      ...prev,
      elements: [...prev.elements, commentElement]
    }));
  }, []);


  // Unused - kept for potential future undo/redo functionality
  // const deleteProofElement = useCallback((index: number) => { ... }, []);

  // Get applicable rules, including both forward and reverse directions for bidirectional rules
  const applicableRules: ExtendedRule[] = (focusedNode && currentExpression) ? ENHANCED_FOCUS_RULES.flatMap(rule => {
    const rules: ExtendedRule[] = [];

    // Check forward direction
    if (rule.isApplicableToFocus(focusedNode, currentExpression, metadata)) {
      rules.push({
        ...rule,
        isReverse: false,
        displayName: rule.name,
        displayDescription: rule.description,
        applyRule: (node: any, expression: any, params: any, ctx: any) => rule.applyToFocus(node, expression, params, ctx)
      });
    }

    // Check reverse direction for bidirectional rules
    if (rule.bidirectional && rule.isApplicableReverse && rule.applyReverse) {
      if (rule.isApplicableReverse(focusedNode, currentExpression, metadata)) {
        // Check if reverse direction needs parameters
        // This happens when the 'to' pattern has fewer variables than 'from'
        // For example: div_self: x/x -> 1, reverse: 1 -> x/x needs x
        // For example: sub_self: a-a -> 0, reverse: 0 -> a-a needs a
        const reverseNeedsParams = rule.requiresParams ||
          ['div_self', 'sub_self', 'mul_one_left', 'mul_one_right', 'add_zero_left', 'add_zero_right'].includes(rule.id);

        // Create appropriate param template if needed
        let reverseParamTemplate = rule.paramTemplate;
        if (reverseNeedsParams && !rule.paramTemplate) {
          // Auto-generate param template for common reverse patterns
          if (rule.id === 'div_self') {
            reverseParamTemplate = { x: 'Enter expression for x' };
          } else if (rule.id === 'sub_self') {
            reverseParamTemplate = { a: 'Enter expression for a' };
          } else if (rule.id === 'mul_one_left' || rule.id === 'mul_one_right') {
            reverseParamTemplate = { a: 'Enter expression to multiply by 1' };
          } else if (rule.id === 'add_zero_left' || rule.id === 'add_zero_right') {
            reverseParamTemplate = { a: 'Enter expression to add 0 to' };
          }
        }

        rules.push({
          ...rule,
          isReverse: true,
          displayName: rule.reverseName || `${rule.name} (Reverse)`,
          displayDescription: rule.reverseDescription || `Reverse of: ${rule.description}`,
          requiresParams: reverseNeedsParams,
          paramTemplate: reverseParamTemplate,
          applyRule: (node: any, expression: any, params: any, ctx: any) => rule.applyReverse!(node, expression, params, ctx)
        });
      }
    }

    return rules;
  }) : [];

  // Group rules by category
  const rulesByCategory = applicableRules.reduce((acc, rule) => {
    if (!acc[rule.category]) acc[rule.category] = [];
    acc[rule.category].push(rule);
    return acc;
  }, {} as Record<string, ExtendedRule[]>);

  // Create expression element for current expression
  // Unused - equation element rendering (reserved for future UI improvements)
  // const currentEquationElement = currentExpression ? (
  //   <MathJaxExpressionRenderer ... />
  // ) : null

  // Unused - chaining detection (reserved for future proof display)
  // const currentEquationIsChained = currentExpression && structuredProof.elements.length > 0 ?
  //   elementIsChained(structuredProof.elements[structuredProof.elements.length - 1], currentExpression) : false;

  return (
    <div style={{
      padding: '20px',
      fontFamily: 'system-ui, sans-serif',
      maxWidth: '1200px',
      margin: '0 auto'
    }}>
      <div style={{
        display: 'flex',
        justifyContent: 'space-between',
        alignItems: 'center',
        marginBottom: '24px',
        borderBottom: '2px solid #007acc',
        paddingBottom: '16px'
      }}>
        <h2 style={{ margin: 0, color: '#007acc' }}>Mathematical Proof Workspace</h2>
        <div style={{ display: 'flex', gap: '12px' }}>
          <button
            onClick={() => {
              setStructuredProof(_value => {
                return {
                  elements: [] as ProofElement[],
                  metadata: {
                    assumptions: [{
                      id: crypto.randomUUID(),
                      name: 'a',
                      expression: 'a : ℝ',
                      description: '',
                      introducedBy: 'template',
                    }] as Assumption[],
                    goal: parseExpressionToAST('a + a = 2 * a'),
                  }
                }
              })
            }}
            style={{
              padding: '8px 16px',
              backgroundColor: '#2845a7',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 'bold'
            }}
          >
            a+a=2*a
          </button>
          <button
            onClick={() => {
              const comment = prompt('Add a comment to the proof:');
              if (comment && comment.trim()) {
                const type = confirm('Is this an explanation comment? (Cancel for assumption/strategy)')
                  ? 'explanation' : 'strategy';
                addComment(comment.trim(), type);
              }
            }}
            style={{
              padding: '8px 16px',
              backgroundColor: '#28a745',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 'bold'
            }}
          >
            ➕ Add Comment
          </button>
        </div>
      </div>

      <div style={{
        display: 'grid',
        gridTemplateColumns: '2fr 1fr',
        gap: '24px',
        alignItems: 'start',
        height: 'calc(100vh - 200px)' // Fill viewport minus space for header/margins
      }}>
        {/* Main Proof Area */}
        <div style={{
          backgroundColor: 'white',
          border: '2px solid #e9ecef',
          borderRadius: '12px',
          padding: '24px',
          boxShadow: '0 4px 6px rgba(0, 0, 0, 0.05)',
          minHeight: '600px',
          height: '100%',
          overflowY: 'auto'
        }}>
          <LetManager
            letBindings={letBindings}
            hypotheses={metadata.assumptions.filter(a => {
              // Only show IH when we're in the inductive step context
              if (a.introducedBy === 'induction') {
                return activeProofContext && activeProofContext.endsWith('-inductive');
              }
              return true;
            })}
            goal={goal}
            onAddLet={handleAddLet}
            onDeleteLet={handleDeleteLet}
            onAddHypothesis={handleAddHypothesis}
            onDeleteHypothesis={handleDeleteHypothesis}
            onUpdateHypothesis={handleUpdateHypothesis}
            onSetGoal={handleSetGoal}
            onActivateLetEditor={handleActivateLetEditor}
            activeLetId={activeProofContext}
            currentExpression={currentExpression}
            focusPath={focusPath}
            onFocusChange={setFocusPath}
          />
        </div>

        {currentExpression && (
          <RulesPanel
            rulesByCategory={rulesByCategory}
            focusedNode={focusedNode}
            currentExpression={currentExpression}
            context={metadata}
            addStep={addStep}
          />
        )}
      </div>

      {/* AST Debug Panel */}
      {currentExpression && (
        <ASTDebugPanel
          expression={currentExpression}
          isVisible={showASTDebug}
          onToggle={() => setShowASTDebug(!showASTDebug)}
        />
      )}


      {/* TT Proof Term Viewer */}
      <div style={{ marginTop: '24px' }}>
        {/* Debug info */}
        {activeProofContext && (
          <div style={{
            padding: '8px',
            backgroundColor: '#e3f2fd',
            border: '1px solid #2196f3',
            borderRadius: '4px',
            marginBottom: '12px',
            fontSize: '12px',
            fontFamily: 'monospace'
          }}>
            <strong>Debug:</strong> Active proof context: {activeProofContext},
            Proof terms in map: {letProofTerms.size},
            Has proof for active: {letProofTerms.has(activeProofContext) ? 'YES' : 'NO'}
          </div>
        )}
        <TTViewer
          proofTerm={rootTerm}
          termDefinition={rootDefinition}
          context={[]}
        />
      </div>
    </div>
  );
}

// Unused - element chaining detection (reserved for future proof display improvements)
// function elementIsChained(previousElement: ProofElement, currentElement: ExpressionNode) { ... }


// Unused - proof comment rendering (reserved for future proof annotation features)
// function ProofComment({ element }: { element: CommentElement }) { ... }

function RulesPanel({
  rulesByCategory,
  focusedNode,
  currentExpression,
  context,
  addStep
}: {
  rulesByCategory: Record<string, ExtendedRule[]>;
  focusedNode: ExpressionNode | null;
  currentExpression: ExpressionNode;
  context: ProofContext;
  addStep: (rule: EnhancedFocusRule, params?: any) => void;
}) {
  return (
    <div style={{
      backgroundColor: '#f8f9fa',
      border: '1px solid #e9ecef',
      borderRadius: '8px',
      padding: '20px',
      height: '100%', // Fill parent grid cell
      maxHeight: 'calc(100vh - 200px)', // But don't exceed viewport
      overflowY: 'auto',
      display: 'flex',
      flexDirection: 'column'
    }}>
      <h3 style={{ marginTop: 0, marginBottom: '16px', color: '#495057', flexShrink: 0 }}>Available Rules</h3>
      <div style={{ flex: 1, overflowY: 'auto', minHeight: 0 }}>
        {Object.keys(rulesByCategory).length > 0 ? (
          Object.entries(rulesByCategory).map(([category, rules]) => (
            <div key={category} style={{ marginBottom: '20px' }}>
              <h4 style={{
                margin: '0 0 12px 0',
                fontSize: '14px',
                textTransform: 'capitalize',
                color: '#666',
                borderBottom: '1px solid #dee2e6',
                paddingBottom: '4px'
              }}>
                {category} Rules ({rules.length})
              </h4>
              <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
                {rules.map(rule => (
                  <EnhancedRuleApplication
                    key={`${rule.id}${rule.isReverse ? '-reverse' : ''}`}
                    rule={rule}
                    focusedNode={focusedNode}
                    rootExpression={currentExpression}
                    context={context}
                    onApply={addStep}
                  />
                ))}
              </div>
            </div>
          ))
        ) : (
          <div style={{
            padding: '16px',
            backgroundColor: '#fff3cd',
            borderRadius: '6px',
            color: '#856404',
            fontStyle: 'italic',
            textAlign: 'center'
          }}>
            Click on part of the expression to see available rules
          </div>
        )}
      </div>
    </div>
  );
}

// generateEnhancedLeanProof function removed - not currently used but can be re-added if needed