import { useState, useCallback, useEffect, useRef, useMemo } from 'react';
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
  createTransformationEquationElement,
  createCommentElement,
  LetElement,
  parseExpressionToAST,
  ProofElement
} from '../types/enhanced-focus';
import { MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
import { ExpressionInput } from './ExpressionRenderer';
import { LetManager } from './LetManager';
import { TTViewer } from './TTViewer';
import { TTerm, createRootProofTerm, mkPropTT, TermDefinition, createRootTermDefinition, mkTypeTT, mkHoleTT, isNameUsed, flattenPiBinders, getFinalReturnType, insertPiBinder, removePiBinder, setFinalReturnType, isBinderUsedDownstream, flattenLetBindings, removeLetBinding, isLetUsedDownstream, hypothesesToPi, replaceHoleTT, findHoleTT, fillHoleWithTT } from '../compiler/surface';
import {
  LetProofTerm,
  buildFullProofTerm,
  applyProofStep,
  expressionNodeToTTerm,
  applyEqualityStep
} from '../compiler/bridge';
import { NavigationProvider, useNavigation } from '../contexts/NavigationContext';
import { NavigationFooter, NavigationFooterSpacer } from './NavigationFooter';
import { createApplicationCommandTree } from '../config/navigationCommands';

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
  onApply: (rule: ExtendedRule, params?: any) => void;
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

// ============================================================================
// Helper Functions: Convert between UI types and TT types
// ============================================================================

/**
 * Convert a TT Pi-binder to a UI Assumption.
 */
function piBinderToAssumption([name, type]: [string, TTerm], id: string): Assumption {
  // Pretty-print the type
  let typeStr = '';
  if (type.tag === 'Hole') {
    // Type hole: ?type_a
    typeStr = `?${type.id}`;
  } else if (type.tag === 'Const') {
    typeStr = type.name;
  } else if (type.tag === 'Sort') {
    typeStr = type.level.tag === 'ULit' && type.level.n === 0 ? 'Prop' : 'Type';
  } else if (type.tag === 'ULevel') {
    typeStr = 'ULevel';
  } else {
    // For complex types, use pretty-print
    typeStr = astToString({ type: 'variable', value: type, children: [], raw: '' } as any);
  }

  return {
    id,
    name,
    type: {
      id: `type-${id}`,
      type: 'variable' as const,
      raw: typeStr,
      children: [],
    },
    description: `Hypothesis: ${name} has type ${typeStr}`,
    introducedBy: 'user'
  };
}

/**
 * Convert a UI Assumption to a TT Pi-binder.
 */
function assumptionToPiBinder(assumption: Assumption): [string, TTerm] {
  // Get the type string from the type node
  const typeStr = assumption.type?.raw ?? '?';

  let typeTerm: TTerm;

  // Check if this is a type hole reference (e.g., "?type_a")
  if (typeStr.startsWith('?')) {
    const typeHoleId = typeStr.substring(1);
    typeTerm = mkHoleTT(typeHoleId, mkTypeTT(1), []);
  } else if (typeStr === 'Type') {
    typeTerm = mkTypeTT(1);
  } else if (typeStr === 'Prop') {
    typeTerm = mkPropTT();
  } else {
    // Named type (e.g., "ℝ")
    typeTerm = { tag: 'Const', name: typeStr };
  }

  return [assumption.name, typeTerm];
}

function EnhancedProofWorkspaceInner() {
  // Start with null expression - proof area is empty initially
  const [currentExpression, setCurrentExpression] = useState<ExpressionNode | null>(null);

  // Get navigation context
  const navigation = useNavigation();

  const [focusPath, setFocusPath] = useState<FocusPath>([]);
  const [steps, setSteps] = useState<EnhancedProofStep[]>([]);

  // Track which proof context we're in (null = main proof, or an element id)
  const [activeProofContext, setActiveProofContext] = useState<string | null>(null);

  // Proof elements (structured proof steps - comments, equations, etc.)
  // These are separate from the TT term and are for display/UI only
  const [proofElements, setProofElements] = useState<ProofElement[]>([]);

  // State for let-bindings
  const [letBindings, setLetBindings] = useState<LetElement[]>([]);

  // UI state DERIVED from navigation path (no more React state!)
  const showEditGoal = navigation.state.navigationPath[0] === 'Goals' &&
    navigation.state.navigationPath[1] === 'Editor';
  const showAddHypothesis = navigation.state.navigationPath[0] === 'Hypotheses' &&
    navigation.state.navigationPath[1] === 'Editor';
  const showAddLet = navigation.state.navigationPath[0] === 'Let Bindings' &&
    navigation.state.navigationPath[1] === 'Editor';

  // Callbacks to close editors by popping navigation path
  const closeEditGoal = useCallback(() => {
    if (navigation.state.navigationPath.length > 1) {
      navigation.navigateTo([navigation.state.navigationPath[0]]);
    }
  }, [navigation]);

  const closeAddHypothesis = useCallback(() => {
    if (navigation.state.navigationPath.length > 1) {
      navigation.navigateTo([navigation.state.navigationPath[0]]);
    }
  }, [navigation]);

  const closeAddLet = useCallback(() => {
    if (navigation.state.navigationPath.length > 1) {
      navigation.navigateTo([navigation.state.navigationPath[0]]);
    }
  }, [navigation]);

  // ============================================================================
  // NEW ARCHITECTURE: Term Definition + Focused Hole
  // ============================================================================

  // Root term definition - the single source of truth
  // - type: contains Pi-binders (assumptions) + goal (return type)
  // - value: contains let-bindings + proof holes
  const [rootDefinition, setRootDefinition] = useState<TermDefinition>(() =>
    createRootTermDefinition('_root', [], mkPropTT(), 'proof', [])
  );

  // Store the original goal ExpressionNode (for UI display)
  // We need this because converting TT → ExpressionNode is complex
  const [goalExprNode, setGoalExprNode] = useState<ExpressionNode | null>(null);

  // Which hole are we currently working on?
  const [focusedHole, setFocusedHole] = useState<string | null>('proof');

  // Get the currently focused hole (if it exists)
  const currentHole = focusedHole ? findHoleTT(rootDefinition.value, focusedHole) : null;

  // ============================================================================
  // DERIVED STATE: Extract from TermDefinition
  // ============================================================================

  // Extract assumptions from Pi-binders in the type signature
  const assumptions = useMemo((): Assumption[] => {
    const binders = flattenPiBinders(rootDefinition.type);
    return binders.map(([name, type], index) =>
      piBinderToAssumption([name, type], `assumption-${index}`)
    );
  }, [rootDefinition.type]);

  // Goal is stored as ExpressionNode for UI display
  // The TT representation is in rootDefinition.type (final return type)
  const goal = goalExprNode;

  // Build a ProofContext for compatibility with existing code
  const metadata = useMemo((): ProofContext => ({
    assumptions
  }), [assumptions]);

  // ============================================================================
  // OLD ARCHITECTURE (keeping for compatibility during migration)
  // ============================================================================

  // Root TT term - the unified proof term model (OLD - will be removed)
  const [rootTerm, setRootTerm] = useState<TTerm>(() => {
    // Initialize with empty hypotheses and a Prop goal
    return createRootProofTerm([], mkPropTT(), 'proof', []);
  });

  // Keep rootTerm in sync with rootDefinition (temporary during migration)
  useEffect(() => {
    const binders = flattenPiBinders(rootDefinition.type);
    const goalTerm = getFinalReturnType(rootDefinition.type);
    const newRootTerm = createRootProofTerm(binders, goalTerm, 'proof', []);
    setRootTerm(newRootTerm);
  }, [rootDefinition]);

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
  }, [proofElements.length]);

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
  console.debug('Proof workspace state:', { steps: steps.length, elements: proofElements.length, assumptions: assumptions.length });

  // Helper: Update a let-binding's value in the root definition
  const updateLetValueInRootDefinition = useCallback((term: TTerm, letName: string, newValue: TTerm): TTerm => {
    // Recursively find and update the let-binding
    function updateInTerm(t: TTerm): TTerm {
      if (t.tag === 'Binder' && t.binderKind.tag === 'BLetTT' && t.name === letName) {
        // Found it! Update the defVal
        return {
          ...t,
          binderKind: { tag: 'BLetTT', defVal: newValue }
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
    // ====================================================================
    // SIMPLIFIED: Just convert the value to TT, no special equality logic
    // ====================================================================
    // Convert expression to TT
    const letValueTT = expressionNodeToTTerm(letElement.value);

    // Use type annotation if provided, otherwise create a hole for type inference
    const letTypeTT = letElement.typeAnnotation
      ? { tag: 'Const' as const, name: letElement.typeAnnotation, type: mkPropTT() }
      : mkHoleTT(`type-${letElement.name}`, mkTypeTT(0));

    // ====================================================================
    // Step 3: Add to UI state
    // ====================================================================
    setLetBindings(prev => [...prev, letElement]);
    setProofElements(prev => [...prev, letElement]);

    // ====================================================================
    // Step 4: Nest the let-binding inside the focused hole
    // ====================================================================
    if (!focusedHole) {
      console.warn('[ADD-LET] No focused hole! Cannot add let to TT term.');
      return;
    }

    const newValue = fillHoleWithTT(
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
          binderKind: { tag: 'BLetTT' as const, defVal: letValueTT },
          domain: letTypeTT,
          body: newHole
        };
      }
    );

    setRootDefinition({ ...rootDefinition, value: newValue });

    // ====================================================================
    // Step 5: Update focus to the new hole after the let-binding
    // ====================================================================
    setFocusedHole(`after-${letElement.name}`);

    // ====================================================================
    // Step 6: Activate let for interactive editing if it's from goal left/right
    // ====================================================================
    if (letElement.editorMode.tag === 'equality-left' || letElement.editorMode.tag === 'equality-right') {
      setActiveProofContext(letElement.id);
      setFocusPath([]); // Start with root focus
    }
  }, [focusedHole, rootDefinition]);

  const handleDeleteLet = useCallback((id: string) => {
    // Find the let-binding to delete
    const letBinding = letBindings.find(l => l.id === id);
    if (!letBinding) return;

    const varName = letBinding.name;

    // Find position of this let in the value term
    const lets = flattenLetBindings(rootDefinition.value);
    const position = lets.findIndex(([name]) => name === varName);

    if (position === -1) {
      console.error('Let-binding not found in value term:', varName);
      return;
    }

    // Check if used downstream (in subsequent lets or final body)
    if (isLetUsedDownstream(rootDefinition.value, varName, position)) {
      alert(`Cannot delete let-binding "${varName}": it is used in a subsequent let-binding or proof term`);
      return;
    }

    // Check if used in the goal (type signature)
    if (isNameUsed(varName, rootDefinition.type)) {
      alert(`Cannot delete let-binding "${varName}": it is used in the type signature (goal or assumptions)`);
      return;
    }

    // Safe to delete - remove from UI state
    setLetBindings(prev => prev.filter(l => l.id !== id));
    setProofElements(prev => prev.filter(e => e.id !== id));

    // Remove from TT term
    const newValue = removeLetBinding(rootDefinition.value, position);
    setRootDefinition(prev => ({
      ...prev,
      value: newValue
    }));
  }, [letBindings, rootDefinition]);

  const handleAddHypothesis = useCallback((hypothesis: Assumption) => {
    // Convert hypothesis to Pi-binder and add to type signature
    const [name, type] = assumptionToPiBinder(hypothesis);
    const newType = insertPiBinder(
      rootDefinition.type,
      flattenPiBinders(rootDefinition.type).length, // Add at end
      name,
      type
    );

    setRootDefinition(prev => ({
      ...prev,
      type: newType
    }));
  }, [rootDefinition]);

  const handleDeleteHypothesis = useCallback((id: string) => {
    // Find the hypothesis to delete by ID
    const hypothesis = assumptions.find(h => h.id === id);
    if (!hypothesis) return;

    // Find its position in the Pi-binder chain
    const binders = flattenPiBinders(rootDefinition.type);
    const position = binders.findIndex(([name]) => name === hypothesis.name);

    if (position === -1) {
      console.error('Hypothesis not found in Pi-binders:', hypothesis.name);
      return;
    }

    // Check if the binder is used downstream
    if (isBinderUsedDownstream(rootDefinition.type, hypothesis.name, position)) {
      alert(`Cannot delete hypothesis "${hypothesis.name}": it is used in the goal or other assumptions`);
      return;
    }

    // Check if used in the proof term (value)
    if (isNameUsed(hypothesis.name, rootDefinition.value)) {
      alert(`Cannot delete hypothesis "${hypothesis.name}": it is used in the proof term`);
      return;
    }

    // Safe to delete - remove from type signature
    const newType = removePiBinder(rootDefinition.type, position);
    setRootDefinition(prev => ({
      ...prev,
      type: newType
    }));
  }, [assumptions, rootDefinition]);

  // Helper: Rename a variable in an ExpressionNode (for UI display, not TTerm)
  const renameVarInExprNode = (node: ExpressionNode, oldName: string, newName: string): ExpressionNode => {
    if (oldName === newName) return node;

    // If this is a variable node with the old name, rename it
    if (node.type === 'variable' && node.value === oldName) {
      return {
        ...node,
        value: newName,
        raw: node.raw.replace(new RegExp(`\\b${oldName}\\b`, 'g'), newName)
      };
    }

    // Recursively rename in children
    if (node.children && node.children.length > 0) {
      return {
        ...node,
        children: node.children.map(child => renameVarInExprNode(child, oldName, newName)),
        raw: node.raw.replace(new RegExp(`\\b${oldName}\\b`, 'g'), newName)
      };
    }

    return node;
  };

  const handleUpdateHypothesis = useCallback((id: string, updatedHypothesis: Assumption) => {
    // Find the hypothesis by ID
    const oldHypothesis = assumptions.find(h => h.id === id);
    if (!oldHypothesis) return;

    // Find its position in the Pi-binder chain
    const binders = flattenPiBinders(rootDefinition.type);
    const position = binders.findIndex(([name]) => name === oldHypothesis.name);

    if (position === -1) {
      console.error('Hypothesis not found in Pi-binders:', oldHypothesis.name);
      return;
    }

    // Check if the old type was a hole and extract its ID
    const oldType = binders[position][1];
    const oldTypeHoleId = oldType.tag === 'Hole' ? oldType.id : null;

    // Convert updated hypothesis to Pi-binder
    const [newName, newType] = assumptionToPiBinder(updatedHypothesis);

    const oldName = oldHypothesis.name;
    const nameChanged = oldName !== newName;

    // Remove old binder and insert new one at same position
    // Note: TTerm uses De Bruijn indices, so no variable renaming needed in the type signature.
    // However, the UI goal (ExpressionNode) uses named variables and needs to be updated.
    let newTypeSignature = removePiBinder(rootDefinition.type, position);
    newTypeSignature = insertPiBinder(newTypeSignature, position, newName, newType);

    // If name changed, update the goal ExpressionNode (used for UI display)
    if (nameChanged && goalExprNode) {
      const renamedGoal = renameVarInExprNode(goalExprNode, oldName, newName);
      setGoalExprNode(renamedGoal);
    }

    setRootDefinition(prev => {
      let updatedType = newTypeSignature;
      let updatedValue = prev.value;

      // If the old type was a hole, replace all occurrences of it throughout the term
      if (oldTypeHoleId) {
        console.log(`[UPDATE-HYP] Replacing type hole ?${oldTypeHoleId} with`, newType);
        updatedType = replaceHoleTT(updatedType, oldTypeHoleId, newType);
        updatedValue = replaceHoleTT(updatedValue, oldTypeHoleId, newType);
      }

      return {
        ...prev,
        type: updatedType,
        value: updatedValue
      };
    });
  }, [assumptions, rootDefinition, goalExprNode]);

  const handleSetGoal = useCallback((goalStr: string) => {
    // Parse goal to AST
    try {
      const goalExpr = parseExpressionToAST(goalStr);

      // Store the goal ExpressionNode for UI display
      setGoalExprNode(goalExpr);

      // Add all hypotheses and goal in a single update
      setRootDefinition(prev => {
        let newType = prev.type;
        const unboundVars = new Set<string>();

        // Reserved keywords in type theory that should not be treated as variables
        const reservedKeywords = new Set(['Type', 'Prop', 'Sort']);

        // Get current binders from the type we're about to update
        const currentBinders = flattenPiBinders(newType);
        const currentBinderNames = new Set(currentBinders.map(([name]) => name));

        const extractVars = (node: ExpressionNode) => {
          if (node.type === 'variable' && typeof node.value === 'string') {
            const varName = node.value;

            // Skip reserved keywords
            if (reservedKeywords.has(varName)) {
              return;
            }

            // Check if it's not already a hypothesis or let-binding
            const isAlreadyBound =
              currentBinderNames.has(varName) ||
              letBindings.some(l => l.name === varName);

            if (!isAlreadyBound) {
              unboundVars.add(varName);
            }
          }
          node.children?.forEach(extractVars);
        };

        extractVars(goalExpr);

        // Add a Pi-binder for each unbound variable WITH TYPE HOLE
        unboundVars.forEach(varName => {
          const typeHoleId = `type_${varName}`;
          const typeHole = mkHoleTT(typeHoleId, mkTypeTT(1), []);

          // Insert Pi-binder at the end (before the goal)
          const currentBinders = flattenPiBinders(newType);
          const currentGoal = getFinalReturnType(newType);
          newType = hypothesesToPi([...currentBinders, [varName, typeHole]], currentGoal);
        });

        // Now build type context from ALL hypotheses (including newly added ones)
        const allBinders = flattenPiBinders(newType);
        const typeContext = new Map<string, TTerm>();
        allBinders.forEach(([name, type]) => {
          typeContext.set(name, type);
        });

        // Convert goal expression to TT term
        const goalTT = expressionNodeToTTerm(goalExpr, new Map(), typeContext);

        // Update the final return type in the type signature
        newType = setFinalReturnType(newType, goalTT);

        return {
          ...prev,
          type: newType
        };
      });
    } catch (error) {
      console.warn('Could not parse goal:', error);
      // On error, clear goal
      setGoalExprNode(null);
      const newType = setFinalReturnType(rootDefinition.type, mkPropTT());
      setRootDefinition(prev => ({
        ...prev,
        type: newType
      }));
    }
  }, [assumptions, letBindings, handleAddHypothesis, rootDefinition]);

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

  // ============================================================================
  // KEYBOARD NAVIGATION HANDLERS
  // ============================================================================

  // Navigation command handlers
  // Note: showEditGoal is now derived from navigation path, so these handlers are empty
  const handleEditGoalCommand = useCallback(() => {
    // Navigation path is already set by the command itself
  }, []);

  const handleSetGoalCommand = useCallback(() => {
    // Navigation path is already set by the command itself
  }, []);

  const handleClearGoalCommand = useCallback(() => {
    setGoalExprNode(null);
    const newType = setFinalReturnType(rootDefinition.type, mkPropTT());
    setRootDefinition(prev => ({
      ...prev,
      type: newType
    }));
  }, [rootDefinition]);

  const handleAddHypothesisCommand = useCallback(() => {
    // Navigation path is already set by the command itself
  }, []);

  const handleEditHypothesisCommand = useCallback(() => {
    // TODO: Trigger edit hypothesis UI - need to track selected hypothesis
    console.log('Edit hypothesis');
  }, []);

  const handleDeleteHypothesisCommand = useCallback(() => {
    // TODO: Delete selected hypothesis - need to track selected hypothesis
    console.log('Delete hypothesis');
  }, []);

  const handleAddLetBindingCommand = useCallback(() => {
    // Navigation path is already set by the command itself
  }, []);

  const handleEditLetBindingCommand = useCallback(() => {
    // TODO: Trigger edit let binding UI - need to track selected let binding
    console.log('Edit let binding');
  }, []);

  const handleDeleteLetBindingCommand = useCallback(() => {
    // TODO: Delete selected let binding - need to track selected let binding
    console.log('Delete let binding');
  }, []);

  // Update navigation metadata with command handlers
  useEffect(() => {
    navigation.updateMetadata({
      onEditGoal: handleEditGoalCommand,
      onSetGoal: handleSetGoalCommand,
      onClearGoal: handleClearGoalCommand,
      onAddHypothesis: handleAddHypothesisCommand,
      onEditHypothesis: handleEditHypothesisCommand,
      onDeleteHypothesis: handleDeleteHypothesisCommand,
      onAddLetBinding: handleAddLetBindingCommand,
      onEditLetBinding: handleEditLetBindingCommand,
      onDeleteLetBinding: handleDeleteLetBindingCommand,
      // Add any selected IDs here
      selectedHypothesisId: null, // TODO: Track selected hypothesis
      selectedLetBindingId: null, // TODO: Track selected let binding
    });
  }, [
    navigation.updateMetadata,
    handleEditGoalCommand,
    handleSetGoalCommand,
    handleClearGoalCommand,
    handleAddHypothesisCommand,
    handleEditHypothesisCommand,
    handleDeleteHypothesisCommand,
    handleAddLetBindingCommand,
    handleEditLetBindingCommand,
    handleDeleteLetBindingCommand,
  ]);

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

          const newValue = fillHoleWithTT(
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
        // Otherwise add to global proof elements
        setProofElements(prev => [...prev, equationElement]);
      }
      console.log('Applied transformation:', rule.displayName);
      console.log('  New expression:', astToString(newExpression));

      // Add new assumptions to context
      if (result.newAssumptions && result.newAssumptions.length > 0) {
        // Add each new assumption to the type signature
        result.newAssumptions.forEach((assumption: Assumption) => {
          handleAddHypothesis(assumption);
        });
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
    setProofElements(prev => [...prev, commentElement]);
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

  // ====================================================================
  // Compute rules for active let value editing
  // ====================================================================
  const activeLetBinding = useMemo(() =>
    activeProofContext ? letBindings.find(l => l.id === activeProofContext) : null,
    [activeProofContext, letBindings]
  );

  const letValueExpression = useMemo(() =>
    activeLetBinding?.value ?? null,
    [activeLetBinding]
  );

  const letValueFocusedNode = useMemo(() =>
    letValueExpression ? getNodeAtPath(letValueExpression, focusPath) : null,
    [letValueExpression, focusPath]
  );

  const letValueRulesByCategory = useMemo(() => {
    if (!letValueExpression || !letValueFocusedNode) return {};

    // Build applicable rules using the same logic as main expression
    const applicableLetRules: ExtendedRule[] = ENHANCED_FOCUS_RULES.flatMap(rule => {
      const rules: ExtendedRule[] = [];

      // Check forward direction
      if (rule.isApplicableToFocus(letValueFocusedNode, letValueExpression, metadata)) {
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
        if (rule.isApplicableReverse(letValueFocusedNode, letValueExpression, metadata)) {
          rules.push({
            ...rule,
            isReverse: true,
            displayName: rule.reverseName || `${rule.name} (Reverse)`,
            displayDescription: rule.reverseDescription || `Reverse of: ${rule.description}`,
            applyRule: (node: any, expression: any, params: any, ctx: any) => rule.applyReverse!(node, expression, params, ctx)
          });
        }
      }

      return rules;
    });

    // Group by category
    return applicableLetRules.reduce((acc, rule) => {
      if (!acc[rule.category]) acc[rule.category] = [];
      acc[rule.category].push(rule);
      return acc;
    }, {} as Record<string, ExtendedRule[]>);
  }, [letValueExpression, letValueFocusedNode, metadata]);

  const handleLetValueRuleApplication = useCallback((rule: ExtendedRule, params?: any) => {
    // TODO: Apply the rule to transform the let value
    alert(`TODO: Apply rule "${rule.displayName}" to let value\n\nRule ID: ${rule.id}\nIs Reverse: ${rule.isReverse}\nParams: ${JSON.stringify(params, null, 2)}`);
  }, []);

  return (
    <NavigationFooterSpacer>
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
                // Reset proof elements and goal
                setProofElements([]);
                setGoalExprNode(null);

                // Reset root definition with the hypothesis already included
                setRootDefinition(createRootTermDefinition('_root', [['a', { tag: 'Const', name: 'ℝ' }]], mkPropTT(), 'proof', []));
                handleSetGoal('a + a = 2 * a');
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
              hypotheses={assumptions.filter(a => {
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
              activeLetId={activeProofContext}
              onActivateLetEditor={handleActivateLetEditor}
              focusPath={focusPath}
              onFocusChange={setFocusPath}
              showFocusAsBetaRedux={true}
              showEditGoalExternal={showEditGoal}
              onShowEditGoalChange={closeEditGoal}
              showAddHypothesisExternal={showAddHypothesis}
              onShowAddHypothesisChange={closeAddHypothesis}
              showAddLetExternal={showAddLet}
              onShowAddLetChange={closeAddLet}
            />
          </div>

          {/* Show rules for active let value editing OR current main expression */}
          {letValueExpression ? (
            <RulesPanel
              rulesByCategory={letValueRulesByCategory}
              focusedNode={letValueFocusedNode}
              currentExpression={letValueExpression}
              context={metadata}
              addStep={handleLetValueRuleApplication}
            />
          ) : currentExpression ? (
            <RulesPanel
              rulesByCategory={rulesByCategory}
              focusedNode={focusedNode}
              currentExpression={currentExpression}
              context={metadata}
              addStep={addStep}
            />
          ) : null}
        </div>

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
    </NavigationFooterSpacer>
  );
}

/**
 * Main export - EnhancedProofWorkspace wrapped with NavigationProvider
 */
export function EnhancedProofWorkspace() {
  const commandTree = useMemo(() => createApplicationCommandTree(), []);

  return (
    <NavigationProvider initialCommandTree={commandTree}>
      <EnhancedProofWorkspaceInner />
      <NavigationFooter />
    </NavigationProvider>
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
  addStep: (rule: ExtendedRule, params?: any) => void;
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