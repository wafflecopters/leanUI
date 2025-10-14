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
  CommentElement,
  EquationElement,
  ProofElement,
  InductionProofElement,
  substituteVariableInExpression,
  LetElement,
  createLetElement,
  parseExpressionToAST
} from '../types/enhanced-focus';
import { FocusBreadcrumbs } from './FocusedExpressionRenderer';
import { MathJaxExpressionRenderer, MathJaxExpressionRendererRaw } from './MathJaxExpressionRenderer';
import { ExpressionInput } from './ExpressionRenderer';
import { ASTDebugPanel } from './ASTDebugPanel';
import { LetManager } from './LetManager';
import { TTViewer } from './TTViewer';
import { TTerm, createRootProofTerm, mkProp } from '../types/tt-core';
import {
  LetProofTerm,
  createEqualityProofTerm,
  buildFullProofTerm,
  applyProofStep
} from '../types/tt-bridge';

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
  const [context, setContext] = useState<ProofContext>({
    assumptions: [],
    variables: new Map()
  });
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

  // State for claim insertion

  // State for let-bindings
  const [letBindings, setLetBindings] = useState<LetElement[]>([]);

  // State for goal
  const [goal, setGoal] = useState<string | null>(null);

  // Root TT term - the unified proof term model
  const [rootTerm, setRootTerm] = useState<TTerm>(() => {
    // Initialize with empty hypotheses and a Prop goal
    return createRootProofTerm([], mkProp(), 'proof', []);
  });

  // Update rootTerm whenever hypotheses or goal change
  useEffect(() => {
    // Convert UI hypotheses to TT term format
    const ttHypotheses: Array<[string, TTerm]> = context.assumptions.map(h => {
      // Parse the hypothesis expression to extract type
      // Format is either "name : Type" or just "Type"
      const match = h.expression.match(/^\s*(\w+)\s*:\s*(.+)$/);
      let typeTerm: TTerm;

      if (match) {
        const typeStr = match[2].trim();
        // For now, treat type as a constant (in real system, would parse properly)
        if (typeStr === '?') {
          typeTerm = mkProp();
        } else {
          typeTerm = { tag: 'Const', name: typeStr, type: mkProp() };
        }
      } else {
        // No type specified, use Prop
        typeTerm = mkProp();
      }

      return [h.name, typeTerm];
    });

    // Convert goal string to TT term
    const goalTerm = goal ? { tag: 'Const', name: goal, type: mkProp() } as TTerm : mkProp();

    // Create updated root term
    const newRootTerm = createRootProofTerm(ttHypotheses, goalTerm, 'proof', []);
    setRootTerm(newRootTerm);
  }, [context.assumptions, goal]);

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

  // Handlers for let-bindings and hypotheses
  const handleAddLet = useCallback((letElement: LetElement) => {
    setLetBindings(prev => [...prev, letElement]);

    // Also add to structured proof
    setStructuredProof(prev => ({
      ...prev,
      elements: [...prev.elements, letElement]
    }));
  }, []);

  const handleDeleteLet = useCallback((id: string) => {
    setLetBindings(prev => prev.filter(l => l.id !== id));

    // Also remove from structured proof
    setStructuredProof(prev => ({
      ...prev,
      elements: prev.elements.filter(e => e.id !== id)
    }));
  }, []);

  const handleAddHypothesis = useCallback((hypothesis: Assumption) => {
    setContext(prev => ({
      ...prev,
      assumptions: [...prev.assumptions, hypothesis]
    }));

    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: [...prev.metadata.assumptions, hypothesis]
      }
    }));
  }, []);

  const handleDeleteHypothesis = useCallback((id: string) => {
    setContext(prev => ({
      ...prev,
      assumptions: prev.assumptions.filter(a => a.id !== id)
    }));

    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: prev.metadata.assumptions.filter(a => a.id !== id)
      }
    }));
  }, []);

  const handleUpdateHypothesis = useCallback((id: string, updatedHypothesis: Assumption) => {
    setContext(prev => ({
      ...prev,
      assumptions: prev.assumptions.map(a => a.id === id ? updatedHypothesis : a)
    }));

    setStructuredProof(prev => ({
      ...prev,
      metadata: {
        ...prev.metadata,
        assumptions: prev.metadata.assumptions.map(a => a.id === id ? updatedHypothesis : a)
      }
    }));
  }, []);

  const handleSetGoal = useCallback((goalStr: string) => {
    setGoal(goalStr);

    // Parse goal to find unbound variables and create hypotheses
    try {
      const goalExpr = parseExpressionToAST(goalStr);
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
            context.assumptions.some(h => h.name === varName) ||
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
        const hypothesis: Assumption = {
          id: crypto.randomUUID(),
          name: varName,
          expression: `${varName} : ?`,
          description: `Auto-generated from goal: ${varName} is unbound`,
          introducedBy: 'auto'
        };
        handleAddHypothesis(hypothesis);
      });
    } catch (error) {
      console.warn('Could not parse goal for unbound variable extraction:', error);
    }

    // TODO: When we have a root TT term, update it using setGoalInRoot()
  }, [context.assumptions, letBindings, handleAddHypothesis]);

  const handleInstantiate = useCallback((letId: string, substitutions: Map<string, ExpressionNode>) => {
    // Find the let binding to instantiate
    const letBinding = letBindings.find(l => l.id === letId);
    if (!letBinding) return;

    // Substitute variables in the expression
    let instantiatedValue = letBinding.value;
    for (const [varName, replacement] of substitutions) {
      instantiatedValue = substituteVariableInExpression(instantiatedValue, varName, replacement);
    }

    // Create a new let-binding for the instantiated expression
    const newLetElement = createLetElement(
      `${letBinding.name}_inst`,
      instantiatedValue,
      letBinding.typeAnnotation
    );
    newLetElement.derivedFrom = [letId];

    // Add the new instantiated let-binding
    handleAddLet(newLetElement);
  }, [letBindings, handleAddLet]);

  // Keyboard navigation handler
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    if (!currentExpression) return;

    if (e.key === 'ArrowUp') {
      e.preventDefault();
      // Move focus up to parent node (remove last element from focus path)
      if (focusPath.length > 0) {
        const newFocusPath = focusPath.slice(0, -1);
        setFocusPath(newFocusPath);
        console.log('Moved focus up to parent, new path:', newFocusPath);
      } else {
        console.log('Already at root, cannot move up');
      }
    } else if (e.key === 'ArrowDown') {
      e.preventDefault();
      // Move focus down to first child
      const focusedNode = getNodeAtPath(currentExpression, focusPath);
      if (focusedNode && focusedNode.children && focusedNode.children.length > 0) {
        const newFocusPath = [...focusPath, 0];
        setFocusPath(newFocusPath);
        console.log('Moved focus down to first child, new path:', newFocusPath);
      } else {
        console.log('No children to move into');
      }
    } else if (e.key === 'ArrowLeft') {
      e.preventDefault();
      // Move to previous sibling (decrement last index in path)
      if (focusPath.length > 0) {
        const lastIndex = focusPath[focusPath.length - 1];
        if (lastIndex > 0) {
          const newFocusPath = [...focusPath.slice(0, -1), lastIndex - 1];
          setFocusPath(newFocusPath);
          console.log('Moved focus to previous sibling, new path:', newFocusPath);
        } else {
          console.log('Already at first sibling (index 0)');
        }
      }
    } else if (e.key === 'ArrowRight') {
      e.preventDefault();
      // Move to next sibling (increment last index in path)
      if (focusPath.length > 0) {
        const parentPath = focusPath.slice(0, -1);
        const parentNode = parentPath.length > 0 ? getNodeAtPath(currentExpression, parentPath) : currentExpression;
        const lastIndex = focusPath[focusPath.length - 1];

        if (parentNode && parentNode.children && lastIndex < parentNode.children.length - 1) {
          const newFocusPath = [...focusPath.slice(0, -1), lastIndex + 1];
          setFocusPath(newFocusPath);
          console.log('Moved focus to next sibling, new path:', newFocusPath);
        } else {
          console.log('Already at last sibling');
        }
      }
    }
  }, [focusPath, currentExpression]);

  const handleStartProof = useCallback((letId: string) => {
    // Find the claim to prove
    const claim = letBindings.find(l => l.id === letId);
    if (!claim || !claim.isClaim) return;

    // Start the proof based on the method
    if (claim.proofMethod === 'induction') {
      // For induction, we need to determine the induction variable
      // For now, we'll detect common patterns or ask the user
      // Let's look for summation patterns or variables in the expression

      // Simple heuristic: look for variables in the expression
      const variables = new Set<string>();
      const extractVars = (node: ExpressionNode) => {
        if (node.type === 'variable' && typeof node.value === 'string') {
          variables.add(node.value);
        }
        node.children?.forEach(extractVars);
      };
      extractVars(claim.value);

      // Common induction variables
      const inductionVarCandidates = ['n', 'k', 'm', 'i'];
      let inductionVar = inductionVarCandidates.find(v => variables.has(v)) || 'n';

      // Ask user to confirm/specify the induction variable
      const userVar = prompt(`Induction variable (detected: ${Array.from(variables).join(', ')}):`, inductionVar);
      if (!userVar) return; // User cancelled
      inductionVar = userVar;

      // Ask for base case value
      const baseValue = prompt('Base case value (e.g., 0, 1):', '1');
      if (baseValue === null) return; // User cancelled

      // Create base case: P(base)
      const baseValueNode: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'literal',
        value: parseInt(baseValue) || baseValue,
        children: [],
        raw: baseValue
      };

      const baseCaseExpr = substituteVariableInExpression(claim.value, inductionVar, baseValueNode);
      const baseCaseLet = createLetElement(
        `${claim.name}_base`,
        baseCaseExpr,
        claim.typeAnnotation,
        [letId],
        true,  // It's a claim to prove
        'equality'  // Will prove by equality chaining
      );
      baseCaseLet.proofStatus = 'pending';

      // Create inductive case: P(k) → P(k+1)
      // Use 'k' for the inductive variable name (the actual variable we're proving for)
      const kVar: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'variable',
        value: 'k',
        children: [],
        raw: 'k'
      };

      // Create k+1 expression
      const kPlusOne: ExpressionNode = {
        id: crypto.randomUUID(),
        type: 'binop',
        operator: '+',
        value: '+',
        children: [
          { id: crypto.randomUUID(), type: 'variable', value: 'k', children: [], raw: 'k' },
          { id: crypto.randomUUID(), type: 'literal', value: 1, children: [], raw: '1' }
        ],
        raw: 'k + 1'
      };

      // Substitute k+1 into the claim to get P(k+1)
      const inductiveCaseExpr = substituteVariableInExpression(claim.value, inductionVar, kPlusOne);
      const inductiveCaseLet = createLetElement(
        `${claim.name}_inductive`,
        inductiveCaseExpr,
        claim.typeAnnotation,
        [letId],
        true,  // It's a claim to prove
        'equality'  // Will prove by equality chaining
      );
      inductiveCaseLet.proofStatus = 'pending';

      // Add inductive hypothesis P(k) to the inductive case
      const inductiveHypothesisExpr = substituteVariableInExpression(claim.value, inductionVar, kVar);
      const inductiveHypothesis: Assumption = {
        id: crypto.randomUUID(),
        name: 'IH',
        expression: astToString(inductiveHypothesisExpr),
        description: `Inductive hypothesis: ${claim.name}(k)`,
        introducedBy: 'induction'
      };

      // Attach the inductive hypothesis to the inductive case let
      inductiveCaseLet.localHypotheses = [inductiveHypothesis];

      // Add the base case and inductive case as child let statements
      setLetBindings(prev => {
        // Find the index of the original claim
        const claimIndex = prev.findIndex(l => l.id === letId);
        if (claimIndex === -1) return prev;

        // Update the claim status
        const updatedClaim = { ...prev[claimIndex], proofStatus: 'in-progress' as const };

        // Insert the two cases right after the claim
        return [
          ...prev.slice(0, claimIndex + 1).map(l => l.id === letId ? updatedClaim : l),
          baseCaseLet,
          inductiveCaseLet,
          ...prev.slice(claimIndex + 1)
        ];
      });

      // Note: We don't set activeProofContext here - the user will click "Start Proof" on each case
    } else if (claim.proofMethod === 'equality') {
      // For equality claims, parse the expression as "left = right"
      // We'll prove it by starting with "left" and chaining to reach "right" (the goal)
      if (claim.value.type === 'equality' && claim.value.children.length === 2) {
        const leftSide = claim.value.children[0];
        const rightSide = claim.value.children[1];

        // CREATE TT PROOF TERM for this claim
        const proofTerm = createEqualityProofTerm(claim, rightSide);
        console.log('Created TT proof term for claim:', claim.name, proofTerm);

        // Store the TT proof term
        setLetProofTerms(prev => {
          const newMap = new Map(prev).set(letId, proofTerm);
          console.log('Updated letProofTerms map, size:', newMap.size);
          return newMap;
        });

        // Update the claim with goal and initial proof elements
        setLetBindings(prev => prev.map(l =>
          l.id === letId ? {
            ...l,
            proofStatus: 'in-progress',
            goal: rightSide,
            proofElements: []
          } : l
        ));

        // Add local hypotheses to the proof context if this claim has any
        if (claim.localHypotheses && claim.localHypotheses.length > 0) {
          setContext(prev => ({
            ...prev,
            assumptions: [...prev.assumptions, ...claim.localHypotheses!]
          }));
        }

        // Set current expression to just the left side (we'll build up the chain)
        setCurrentExpression(leftSide);
        setFocusPath([]);

        // Set this claim as the active proof context
        setActiveProofContext(letId);
      } else {
        alert('Equality proof requires an equality expression (left = right)');
      }
    }
  }, [letBindings]);

  const addStep = useCallback((rule: any, params?: any) => {
    if (!focusedNode || !currentExpression) {
      alert('No focused node to apply rule to');
      return;
    }

    try {
      const result = rule.applyRule(focusedNode, currentExpression, params, context);
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

      // Add transformation to proof elements
      // If we're in an active proof context (proving a let-claim), add to that claim's proof
      if (activeProofContext) {
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
            console.log('Applying proof step:', rule.displayName, 'to proof term');
            const updatedProof = applyProofStep(
              currentProof,
              currentExpression,
              newExpression,
              { name: rule.displayName, id: rule.id, params }
            );
            console.log('Updated proof term:', updatedProof);
            const newMap = new Map(prev);
            newMap.set(activeProofContext, updatedProof);
            return newMap;
          }
          console.warn('No current proof found for context:', activeProofContext);
          return prev;
        });
      } else {
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
        setContext(prev => ({
          ...prev,
          assumptions: [...prev.assumptions, ...result.newAssumptions!]
        }));

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
  }, [currentExpression, focusPath, focusedNode, context]);

  const addComment = useCallback((content: string, commentType: 'explanation' | 'assumption' | 'goal' | 'strategy' = 'explanation') => {
    const commentElement = createCommentElement(content, commentType);
    setStructuredProof(prev => ({
      ...prev,
      elements: [...prev.elements, commentElement]
    }));
  }, []);


  const deleteProofElement = useCallback((index: number) => {
    if (index === 0) return; // Don't delete the first element

    // Check if we're in an active proof context
    if (activeProofContext) {
      // Delete from the let-binding's proof elements
      setLetBindings(prev => prev.map(l => {
        if (l.id === activeProofContext && l.proofElements) {
          const newProofElements = l.proofElements.filter((_, i) => i !== index);

          // Update current expression to the previous step's right side
          if (index === l.proofElements.length - 1 && newProofElements.length > 0) {
            const previousElement = newProofElements[newProofElements.length - 1];
            if (previousElement.type === 'equation') {
              const eq = previousElement as EquationElement;
              setCurrentExpression(eq.rightSide);
            }
          } else if (newProofElements.length === 0 && l.goal) {
            // If we deleted all steps, go back to the starting expression (left side of equality)
            if (l.value.type === 'equality' && l.value.children.length === 2) {
              setCurrentExpression(l.value.children[0]);
            }
          }

          return { ...l, proofElements: newProofElements };
        }
        return l;
      }));
    } else {
      // Delete from global structured proof
      setStructuredProof(prev => ({
        ...prev,
        elements: prev.elements.filter((_, i) => i !== index)
      }));

      // If we're deleting the last element, update the current expression
      if (index === structuredProof.elements.length - 1) {
        const previousElement = structuredProof.elements[index - 1];
        if (previousElement.type === 'equation') {
          const eq = previousElement as EquationElement;
          setCurrentExpression(eq.rightSide);
        }
      }
    }
  }, [structuredProof.elements, activeProofContext, letBindings]);

  // Get applicable rules, including both forward and reverse directions for bidirectional rules
  const applicableRules: ExtendedRule[] = (focusedNode && currentExpression) ? ENHANCED_FOCUS_RULES.flatMap(rule => {
    const rules: ExtendedRule[] = [];

    // Check forward direction
    if (rule.isApplicableToFocus(focusedNode, currentExpression, context)) {
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
      if (rule.isApplicableReverse(focusedNode, currentExpression, context)) {
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
  const currentEquationElement = currentExpression ? (
    <MathJaxExpressionRenderer
      expression={currentExpression}
      focusPath={focusPath}
      onFocusChange={setFocusPath}
      isActive={true}
      readonly={false}
    />
  ) : null

  const currentEquationIsChained = currentExpression && structuredProof.elements.length > 0 ?
    elementIsChained(structuredProof.elements[structuredProof.elements.length - 1], currentExpression) : false;

  return (
    <div style={{
      padding: '20px',
      fontFamily: 'system-ui, sans-serif',
      maxWidth: '1200px',
      margin: '0 auto'
    }}>
      {/* Header */}
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
            hypotheses={context.assumptions.filter(a => {
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
            onInstantiate={handleInstantiate}
            onStartProof={handleStartProof}
          />

          {/* Mathematical Derivation */}
          <div
            tabIndex={0}
            onKeyDown={handleKeyDown}
            style={{
              backgroundColor: '#fafbfc',
              border: '2px solid #e1e8ed',
              borderRadius: '8px',
              padding: '20px',
              minHeight: '400px',
              maxHeight: '600px',
              display: 'flex',
              flexDirection: 'column',
              outline: 'none'
            }}
          >
            <h4 style={{
              margin: '0 0 20px 0',
              color: '#495057',
              fontSize: '16px',
              borderBottom: '1px solid #dee2e6',
              paddingBottom: '8px'
            }}>
              🔢 Proof:
            </h4>


            {/* Goal display when proving a claim */}
            {activeProofContext && (() => {
              const activeClaim = letBindings.find(l => l.id === activeProofContext);
              if (activeClaim?.goal) {
                return (
                  <div style={{
                    marginBottom: '16px',
                    padding: '12px 16px',
                    backgroundColor: '#fff3cd',
                    border: '2px solid #ffc107',
                    borderRadius: '6px'
                  }}>
                    <div style={{ fontSize: '13px', fontWeight: 'bold', color: '#856404', marginBottom: '4px' }}>
                      Goal:
                    </div>
                    <div style={{ fontSize: '18px', color: '#856404' }}>
                      <MathJaxExpressionRenderer expression={activeClaim.goal} />
                    </div>
                  </div>
                );
              }
              return null;
            })()}

            {/* All previous proof steps */}
            <div ref={proofScrollRef} style={{ overflowY: 'auto', flex: 1 }}>
              {(() => {
                // Get proof elements based on active context
                const proofElements = activeProofContext
                  ? (letBindings.find(l => l.id === activeProofContext)?.proofElements || [])
                  : structuredProof.elements;

                return proofElements.length === 0 && !currentExpression ? (
                  <div style={{
                    textAlign: 'center',
                    color: '#6c757d',
                    padding: '60px 20px',
                    fontSize: '16px'
                  }}>
                    <div style={{ fontSize: '48px', marginBottom: '20px' }}>📝</div>
                    <div>No proof started yet.</div>
                    <div style={{ marginTop: '8px' }}>Create a claim in the Context Manager above to start proving!</div>
                  </div>
                ) : (
                  <table style={{ width: '100%' }}>
                    <tbody>
                      {proofElements.map((element, index) => {
                        if (element.type === 'equation') {
                          const eq = element as EquationElement;
                          const isChained = elementIsChained(proofElements[index - 1], eq.leftSide);

                          const right = (index === proofElements.length - 1 && currentExpression && eq.rightSide.id === currentExpression.id) ? currentEquationElement : (
                            <MathJaxExpressionRenderer
                              expression={eq.rightSide}
                            />
                          )

                          return (
                            <tr key={element.id}>
                              <td>
                                <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'flex-end' }}>
                                  {isChained ? null : (
                                    <MathJaxExpressionRenderer
                                      expression={eq.leftSide}
                                    />
                                  )}
                                </div>
                              </td>
                              <td><MathJaxExpressionRendererRaw expression={'='} /></td>
                              <td>
                                <div style={{ display: 'flex', flexDirection: 'row', justifyContent: 'flex-start' }}>
                                  {right}
                                </div>
                              </td>
                              <td>
                                <div style={{
                                  fontSize: '13px',
                                  color: '#7f8c8d',
                                  fontStyle: 'italic',
                                  marginTop: '6px'
                                }}>
                                  {eq.justification && `(${eq.justification})`}
                                </div>
                              </td>
                              <td style={{ width: '30px', textAlign: 'right' }}>
                                {index === proofElements.length - 1 && (
                                  <button
                                    onClick={() => deleteProofElement(index)}
                                    style={{
                                      padding: '2px 6px',
                                      backgroundColor: '#dc3545',
                                      color: 'white',
                                      border: 'none',
                                      borderRadius: '3px',
                                      cursor: 'pointer',
                                      fontSize: '12px',
                                      fontWeight: 'bold'
                                    }}
                                    title="Undo this step"
                                  >
                                    ✕
                                  </button>
                                )}
                              </td>
                            </tr>
                          )
                        } else if (element.type === 'comment') {
                          return <ProofComment key={element.id} element={element as CommentElement} />;
                        } else if (element.type === 'let') {
                          const letElem = element as LetElement;
                          return (
                            <tr key={element.id}>
                              <td colSpan={5} style={{ padding: '12px' }}>
                                <div style={{
                                  display: 'flex',
                                  alignItems: 'center',
                                  gap: '8px',
                                  backgroundColor: '#f0f8ff',
                                  padding: '8px 12px',
                                  borderRadius: '6px',
                                  border: '1px solid #b3d9ff'
                                }}>
                                  <span style={{ fontWeight: 'bold', color: '#0066cc' }}>
                                    let {letElem.name}
                                  </span>
                                  {letElem.typeAnnotation && (
                                    <span style={{ color: '#666' }}>
                                      : {letElem.typeAnnotation}
                                    </span>
                                  )}
                                  <span>=</span>
                                  <MathJaxExpressionRenderer
                                    expression={letElem.value}
                                    readonly={true}
                                  />
                                </div>
                              </td>
                            </tr>
                          );
                        } else if (element.type === 'induction') {
                          const induction = element as InductionProofElement;
                          return (
                            <tr key={element.id}>
                              <td colSpan={5}>
                                <div style={{
                                  margin: '16px 0',
                                  padding: '16px',
                                  backgroundColor: '#e8f5e9',
                                  borderRadius: '8px',
                                  border: '2px solid #4caf50'
                                }}>
                                  <div style={{ marginBottom: '16px' }}>
                                    <strong style={{ color: '#2e7d32', fontSize: '16px' }}>
                                      🔄 Proof by Induction on {induction.inductionVariable}
                                    </strong>
                                    <div style={{ marginTop: '8px' }}>
                                      <strong>Statement P({induction.inductionVariable}):</strong>
                                      <MathJaxExpressionRenderer expression={induction.statement} />
                                    </div>
                                  </div>

                                  {/* Base Case */}
                                  <div style={{
                                    marginTop: '12px',
                                    padding: '12px',
                                    backgroundColor: 'white',
                                    borderRadius: '4px',
                                    border: '1px solid #81c784'
                                  }}>
                                    <strong style={{ color: '#388e3c' }}>Base Case (n = 1):</strong>
                                    {!induction.baseCase ? (
                                      <div style={{ marginTop: '8px' }}>
                                        <button
                                          onClick={() => {
                                            // Initialize base case by substituting n=1
                                            const baseCaseStatement = substituteVariableInExpression(
                                              induction.statement,
                                              induction.inductionVariable,
                                              { id: crypto.randomUUID(), type: 'literal', value: 1, children: [], raw: '1' }
                                            );

                                            // Update the induction element with base case
                                            const updatedElements = [...structuredProof.elements];
                                            const inductionIndex = updatedElements.findIndex(el => el.id === induction.id);
                                            if (inductionIndex !== -1) {
                                              (updatedElements[inductionIndex] as InductionProofElement).baseCase = {
                                                value: 1,
                                                proof: [],
                                                status: 'proving'
                                              };
                                              setStructuredProof(prev => ({ ...prev, elements: updatedElements }));

                                              // Set up expression for base case
                                              setCurrentExpression(baseCaseStatement);
                                              setFocusPath([]);
                                              setActiveProofContext(`${induction.id}-base`);

                                              console.log('Setting up base case:', astToString(baseCaseStatement));
                                            }
                                          }}
                                          style={{
                                            padding: '6px 12px',
                                            backgroundColor: '#4caf50',
                                            color: 'white',
                                            border: 'none',
                                            borderRadius: '4px',
                                            cursor: 'pointer'
                                          }}
                                        >
                                          Start Base Case
                                        </button>
                                      </div>
                                    ) : (
                                      <div style={{ marginTop: '8px', fontSize: '14px' }}>
                                        <div style={{
                                          padding: '8px',
                                          backgroundColor: activeProofContext === `${induction.id}-base` ? '#e8f5e9' : 'white',
                                          borderRadius: '4px',
                                          border: activeProofContext === `${induction.id}-base` ? '2px solid #4caf50' : '1px solid #ddd'
                                        }}>
                                          <strong>Status:</strong> {induction.baseCase.status}
                                          {activeProofContext !== `${induction.id}-base` && induction.baseCase.status === 'proving' && (
                                            <button
                                              onClick={() => {
                                                // Resume working on base case
                                                setActiveProofContext(`${induction.id}-base`);

                                                const baseCaseStatement = substituteVariableInExpression(
                                                  induction.statement,
                                                  induction.inductionVariable,
                                                  { id: crypto.randomUUID(), type: 'literal', value: 1, children: [], raw: '1' }
                                                );

                                                // Resume expression for base case
                                                console.log('Resume base case:', astToString(baseCaseStatement));

                                                setCurrentExpression(baseCaseStatement);
                                                setFocusPath([]);
                                              }}
                                              style={{
                                                marginTop: '8px',
                                                padding: '4px 8px',
                                                backgroundColor: '#2196F3',
                                                color: 'white',
                                                border: 'none',
                                                borderRadius: '4px',
                                                cursor: 'pointer',
                                                fontSize: '12px'
                                              }}
                                            >
                                              Resume Base Case
                                            </button>
                                          )}
                                        </div>
                                      </div>
                                    )}
                                  </div>

                                  {/* Inductive Step */}
                                  <div style={{
                                    marginTop: '12px',
                                    padding: '12px',
                                    backgroundColor: 'white',
                                    borderRadius: '4px',
                                    border: '1px solid #81c784'
                                  }}>
                                    <strong style={{ color: '#388e3c' }}>
                                      Inductive Step (P(n) → P(n+1)):
                                    </strong>
                                    {!induction.inductiveStep ? (
                                      <div style={{ marginTop: '8px' }}>
                                        <button
                                          onClick={() => {
                                            // Initialize inductive step
                                            const nPlusOne: ExpressionNode = {
                                              id: crypto.randomUUID(),
                                              type: 'binop',
                                              operator: '+',
                                              children: [
                                                { id: crypto.randomUUID(), type: 'variable', value: induction.inductionVariable, children: [], raw: induction.inductionVariable },
                                                { id: crypto.randomUUID(), type: 'literal', value: 1, children: [], raw: '1' }
                                              ],
                                              raw: `${induction.inductionVariable} + 1`
                                            };

                                            const inductiveGoal = substituteVariableInExpression(
                                              induction.statement,
                                              induction.inductionVariable,
                                              nPlusOne
                                            );

                                            // Update the induction element with inductive step
                                            const updatedElements = [...structuredProof.elements];
                                            const inductionIndex = updatedElements.findIndex(el => el.id === induction.id);
                                            if (inductionIndex !== -1) {
                                              (updatedElements[inductionIndex] as InductionProofElement).inductiveStep = {
                                                assumption: induction.statement,
                                                goal: inductiveGoal,
                                                proof: [],
                                                status: 'proving'
                                              };
                                              setStructuredProof(prev => ({ ...prev, elements: updatedElements }));

                                              // Add the inductive hypothesis as an assumption
                                              // Keep the original raw expression for correct display
                                              const ihExpression = induction.statement.raw || astToString(induction.statement);
                                              setContext(prev => ({
                                                ...prev,
                                                assumptions: [...prev.assumptions, {
                                                  id: crypto.randomUUID(),
                                                  name: 'IH',
                                                  expression: ihExpression,
                                                  description: 'Inductive Hypothesis: P(n)',
                                                  introducedBy: 'induction'
                                                }]
                                              }));

                                              // Set up expression for inductive step
                                              setCurrentExpression(inductiveGoal);
                                              setFocusPath([]);
                                              setActiveProofContext(`${induction.id}-inductive`);
                                              console.log('Setting up inductive step:', astToString(inductiveGoal));
                                            }
                                          }}
                                          style={{
                                            padding: '6px 12px',
                                            backgroundColor: '#4caf50',
                                            color: 'white',
                                            border: 'none',
                                            borderRadius: '4px',
                                            cursor: 'pointer'
                                          }}
                                        >
                                          Start Inductive Step
                                        </button>
                                      </div>
                                    ) : (
                                      <div style={{ marginTop: '8px', fontSize: '14px' }}>
                                        <div style={{
                                          padding: '8px',
                                          backgroundColor: activeProofContext === `${induction.id}-inductive` ? '#e8f5e9' : 'white',
                                          borderRadius: '4px',
                                          border: activeProofContext === `${induction.id}-inductive` ? '2px solid #4caf50' : '1px solid #ddd'
                                        }}>
                                          <div><strong>Assumption (IH):</strong> <MathJaxExpressionRenderer expression={induction.inductiveStep.assumption} inline={true} /></div>
                                          <div style={{ marginTop: '8px' }}><strong>Status:</strong> {induction.inductiveStep.status}</div>
                                          {activeProofContext !== `${induction.id}-inductive` && induction.inductiveStep.status === 'proving' && (
                                            <button
                                              onClick={() => {
                                                // Resume working on inductive step
                                                setActiveProofContext(`${induction.id}-inductive`);

                                                const nPlusOne: ExpressionNode = {
                                                  id: crypto.randomUUID(),
                                                  type: 'binop',
                                                  operator: '+',
                                                  children: [
                                                    { id: crypto.randomUUID(), type: 'variable', value: induction.inductionVariable, children: [], raw: induction.inductionVariable },
                                                    { id: crypto.randomUUID(), type: 'literal', value: 1, children: [], raw: '1' }
                                                  ],
                                                  raw: `${induction.inductionVariable} + 1`
                                                };

                                                const inductiveGoal = substituteVariableInExpression(
                                                  induction.statement,
                                                  induction.inductionVariable,
                                                  nPlusOne
                                                );

                                                // Resume expression for inductive step
                                                setCurrentExpression(inductiveGoal);
                                                setFocusPath([]);
                                                setActiveProofContext(`${induction.id}-inductive`);
                                                console.log('Resume inductive step:', astToString(inductiveGoal));
                                              }}
                                              style={{
                                                marginTop: '8px',
                                                padding: '4px 8px',
                                                backgroundColor: '#2196F3',
                                                color: 'white',
                                                border: 'none',
                                                borderRadius: '4px',
                                                cursor: 'pointer',
                                                fontSize: '12px'
                                              }}
                                            >
                                              Resume Inductive Step
                                            </button>
                                          )}
                                        </div>
                                      </div>
                                    )}
                                  </div>
                                </div>
                              </td>
                            </tr>
                          );
                        }
                        return null;
                      })}
                      {currentExpression && proofElements.length === 0 && (
                        <tr>
                          <td colSpan={5}>{currentEquationIsChained ? null : currentEquationElement}</td>
                        </tr>
                      )}
                    </tbody>
                  </table>
                );
              })()}
            </div>
            {currentExpression && (
              <FocusBreadcrumbs
                expression={currentExpression}
                focusPath={focusPath}
                onFocusChange={setFocusPath}
              />
            )}
          </div>
        </div>

        {currentExpression && (
          <RulesPanel
            rulesByCategory={rulesByCategory}
            focusedNode={focusedNode}
            currentExpression={currentExpression}
            context={context}
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
          context={[]}
        />
      </div>
    </div>
  );
}

function elementIsChained(previousElement: ProofElement, currentElement: ExpressionNode) {
  if (previousElement?.type !== 'equation') {
    return false;
  }

  const previousEquation = previousElement as EquationElement;
  return previousEquation.rightSide === currentElement;
}


function ProofComment({ element }: { element: CommentElement }) {
  return (
    <tr key={element.id}>
      <td colSpan={5}>
        <div style={{
          margin: '16px 0',
          padding: '12px 16px',
          backgroundColor: '#e8f4f8',
          borderLeft: '4px solid #17a2b8',
          borderRadius: '0 6px 6px 0',
          color: '#0c5460',
          fontSize: '14px',
          fontStyle: 'italic'
        }}>
          {element.content}
        </div>
      </td>
    </tr>
  );
}

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