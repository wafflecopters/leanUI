# LeanUI Development TODO

## Current Priority: Architectural Shift to Proper Lean Integration

### Immediate Tasks
- [x] Fix TypeScript compilation errors (completed)
- [x] Implement induction proof workflow with child statement generation (completed)
  - [x] Create base case and inductive case as child let statements
  - [x] Add inductive hypothesis to inductive case
  - [x] Display local hypotheses in UI
- [ ] Replace custom parseExpressionToAST with proper Lean term parsing
- [ ] Implement `d/dx (c f(x))` as proper Lean term with assumption `f: R->R`
- [ ] Add AST debug panel near the focus window
- [ ] Research Lean 4 integration options for web applications

### Core Architecture Changes Needed

#### 1. Lean Integration Research
- [ ] Investigate Lean 4 web integration options
  - [ ] Lean 4 WASM compilation
  - [ ] Lean Language Server Protocol (LSP) integration
  - [ ] Online Lean compiler APIs
- [ ] Determine best approach for parsing Lean syntax in browser

#### 2. Expression System Overhaul
- [ ] Current: `parseExpressionToAST('deriv (lambda x, integral a x f)')`
- [ ] Target: Proper Lean term parsing of `d/dx (c * f(x))`
- [ ] Replace custom AST with Lean's native AST representation
- [ ] Update syntax mapping to work with Lean AST

#### 3. Mathematical Context Updates
- [ ] Update example to: assumption `f: ℝ → ℝ` and term `d/dx (c * f(x))`
- [ ] Ensure proper Lean syntax for types (`ℝ → ℝ` vs `R->R`)
- [ ] Implement Lean type checking integration

#### 4. UI Enhancements
- [ ] Add AST debug panel component
- [ ] Position debug panel near focus window
- [ ] Display raw Lean AST structure
- [ ] Show type information from Lean type checker

#### 5. Proof System Foundation
- [ ] Set up goal: prove `d/dx (c * f(x)) = c * df/dx`
- [ ] Design architecture for dual proof representation:
  - [ ] Type-checked Lean proof
  - [ ] Human-readable proof (possibly via annotated Lean comments)
- [ ] Enable "mess around" functionality for mathematical exploration

### Files to Modify

#### Core Components
- `src/components/EnhancedProofWorkspace.tsx` - Update to use Lean terms
- `src/components/MathJaxExpressionRenderer.tsx` - Integrate with Lean AST
- `src/config/syntax-mapping.ts` - Adapt to Lean AST structure
- `src/types/enhanced-focus.ts` - Add Lean-specific types

#### New Components Needed
- `src/components/ASTDebugPanel.tsx` - Show Lean AST structure
- `src/services/lean-integration.ts` - Handle Lean parsing/type checking
- `src/types/lean-types.ts` - TypeScript types for Lean structures

### Research Findings (Updated)

#### Lean 4 Web Integration Status (2025)
- **WASM Status**: Lean 4 doesn't yet have client-side WASM support like Lean 3 did
- **Current Best Practice**: Server-side Lean execution with web frontend via LSP/HTTP APIs
- **Reference Implementation**: lean4web uses TypeScript client/server architecture
- **Active Web Interface**: live.lean-lang.org uses React frontend with remote server
- **LSP Integration**: Lean 4 has built-in LSP server support for modern editor integration

#### Recommended Implementation Strategy
1. **Phase 1**: Create mock Lean service for immediate development
   - Proper Lean syntax parsing for `d/dx (c * f(x))` with `f: ℝ → ℝ`
   - Basic type checking simulation
   - AST debug panel integration
2. **Phase 2**: Integrate with server-side Lean execution
   - Follow lean4web architecture patterns
   - Implement LSP or HTTP API communication
   - Add real type checking and proof validation

### Research Notes
- Current system uses custom parsing: not leveraging Lean's parsing
- lean4web shows TypeScript/React stack works well for Lean integration
- Server-side execution provides security and performance benefits
- Must maintain MathJax rendering for beautiful mathematical display

### Long-term Vision
- Interactive theorem proving workspace
- Real-time Lean type checking
- Side-by-side formal and informal proofs
- Mathematical expression manipulation with proof state tracking

---

## Recent Implementations

### Induction Proof Workflow (Completed 2025-10)

**Feature**: Complete induction proof workflow with child statement generation

**Implementation Details**:
1. **Starting an Induction Proof**:
   - User creates a let statement marked as a claim with proof method "induction on ℕ"
   - User clicks "Start Proof" button
   - System prompts for induction variable (auto-detected from common patterns: n, k, m, i)
   - System prompts for base case value (default: 1)

2. **Child Statement Generation**:
   - System creates two child let statements as siblings (not nested):
     - **Base Case** (`claim_base`): P(base_value)
     - **Inductive Case** (`claim_inductive`): P(k+1)
   - Both are marked as claims with proof method "equality"
   - Original claim status updated to "in-progress"

3. **Inductive Hypothesis**:
   - Created as P(k) where k is the inductive variable
   - Stored in `inductiveCaseLet.localHypotheses`
   - Displayed in UI within the inductive case let binding
   - Automatically added to proof context when starting proof of inductive case

4. **Proof Flow**:
   - User proves base case independently (click "Start Proof" on base case)
   - User proves inductive case independently (click "Start Proof" on inductive case)
   - Inductive hypothesis available as assumption during inductive case proof
   - When both cases complete, original claim marked as "completed"

**Files Modified**:
- `src/types/enhanced-focus.ts`: Added `localHypotheses` to `LetElement`
- `src/components/EnhancedProofWorkspace.tsx`: Implemented child statement creation logic
- `src/components/LetManager.tsx`: Added UI for displaying local hypotheses
- `src/test-induction.ts`: Updated test documentation

**Test File**: `src/test-induction.ts` demonstrates the complete workflow