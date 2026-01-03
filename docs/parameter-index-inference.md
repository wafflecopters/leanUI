# Parameter/Index Inference for Inductive Families

An algorithm for classifying arguments to inductive type families and generating the strongest possible eliminator.

## Input

```
inductive D : (x₁ : A₁) → ... → (xₙ : Aₙ) → Sort where
  c₁ : Γ₁ → D t₁,₁ ... t₁,ₙ
  ...
  cₖ : Γₖ → D tₖ,₁ ... tₖ,ₙ
```

- `n` argument positions to classify
- `k` constructors
- `Γⱼ` is constructor `cⱼ`'s telescope (its bound variables)
- `tⱼ,ᵢ` is the term in position `i` of constructor `cⱼ`'s return type

## Output

- A partition of positions `1..n` into **parameters** (a prefix) and **indices** (the rest)
- An eliminator with maximal strength (i.e., J for equality, not the weak 2-index version)

---

## Phase 1: Syntactic Parameter Detection

For each position `i ∈ 1..n`:

```
is_syntactic_param(i) :=
  for all constructors cⱼ:
    tⱼ,ᵢ is a single variable v, AND
    v is bound in Γⱼ, AND
    v appears exactly once in (tⱼ,₁, ..., tⱼ,ₙ)
```

If `is_syntactic_param(i)`, mark position `i` as a **parameter**.

Otherwise, mark position `i` as an **index** (provisional — may be promoted in Phase 2).

---

## Phase 2: Index Promotion

This phase detects indices that are "trivially constrained" to equal another index across all constructors, allowing one to be promoted to a parameter.

### Step 2.1: Build equivalence classes

For each constructor `cⱼ`, define an equivalence relation `~ⱼ` on index positions:

```
i ~ⱼ k  iff  tⱼ,ᵢ ≡ tⱼ,ₖ  (definitionally equal)
```

Compute the **global equivalence**: `i ~ k` iff `i ~ⱼ k` for ALL constructors `cⱼ`.

### Step 2.2: Promote one index per equivalence class

For each equivalence class under `~` with more than one index position:

1. Select one position as the **promoted parameter** (conventionally: the leftmost)
2. All other positions in the class remain **indices**

### Step 2.3: Verify promotion validity

For a position `i` to be promoted, confirm that in every constructor:
- `tⱼ,ᵢ` is a variable bound in `Γⱼ` (not a complex term)

If `tⱼ,ᵢ` is a complex term (e.g., `suc n`), the position cannot be promoted.

---

## Phase 2.5: Dependency Validation

Parameters are bound *before* indices in the eliminator. Therefore, a parameter's type cannot depend on an index — the index wouldn't be in scope.

Since the datatype telescope `(x₁ : A₁) → ... → (xₙ : Aₙ)` has each `Aᵢ` potentially depending on `x₁ ... xᵢ₋₁`, we must ensure:

**No parameter's type depends on an index.**

### Enforcement: Parameters must form a prefix

The simplest approach: parameters must occupy a contiguous prefix of positions.

```
let first_index = min { i : position i is an index }
for each position j > first_index:
  demote position j to index (even if Phase 1/2 said parameter)
```

### Why this is sound

If position `i` is an index and position `j > i`, then `Aⱼ` (the type at position `j`) may reference `xᵢ`. If we tried to make `j` a parameter in the eliminator, we'd have:

```
D-elim : {xⱼ : Aⱼ} → (P : (xᵢ : ...) → ...) → ...
                           ↑
                    xᵢ not in scope, but Aⱼ mentions it!
```

By forcing parameters to be a prefix, we guarantee all parameter types are well-scoped.

### Example

```
inductive Weird : (n : Nat) → (v : Vec Bool n) → Type where
  mk0 : (v : Vec Bool 0) → Weird 0 v
  mkS : (n : Nat) → (v : Vec Bool (suc n)) → Weird (suc n) v
```

Phase 1:
- Position 1 (`n`): `0` and `suc n` are not variables → **index**
- Position 2 (`v`): `v` passed through → **param** (provisionally)

Phase 2: No equivalence classes to merge.

Phase 2.5:
- First index is position 1
- Position 2 > position 1, so **demote position 2 to index**

Final: 0 parameters, 2 indices.

---

## Phase 3: Eliminator Generation

Given final classification with `p` parameters and `m` indices:

```
D-elim :
  {params}                                          -- implicit, fixed
  → (P : (indices) → D params indices → Sort)       -- motive
  → (case for each constructor)                     -- methods
  → (indices) → (target : D params indices)         -- target
  → P indices target
```

### Constructor case generation

For constructor `cⱼ : Γⱼ → D tⱼ,₁ ... tⱼ,ₙ`:

The case has type:
```
(args : Γⱼ') → (ih : ...) → P [indices from tⱼ] (cⱼ args)
```

Where:
- `Γⱼ'` is `Γⱼ` with promoted parameters removed (they're now inherited)
- `ih` contains inductive hypotheses for recursive arguments
- `[indices from tⱼ]` extracts the index-position terms from `tⱼ,₁ ... tⱼ,ₙ`

---

## Example: Equality

### Input
```
inductive Equal : (A : Type) → A → A → Type where
  refl : (A : Type) → (x : A) → Equal A x x
```

### Phase 1
| Position | Term in `refl` | Single var? | Appears once? | Syntactic param? |
|----------|---------------|-------------|---------------|------------------|
| 1 (`A`)  | `A`           | ✓           | ✓             | ✓ **param**      |
| 2        | `x`           | ✓           | ✗ (also pos 3)| ✗ index          |
| 3        | `x`           | ✓           | ✗ (also pos 2)| ✗ index          |

### Phase 2
- Index positions: {2, 3}
- In `refl`: position 2 has `x`, position 3 has `x`
- Therefore: `2 ~ 3`
- Equivalence class: {2, 3}
- Promote leftmost: position 2 → **parameter**
- Position 3 remains **index**

### Final classification
- Position 1: parameter (`A`)
- Position 2: parameter (`x`) — promoted
- Position 3: index

### Generated eliminator (J)
```
Equal-elim :
  {A : Type} → {x : A}
  → (P : (y : A) → Equal A x y → Sort)
  → P x refl
  → (y : A) → (e : Equal A x y) → P y e
```

---

## Example: Vector

### Input
```
inductive Vec : Type → Nat → Type where
  nil  : (A : Type) → Vec A 0
  cons : (A : Type) → (n : Nat) → A → Vec A n → Vec A (suc n)
```

### Phase 1
| Position | `nil`  | `cons`  | Syntactic param? |
|----------|--------|---------|------------------|
| 1        | `A` ✓  | `A` ✓   | ✓ **param**      |
| 2        | `0`    | `suc n` | ✗ (not variables)|

### Phase 2
- Index positions: {2}
- Only one index, nothing to promote

### Final classification
- Position 1: parameter
- Position 2: index

---

## Example: Fin

### Input
```
inductive Fin : Nat → Type where
  fzero : (n : Nat) → Fin (suc n)
  fsuc  : (n : Nat) → Fin n → Fin (suc n)
```

### Phase 1
| Position | `fzero` | `fsuc`  | Syntactic param? |
|----------|---------|---------|------------------|
| 1        | `suc n` | `suc n` | ✗ (complex term) |

### Phase 2
- Index positions: {1}
- `suc n ≡ suc n` across constructors, but it's not a variable — cannot promote

### Final classification
- Position 1: index

---

## Summary

1. **Phase 1**: Mark positions as parameters if they have a unique variable passed through unchanged in every constructor

2. **Phase 2**: Among indices, find positions that are always equal across all constructors; promote one per equivalence class (if the term is a variable)

3. **Phase 2.5**: Demote any "parameter" that comes after an index (parameters must form a prefix to ensure well-scoped types)

4. **Phase 3**: Generate eliminator where parameters are fixed and indices appear in the motive

The key insights:
- Two index positions receiving the *same* variable indicates a constraint that can be reified as a parameter/index relationship, yielding a stronger eliminator
- Parameters must form a prefix because later types may depend on earlier values, and indices aren't bound until inside the motive
