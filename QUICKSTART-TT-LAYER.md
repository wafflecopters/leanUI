# Quick Start: Testing the TT Layer

## 🚀 See It In Action (5 Minutes)

### Step 1: Open the App
```
http://localhost:3001
```
(Server is already running)

### Step 2: Create a Let-Binding Claim

1. **Click the "+ Add Let" button** (in the "Context Manager" section)

2. **Fill in the form:**
   - **Variable name:** `thm`
   - **Expression:** `a + a = 2 * a`
   - **Type annotation:** (leave empty or put `Prop`)
   - ☑️ **Check the box:** "This is a claim to be proved"
   - **Proof method:** Select "Equality Chaining (Direct Proof)"

3. **Click "Add"**

### Step 3: Start the Proof

1. You'll see your claim appear with a **"Start Proof"** button
2. **Click "Start Proof"**
3. **Result:** No error! (Previously this crashed with "Unsupported expression type")

### Step 4: View the TT Proof Term

**Scroll down** to the bottom of the page to the **"TT Proof Term"** section.

**You should see:**

```
TT Proof Term
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

[Hide/Show Type Info] [Hide/Show Raw AST]

Type:
  ((((eq ℝ) ((+ a) a)) ((* 2) a)))

Holes (1):
  ?proof_<id> : ((((eq ℝ) ((+ a) a)) ((* 2) a)))
  [Show Context]

Pretty-Printed Term:
  ?proof_<id>

⚠️ Proof incomplete: 1 hole remaining
```

### What This Means ✅

✅ **Type line**: Shows the proposition `a+a = 2*a` in TT form
- `eq` = equality
- `ℝ` = Real numbers
- `(+ a) a` = a + a
- `(* 2) a` = 2 * a

✅ **Hole**: The `?proof_<id>` is the incomplete proof (what you called `_incomplete_ "id0"`)

✅ **Type of hole**: Shows it expects a proof of type `a+a = 2*a`

✅ **Status**: "Proof incomplete: 1 hole remaining"

## 🎯 What You've Proven

You've verified that:

1. ✅ Creating a let-binding claim works
2. ✅ Starting a proof creates a TT proof term
3. ✅ The TT term has the correct type
4. ✅ Holes are tracked properly
5. ✅ No errors or crashes
6. ✅ The formal proof structure is visible

## 🔍 Optional: Explore More

### Toggle Raw AST
- Click **"Show Raw AST"** to see the actual TT term data structure
- You'll see the JSON representation with tags like `'Hole'`, `'App'`, `'Const'`

### Toggle Type Info
- Click **"Hide Type Info"** to collapse the type display
- Click **"Show Type Info"** to expand it again

### Show Hole Context
- Click **"Show Context"** next to a hole
- This shows what variables/assumptions are available for proving this hole

## 🧪 Try Different Examples

### Example 1: Simpler Equality
```
claim eq1: a = a
```
- Start proof → See TT term with reflexivity type

### Example 2: Arithmetic
```
claim calc: 2 + 3 = 5
```
- Start proof → See TT term for numeric equality

### Example 3: More Complex
```
claim factor: a * a = a ^ 2
```
- Start proof → See TT term with exponentiation

## 📚 Next Steps

1. **Apply proof rules** (the UI buttons) → Watch the TT term update (currently stubs)
2. **Check the documentation:**
   - [TT-LAYER-DESIGN.md](TT-LAYER-DESIGN.md) - Complete design
   - [IMPLEMENTATION-SUMMARY.md](IMPLEMENTATION-SUMMARY.md) - What was built
   - [BUGFIX-application-type.md](BUGFIX-application-type.md) - Bug details

3. **Implement proof step application:**
   - Edit [src/types/tt-bridge.ts](src/types/tt-bridge.ts)
   - Fill in `applyProofStep()` function
   - Build actual proof terms as rules are applied

## 🎉 Success!

You now have a **solid foundation**:
- ✅ Good AST (ExpressionNode)
- ✅ Good TT layer (TTerm with types)
- ✅ Clean separation between UI and formal proof
- ✅ Holes tracking what needs to be proven
- ✅ Type checking integration

The "ground truth" is now the TT term, not the UI!
