# Velvet Language Documentation

## 1. Introduction

### What is Velvet?

Velvet is a language for writing imperative programs with specifications, shallowly embedded in Lean 4 on top of `Std.WP`. It allows you to prove the correctness of your programs with respect to their specifications using Lean's proof capabilities. The syntax is inspired by Dafny.

### The Velvet Advantage: Hybrid Verification

The primary strength of Velvet is its nature as a **shallowly embedded language** within Lean. This enables a powerful hybrid verification workflow that combines automated solving with interactive theorem proving:

1. **Automated Proof:** The `velvet_vcgen` tactic with `finish` attempts to automatically prove the correctness of the method using Lean's `grind` tactic and arithmetic simplification. For many methods, this is all that is needed.
2. **Interactive Proving:** If automated solving leaves remaining goals, you are not stuck. You can use `case <name> => ...` to target specific verification conditions with interactive Lean tactics (`omega`, `induction`, `rcases`, etc.).

---

## 2. Quick Start

### Your First Velvet Method

Here is a simple, working example:

```lean
import Velvet

method isqrt (n : Nat) returns (r : Nat)
  requires True
  ensures r * r ≤ n ∧ n < (r + 1) * (r + 1)
do
  let mut x : Nat := 0
  while' loop_cond: (x + 1) * (x + 1) ≤ n
    invariant inv_lower: x * x ≤ n
    decreasing by_remaining: n - x * x
    done_with done: n < (x + 1) * (x + 1)
  do
    x := x + 1
  return x

prove_correct isqrt by
  velvet_vcgen [isqrt] with finish
```

This example shows:
- **Method declaration** with typed parameters and return value (`returns (r : Nat)`).
- **Pre- and postconditions** (`requires`, `ensures`).
- **Loop annotations** (`invariant`, `decreasing` measure, `done_with`).
- **Verification** using `prove_correct` and `velvet_vcgen ... with finish`.

---

## 3. Configuration Options

Velvet provides several options to control verification semantics and feedback:

| Option | Values | Default | Description |
| :--- | :--- | :--- | :--- |
| `velvet.semantics.termination` | `"total"`, `"partial"` | `"total"` | Whether methods require termination measures or use partial fixpoints. |
| `velvet.verifyDuringElab` | `true`, `false` | `false` | Automatically verify specifications at definition time without `prove_correct`. |
| `velvet_vcgen.showProgress` | `true`, `false` | `true` | Show VC generation and discharge progress diagnostics in the Infoview. |

Example:
```lean
set_option velvet.semantics.termination "partial"
set_option velvet_vcgen.showProgress true
```

---

## 4. Writing Methods

### Method Signatures

```lean
method [rec]? <name> (<params>...)* returns (<ret_name> : <RetType>) [in <Monad>]?
  [given (<ghost_binders>...)+]?
  [requires [<name> :]? [(<state_binders>) =>]? <Predicate>]*
  [signals [<name> :]? [(<err_binder>) =>]? <ErrorPredicate>]*
  [ensures [<name> :]? [(<state_binders>) =>]? <PostPredicate>]*
do
  <body>
```

> **Syntax Notation**: `?` denotes an optional element (0 or 1), and `*` denotes repetition (0 or more).

- **Pure Methods (`Option`)**: When `in <Monad>` is omitted and no `signals` clause is provided, methods default to `Option`.
- **Stateful Methods (`StateT`)**: Initial and final state binders are specified using `(s : σ) => ...`.
- **Exceptions (`ExceptT`)**: Error conditions are specified using `signals (e : ε) => ...`.

### Method Parameter Binders

Velvet supports all native Lean 4 binder formats in method signatures:

- **Explicit typed binders**: `(x : Nat)`
- **Multi-variable binders**: `(x y : Nat)`
- **Implicit parameters**: `{α : Type}`, `{α β : Type}`
- **Typeclass instance binders**: `[Inhabited α]`, `[inst : Add α]`
- **Strict implicit binders**: `⦃α : Type⦄`
- **Dependent binders**: `(n : Nat) (xs : List (Fin (n + 1)))`

```lean
method combinedMethod (x y : Nat) {α : Type} [Inhabited α] (val : α)
    returns (res : Nat × α) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = (x + y, val)
do
  return (x + y, val)
```

### Logical / Ghost Variables (`given` Clause)

The `given` clause introduces **logical (ghost) variables** for the specification triple.

- **Specification Scope**: `given` variables are quantified in the generated specification theorem (`<name>.spec_triple` / `<name>.spec`) and can be referenced in `requires`, `signals`, and `ensures` clauses.
- **Program Isolation**: They are **not** parameters to the executable function and **cannot** be referenced inside the `do` body.
- **Binder Types**: `given` supports all Lean binder types (e.g. `given (s₀ : Nat)`, `given (lo hi : Nat) {d : Nat}`).

#### Canonical Pattern: Capturing Initial State `s₀` in `StateM`

The classic Hoare logic pattern for stateful programs is capturing the initial state `s₀` before mutation, and specifying that the final state differs from the initial state by a given delta `x`:

```lean
method incrementBy (x : Nat) returns (res : PUnit) in StateM Nat
  given (s₀ : Nat)
  requires (s : Nat) => s = s₀
  ensures (s : Nat) => s = s₀ + x
do
  let s ← get
  set (s + x)

prove_correct incrementBy by
  velvet_vcgen [incrementBy] with finish

#check @incrementBy.spec
-- incrementBy.spec : ∀ (x s₀ : Nat),
--   ⦃ fun s => s = s₀ ⦄ incrementBy x ⦃ fun res s => s = s₀ + x ⦄
```

### Checking Supplied Inputs

`#derive_tester_for` generates a contract checker. Supply inputs yourself or with any
external generator; no generator library or correctness proof is required.

```lean
open Velvet.Testing

method increment (x : Nat) returns (result : Nat) in StateM Nat
  given (initial : Nat)
  requires (s : Nat) => s = initial ∧ s + x ≤ 100
  ensures (s : Nat) => result = initial ∧ s = initial + x
do
  let old ← get
  set (old + x)
  return old

#derive_tester_for increment

-- Arguments: x, given initial, execution state
#eval increment.check 5 20 20  -- TestVerdict.pass
#eval increment.check 5 99 99  -- TestVerdict.discard
```

A false `requires` returns `.discard` without executing the method. Otherwise,
`ensures` or `signals` determines `.pass` or `.fail`. Checker arguments are method
arguments, then `given` arguments, then initial states/environments in monad-stack order.
There is no execution timeout, and passing tests do not prove the contract.

Decidability is inferred automatically, including bounded `Nat`/`Int` heuristics.
For custom executable decisions, use `prove_precondition_decidable_for`,
`prove_postcondition_decidable_for`, or `prove_signals_decidable_for` with `by …`
**before** `#derive_tester_for`. Proofs start with arguments introduced and assertion
wrappers simplified. See [the examples](Velvet/Examples/Testing.lean) for monad stacks
and a manual local instance (`withdraw`).

Custom monads need a [DecidableWP instance](Velvet/Core/DecidableWP.lean) matching their
WP interpretation. Instances cover `Id`, `Option`, `Except`, `EStateM`, and the
`StateT`, `ReaderT`, `ExceptT`, and `OptionT` transformers.

### Automatic `ExceptT` Inference

If you write `signals` clauses without an explicit `in <Monad>` stack, Velvet automatically infers and stacks the required `ExceptT` monad transformers around `Option`:

- A single signal `signals boom : (e : String) => ...` infers `ExceptT String Option α`:
  ```lean
  method maybeFail (b : Bool) returns (res : Nat)
    requires True
    signals boom : (e : String) => e = "boom"
    ensures res = 0
  do
    if b then throw "boom"
    return 0
  
  #check maybeFail  -- maybeFail (b : Bool) : ExceptT String Option Nat
  ```
- Multiple signals stack nested `ExceptT` layers (e.g. `signals str : (e : String) => ...` and `signals nat : (e : Nat) => ...` infer `ExceptT String (ExceptT Nat Option) α`).

> 📁 **Examples**:
> - Basic arithmetic: [`Sqrt.lean`](Velvet/Examples/Sqrt.lean)
> - Binder types: [`BindersTest.lean`](Velvet/Examples/BindersTest.lean)
> - Recursion & `given`: [`Recursion.lean`](Velvet/Examples/Recursion.lean), [`MatchRecursion.lean`](Velvet/Examples/MatchRecursion.lean)
> - State & Exceptions: [`StateT.lean`](Velvet/Examples/StateT.lean), [`AutomaticExceptionInference.lean`](Velvet/Examples/AutomaticExceptionInference.lean)
> - Intrinsic verification: [`VelvetAndIntrinsicVerification.lean`](Velvet/Examples/VelvetAndIntrinsicVerification.lean)

---

## 5. Total vs. Partial Correctness

- **Total Correctness (Default)**: Guarantees termination. Loops require a `decreasing` measure.
- **Partial Correctness**: Allows non-termination. Configured with `set_option velvet.semantics.termination "partial" in` (or `signals (_ : Unit) => True`). Loops do not require a `decreasing` measure.

> 📁 **Examples**:
> - Total correctness: [`IsSorted.lean`](Velvet/Examples/IsSorted.lean), [`IsNonPrime.lean`](Velvet/Examples/IsNonPrime.lean)
> - Partial correctness: [`LoopControl.lean`](Velvet/Examples/LoopControl.lean)

---

## 6. Loop Verification

### `while'` Loops

```lean
while' [<cond_name> :]? <condition>
  [invariant [<inv_name> :]? [(<state_binders>) =>]? <Invariant>]*
  [decreasing [<meas_name> :]? <measure_expr>]?
  [done_with [<done_name> :]? [(<state_binders>) =>]? <DonePredicate>]?
do
  <body>
```

### `for'` Loops

```lean
for' [[<h> :]? <elem> in <collection>]
  [invariant [<inv_name> :]? <Invariant>]*
  [done_with [<done_name> :]? <DonePredicate>]?
do
  <body>
```

#### 1. Pure State Invariants (No `done_with` needed)
If an invariant only mentions outer mutable state variables (e.g. `s`, `x`, `y`), Velvet automatically uses the invariant as **both the step invariant and the loop-exit condition**:

```lean
method twoVarPureState (n : Nat) returns (r : Nat)
  ensures r % 2 = 0
do
  let mut x := 0
  let mut y := 0
  for' i in List.range n
    invariant xy_even: (x + y) % 2 = 0  -- Only mentions outer state variables x and y
  do
    x := x + 1
    y := y + 1
  return x + y
```

#### 2. Iteration-Local Variables (`i`, `__pref`, `__rest`) and `done_with`
Outer mutable variables (like `let mut x := 0`) remain in scope after the loop, so referencing them never requires `done_with`.

However, variables tied to the loop's iteration:
- **Loop variable `i` / `elem`**: The iteration variable bound by `for' i in ...` or `for' elem in ...`.
- **`__pref`**: The list of already processed elements in preceding iterations.
- **`__rest`**: The list of remaining elements to be processed in subsequent iterations.

go **out of scope** when the loop terminates. When an invariant references any of these iteration-local variables, an explicit `done_with` clause is required to specify what holds upon exit:

```lean
method twoVar (n : Nat) returns (r : Nat)
  ensures r = n
do
  let mut x := 0
  let mut y := 0
  for' i in List.range n
    invariant xy: x = i ∧ y = i       -- References loop variable `i`
    done_with d: x = n ∧ y = n        -- Explicit exit condition
  do
    x := x + 1
    y := y + 1
  return x
```

#### 3. In-Scope Membership Proof (`for' h : x in xs`)
You can bind a proof that the current element belongs to the collection:

```lean
method memberBound (xs : List Nat) (bound : Nat) returns (sum : Nat)
  requires ∀ x ∈ xs, x ≤ bound
  ensures sum ≥ 0
do
  let mut s := 0
  for' h : x in xs
    invariant nonneg: s ≥ 0
  do
    assert h_in: x ∈ xs  -- `h : x ∈ xs` is in scope!
    s := s + x
  return s
```

#### 4. Control Flow: `break`, `continue`, and Early `return`
Velvet supports standard imperative control flow inside both `while'` and `for'` loops:
- **`continue`**: Skips the remainder of the current iteration while preserving the loop invariant.
- **`break`**: Exits the loop early (specifying `done_with` handles the early exit condition).
- **`return`**: Returns directly from the enclosing method from inside the loop body.

> 📁 **Examples**:
> - Loop patterns & invariants: [`Loops.lean`](Velvet/Examples/Loops.lean)
> - `break`, `continue`, early `return`: [`LoopControl.lean`](Velvet/Examples/LoopControl.lean)
> - Range loops: [`LoopsExplicitVCs.lean`](Velvet/Examples/LoopsExplicitVCs.lean)

---

## 7. In-Body Verification Statements

### `assert`
Emits a proof obligation at that program point and adds the assertion to the context thereafter:

```lean
assert [<name> :]? <Predicate>
```

### Ghost State (`let ghost` and `*var := ...`)
Ghost variables exist purely for specification and verification purposes and are erased at compilation:

- **Declaration**: `let ghost <name> := <value>`
- **Reassignment**: `*<name> := <new_value>`
- **Reading in specs**: `<name>.reveal`

```lean
method tickWithGhost returns (res : Nat)
  requires True
  ensures True
do
  let mut i := 0
  let ghost ctr := 0
  while' loop_cond: i < 10
    invariant ghost_ctr: ctr.reveal = i
    decreasing rem: 10 - i
  do
    i := i + 1
    *ctr := ctr + 1
  return i
```

> 📁 **Example**: [`Loops.lean`](Velvet/Examples/Loops.lean)

---

## 8. Verification & Proving (`velvet_vcgen`)

### Clause Naming & Error Locations

All specification clauses automatically track their source locations. If a verification obligation cannot be discharged by `velvet_vcgen [...] with finish`, Lean reports the error directly at the failing clause in your code (e.g. highlighting the exact `invariant` or `assert` that failed).

You can optionally label clauses with custom names:
- `requires [<req_name> :]? ...`
- `ensures [<post_name> :]? ...`
- `signals [<err_name> :]? ...`
- `invariant [<inv_name> :]? ...`
- `decreasing [<meas_name> :]? ...`
- `done_with [<done_name> :]? ...`
- `assert [<check_name> :]? ...`

If omitted, default names like `invariant1`, `ensures1`, `ensures2`, etc., are assigned automatically. Custom labels give semantic names to the corresponding subgoals in interactive proofs (`case <inv_name> => ...`).

### Automated Proofs (`with finish`)

When all verification conditions can be discharged automatically with `grind` and simplification:

```lean
prove_correct <method_name> by
  velvet_vcgen [<method_name> (, <callee>)*] with finish
```

### Interactive Proofs (`with try finish`)

When some goals require interactive tactics, use `with try finish` to automatically discharge routine goals and solve the remaining subgoals with `case <name> => ...`:

```lean
prove_correct <method_name> by
  velvet_vcgen [<method_name> (, <callee>)*] with try finish
  [case <tag> => <interactive_tactic>]*
```

### Progress Reporting & Diagnostics

With `set_option velvet_vcgen.showProgress true` (default), `velvet_vcgen` reports real-time verification status in the Infoview:

```text
[velvet:isqrt] ℹ Generated 3 VCs:
  • [1/3] 'inv_lower'
  • [2/3] 'by_remaining'
  • [3/3] 'done'
[velvet:isqrt] ✔ Finished: 3/3 solved
```

### Elaboration-Time (Intrinsic) Verification

With `set_option velvet.verifyDuringElab true`, methods automatically run `velvet_vcgen with finish` during elaboration. If verification succeeds, `<name>.spec` is produced immediately without needing a separate `prove_correct` block:

```lean
set_option velvet.verifyDuringElab true

method absDiff (x : Nat) (y : Nat) returns (res : Nat)
  ensures res ≥ 0
  ensures x ≥ y → res = x - y
do
  if x ≥ y then return x - y else return y - x

#check absDiff.spec  -- Automatically verified and generated!
```

### Branch Hypothesis Naming

Velvet automatically names hypotheses from conditionals:
- `if h : cond` names `h : cond` and `¬cond`.
- `bif b` (statement or expression `let y := bif b ...`) names `b = true` and `b = false`.
- `match` introduces pattern equality hypotheses.

> 📁 **Examples**:
> - Interactive discharge: [`IsSorted.lean`](Velvet/Examples/IsSorted.lean), [`IsNonPrime.lean`](Velvet/Examples/IsNonPrime.lean)
> - Intrinsic verification: [`IntrinsicVerification.lean`](Velvet/Examples/IntrinsicVerification.lean)
> - Branch naming: [`HypNaming.lean`](Velvet/Examples/HypNaming.lean)

---

## 9. Monad Lifting & Composition

Velvet supports lifting between monad layers (`Id`, `Option`, `ExceptT`, `StateT`, `ReaderT`, and custom lifts) and interoperates with Lean intrinsic verification.

> 📁 **Examples**: [`LiftingExamples.lean`](Velvet/Examples/LiftingExamples.lean), [`VelvetAndIntrinsicVerification.lean`](Velvet/Examples/VelvetAndIntrinsicVerification.lean)

---

## 10. Examples Reference

All examples are located in [`Velvet/Examples/`](Velvet/Examples):

| File | Description |
| :--- | :--- |
| [`Sqrt.lean`](Velvet/Examples/Sqrt.lean) | Integer square root with loop invariant and measure |
| [`IsSorted.lean`](Velvet/Examples/IsSorted.lean) | Array sortedness checking (total correctness) |
| [`IsNonPrime.lean`](Velvet/Examples/IsNonPrime.lean) | Primality testing and bounds (total correctness) |
| [`SumOfDigits.lean`](Velvet/Examples/SumOfDigits.lean) | Digit peeling loop |
| [`MaxElem.lean`](Velvet/Examples/MaxElem.lean) | Maximum element in array |
| [`InsertionSort.lean`](Velvet/Examples/InsertionSort.lean) | In-place insertion sort |
| [`RunLengthEncoding.lean`](Velvet/Examples/RunLengthEncoding.lean) | Run-length list encoding |
| [`Loops.lean`](Velvet/Examples/Loops.lean) | Loop patterns (`while'`, `for in`, multi-state) |
| [`LoopsExplicitVCs.lean`](Velvet/Examples/LoopsExplicitVCs.lean) | Explicit subgoal proofs with `case <tag>` |
| [`BindersTest.lean`](Velvet/Examples/BindersTest.lean) | All supported parameter binder kinds and `given` clauses |
| [`Recursion.lean`](Velvet/Examples/Recursion.lean) | Recursive `method rec` definitions |
| [`MatchRecursion.lean`](Velvet/Examples/MatchRecursion.lean) | Pattern matching recursion |
| [`StateT.lean`](Velvet/Examples/StateT.lean) | Stateful verification (`StateT`, `ReaderT`) |
| [`StateTExplicitVCs.lean`](Velvet/Examples/StateTExplicitVCs.lean) | Explicit VC proofs for `StateT` |
| [`AutomaticExceptionInference.lean`](Velvet/Examples/AutomaticExceptionInference.lean) | Exception channel inference |
| [`HypNaming.lean`](Velvet/Examples/HypNaming.lean) | Condition hypothesis naming (`if`, `bif`, `match`) |
| [`LiftingExamples.lean`](Velvet/Examples/LiftingExamples.lean) | Monad lifting across transformer stacks |
| [`MemAlloc.lean`](Velvet/Examples/MemAlloc.lean) | Linked-list allocator with ghost pointers |
| [`IntrinsicVerification.lean`](Velvet/Examples/IntrinsicVerification.lean) | Elaboration-time automatic verification (`velvet.verifyDuringElab`) |
| [`VelvetAndIntrinsicVerification.lean`](Velvet/Examples/VelvetAndIntrinsicVerification.lean) | Interoperability with intrinsic contracts and `given` |
| [`ErrorMsgs.lean`](Velvet/Examples/ErrorMsgs.lean) | Compiler error diagnostic tests |
