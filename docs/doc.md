# Velvet Language Documentation

## 1. Introduction

### What is Velvet?

Velvet lets you write imperative programs and prove their contracts in Lean 4. Its syntax is inspired by Dafny.

### The Velvet Advantage: Hybrid Verification

You can combine automatic verification with interactive Lean proofs:

1. **Automated Proof:** The `velvet_vcgen` tactic with `finish` attempts to automatically prove the correctness of the method using Lean's `grind` tactic and arithmetic simplification. For many methods, this is all that is needed.
2. **Interactive Proving:** If automated solving leaves remaining goals, you are not stuck. You can use `case <name> => ...` to target specific verification conditions with interactive Lean tactics (`omega`, `induction`, `rcases`, etc.).

---

## 2. Quick Start

The repository uses Lean **v4.34.0**, selected by `lean-toolchain`.

`import Velvet` is enough for ordinary `method` declarations and `prove_correct`
proofs.

### Your First Velvet Method

Here is a simple, working example:

```lean
import Velvet

-- set_option velvet.verifyOnDefinition true in
method isqrt (n : Nat) returns (r : Nat)
  requires True
  ensures r * r ≤ n ∧ n < (r + 1) * (r + 1)
do
  let mut x : Nat := 0
  while loop_cond: (x + 1) * (x + 1) ≤ n
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

**NOTE**: The commented `set_option velvet.verifyOnDefinition true in` will
try to do the proofs automatically using `velvet_vcgen [<method_name>] with finish`
and remove the need for `prove_correct`. If the proof couldn't be discharged fully,
it'd throw an error highlighting the part that couldn't be discharged.

---

## 3. Writing Methods

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

- **Default Monad (`Option`)**: When `in <Monad>` is omitted and no `signals` clause is provided, methods default to `Option`.
- **Stateful Methods (`StateT`)**: Initial and final state binders are specified using `(s : σ) => ...`.
- **Exceptions (`ExceptT`)**: Error conditions are specified using `signals (e : ε) => ...`.

### Method Parameter Binders

Velvet supports all native Lean 4 binder formats in method signatures:

- **Explicit typed binders**: `(x : Nat)`
- **Multi-variable binders**: `(x y : Nat)`
- **Implicit parameters**: `{α : Type}`, `{α β : Type}`
- **Typeclass instance binders**: `[Inhabited α]`, `[inst : Add α]`
- **Dependent binders**: `(n : Nat) (xs : List (Fin (n + 1)))`

```lean
method combinedMethod (x y : Nat) {α : Type} [Inhabited α] (val : α)
    returns (res : Nat × α) in StateT Nat Id
  requires (s : Nat) => True
  ensures (s : Nat) => res = (x + y, val)
do
  return (x + y, val)
```

### Logical Variables (`given` Clause)

The `given` clause introduces **logical (ghost) variables** for the contract.

- **Specification Scope**: Use `given` variables in `requires`, `signals`, and `ensures` clauses. The proof must cover every value allowed by the preconditions.
- **Program Isolation**: They are **not** parameters to the executable function and **cannot** be referenced inside the `do` body.
- **Binder Types**: `given` supports all Lean binder types (e.g. `given (s₀ : Nat)`, `given (lo hi : Nat) {d : Nat}`).

#### Canonical Pattern: Capturing Initial State `s₀` in `StateM`

A common pattern for stateful programs is capturing the initial state `s₀` before mutation, and specifying that the final state differs from the initial state by a given delta `x`:

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

### Proving Contracts and Recursive Methods

A `method foo` declaration defines the program and its contract.
`prove_correct foo by …` proves the contract and names the theorem `foo.spec`.
Velvet can then use that contract automatically when verifying calls to `foo`.

Use `method rec` when a method calls itself. A proof can often proceed by induction
on an argument:

```lean
method rec countUp (n : Nat)
  returns (res : Nat)
  ensures res_eq: res = n
do
  match n with
  | .zero => pure 0
  | .succ k =>
    let b ← countUp k
    pure (Nat.succ b)

prove_correct countUp by
  intro n
  induction n with
  | zero => unfold countUp; velvet_vcgen with finish
  | succ k ih => unfold countUp; velvet_vcgen with finish
```

See [`Recursion.lean`](Velvet/Examples/Recursion.lean) for
complete recursive proofs, including methods with `given` parameters.

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

For property-based testing, use Plausible to generate arguments for the checker.
[`Testing.lean`](Velvet/Examples/Testing.lean) includes a 100-case run that reports
the discarded and passed totals and reports the generated inputs on failure.

A false `requires` returns `.discard` without executing the method. Otherwise,
`ensures` or `signals` determines `.pass` or `.fail`. Checker arguments are method
arguments, then `given` arguments, then initial states/environments in monad-stack order.
There is no execution timeout, and passing tests do not prove the contract.

The checker needs an executable way to decide whether each condition holds.
Velvet handles many conditions automatically, including bounded `Nat`/`Int`
quantifiers. If it cannot derive a check, supply one using
`prove_precondition_decidable_for`, `prove_postcondition_decidable_for`, or
`prove_signals_decidable_for` with `by …` **before** `#derive_tester_for`.
See [`Testing.lean`](Velvet/Examples/Testing.lean), particularly `withdraw`, for an example.

Testers support `Id`, `Option`, `Except`, `EStateM`, and combinations using `StateT`,
`ReaderT`, `ExceptT`, and `OptionT`. Other monads may need custom testing support.

### Automatic `ExceptT` Inference

When `in <Monad>` is explicit, supply the exception clauses for that monad.
For example, `in Option` needs a bare `signals` clause, while
`in StateM Nat` has no exception channel. The automatic Option defaults below apply
when `in <Monad>` is omitted.

Option failure has no exception value: write `signals False` to forbid it or
`signals True` to allow it. With no explicit `in <Monad>`, a bare signal keeps the
base monad as `Option`. Typed exception binders infer `ExceptT` layers around it;
an optional final bare signal specifies the base Option failure condition.
If omitted, that condition defaults to `False` for total correctness and `True`
for partial correctness:


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

## 4. Total vs. Partial Correctness

- **Total mode (default)**: `while` loops require a natural-number `decreasing` measure. For an inferred Option-based monad, the default failure postcondition is `False`, so a proved contract excludes Option failure/divergence under its precondition.
- **Partial mode**: `set_option velvet.semantics.termination "partial" in` allows `while` without a measure and changes the inferred Option failure postcondition to `True`. Normal returns must still satisfy `ensures`.

`for` loops have no `decreasing` clause. For Option-based methods, explicitly
writing `signals True` allows failure or nontermination even in total mode.
Use `prove_correct` to establish the contract; declaring the method alone does not prove it.

> 📁 **Examples**:
> - Total correctness: [`IsSorted.lean`](Velvet/Examples/IsSorted.lean), [`IsNonPrime.lean`](Velvet/Examples/IsNonPrime.lean)
> - Partial correctness: [`LoopControl.lean`](Velvet/Examples/LoopControl.lean)

---

## 5. Loop Verification

After `import Velvet`, `while` and single-collection `for` loops use Velvet's
elaborators, including loops without inline clauses. In total mode, every
`while` requires a `decreasing` clause. Lean's additional forms, such as parallel
`for` and `while let`, retain their built-in behavior.

### `while` Loops

```lean
while [<cond_name> :]? <condition>
  [invariant [<inv_name> :]? [(<state_binders>) =>]? <Invariant>]*
  [decreasing [<meas_name> :]? <measure_expr>]?
  [done_with [<done_name> :]? [(<state_binders>) =>]? <DonePredicate>]?
do
  <body>
```

### `for` Loops

```lean
for [<h> :]? <elem> in <collection>
  [invariant [<inv_name> :]? <Invariant>]*
  [done_with [<done_name> :]? <DonePredicate>]?
do
  <body>
```

#### 1. Pure State Invariants (No `done_with` needed)
If an invariant only mentions outer mutable state variables (e.g. `s`, `x`, `y`), Velvet automatically uses the invariant as **both the step invariant and the loop-exit condition**:

```lean
set_option velvet.verifyOnDefinition true in
method twoVarPureState (n : Nat) returns (r : Nat)
  ensures r % 2 = 0
do
  let mut x := 0
  let mut y := 0
  for i in List.range n
    invariant xy_even: (x + y) % 2 = 0  -- Only mentions outer state variables x and y
  do
    x := x + 1
    y := y + 1
  return x + y
```

#### 2. Iteration-Local Variables (`i`, `__pref`, `__rest`) and `done_with`
Outer mutable variables (like `let mut x := 0`) remain in scope after the loop, so referencing them never requires `done_with`.

However, variables tied to the loop's iteration:
- **Loop variable `i` / `elem`**: The iteration variable bound by `for i in ...` or `for elem in ...`.
- **`__pref`**: The list of already processed elements in preceding iterations.
- **`__rest`**: The list of remaining elements to be processed in subsequent iterations.

go **out of scope** when the loop terminates. When an invariant references any of these iteration-local variables, an explicit `done_with` clause is required to specify what holds upon exit:

```lean
set_option velvet.verifyOnDefinition true in
method twoVar (n : Nat) returns (r : Nat)
  ensures r = n
do
  let mut x := 0
  let mut y := 0
  for i in List.range n
    invariant xy: x = i ∧ y = i       -- References loop variable `i`
    done_with d: x = n ∧ y = n        -- Explicit exit condition
  do
    x := x + 1
    y := y + 1
  return x
```

#### 3. In-Scope Membership Proof (`for h : x in xs`)
You can bind a proof that the current element belongs to the collection:

```lean
set_option velvet.verifyOnDefinition true in
method memberBound (xs : List Nat) (bound : Nat) returns (sum : Nat)
  requires ∀ x ∈ xs, x ≤ bound
  ensures sum ≥ 0
do
  let mut s := 0
  for h : x in xs
    invariant nonneg: s ≥ 0
  do
    assert h_in: x ∈ xs  -- `h : x ∈ xs` is in scope!
    s := s + x
  return s
```

#### 4. Control Flow: `break`, `continue`, and Early `return`
Velvet supports standard imperative control flow inside both `while` and `for` loops:
- **`continue`**: Skips the remainder of the current iteration while preserving the loop invariant.
- **`break`**: Exits the loop early (specifying `done_with` handles the early exit condition).
- **`return`**: Returns directly from the enclosing method from inside the loop body.

> 📁 **Examples**:
> - Loop patterns & invariants: [`Loops.lean`](Velvet/Examples/Loops.lean)
> - `break`, `continue`, early `return`: [`LoopControl.lean`](Velvet/Examples/LoopControl.lean)
> - Range loops: [`LoopsExplicitVCs.lean`](Velvet/Examples/LoopsExplicitVCs.lean)

---

## 6. In-Body Verification Statements

### `assert`
Emits a proof obligation at that program point and adds the assertion to the context thereafter:

```lean
assert <name> : <Predicate>
```

The label is required and lets you refer to the assertion's proof obligation by name.
Assertions are checked during verification but they are just `pure ()` under the hood.

### Ghost State (`let ghost` and `var *:= ...`)
Ghost variables exist purely for specification and verification purposes and are erased at compilation:

- **Declaration**: `let ghost <name> := <value>`
- **Reassignment**: `<name> *:= <new_value>`
- **Reading in specs**: `<name>.reveal`

```lean
open scoped GhostSyntax

method tickWithGhost returns (res : Nat)
  requires True
  ensures True
do
  let mut i := 0
  let ghost ctr := 0
  while loop_cond: i < 10
    invariant ghost_ctr: ctr.reveal = i
    decreasing rem: 10 - i
  do
    i := i + 1
    ctr *:= ctr + 1
  return i
```

The right-hand side can use ghost variables directly: `ctr *:= ctr + 1`
increments the ghost counter. Use `ctr.reveal` when referring to it in a specification.

`Ghost` gives us almost-zero overhead at runtime, and can be really useful to
do logical computations in a monad, that would affect the proof but have no effects during execution.

> Ghost in Velvet is inspired from [Mathlib's Erased.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Erased.lean)

> 📁 **Example**: [`Loops.lean`](Velvet/Examples/Loops.lean)

---

## 7. Verification & Proving (`velvet_vcgen`)

### Clause Naming & Error Locations

Errors from `with finish` can point directly to the failing clause, such as an
`invariant` or `assert`. Use `with try finish` to leave unresolved goals available
for interactive proof.

Specification clauses accept optional labels; `assert` requires one:
- `requires [<req_name> :]? ...`
- `ensures [<post_name> :]? ...`
- `signals [<err_name> :]? ...`
- `invariant [<inv_name> :]? ...`
- `decreasing [<meas_name> :]? ...`
- `done_with [<done_name> :]? ...`
- `assert <check_name> : ...` (label required)

If omitted, default names like `invariant1`, `ensures1`, `ensures2`, etc., are assigned automatically. Custom labels give semantic names to the corresponding subgoals in interactive proofs (`case <inv_name> => ...`).

### Automated Proofs (`with finish`)

When all verification conditions can be discharged automatically with `grind` and simplification:

```lean
prove_correct <method_name> by
  velvet_vcgen [<method_name> (, <callee>)*] with finish
```

Generally if you expect your proof to be discharged with `finish`, we recommend having
`set_option velvet.verifyOnDefinition true`, which would remove the need to write out
the `prove_correct` block, and in case verification fails, it'll generally highlight the
error at the offending assertion location.

### Interactive Proofs (`with try finish`)

When some goals require interactive tactics, use `with try finish` to automatically discharge routine goals and solve the remaining subgoals with `case <name> => ...`:

```lean
prove_correct <method_name> by
  velvet_vcgen [<method_name> (, <callee>)*] with try finish
  [case <tag> => <interactive_tactic>]*
```

### Simplifying Assumptions

```text
velvet_vcgen [definitions_or_specs]
  simplifying_assumptions [lemma₁, lemma₂]
  with <grind tactic>
```

The first list supplies definitions to unfold, simp lemmas, or specification theorems.
Registered `@[spec]` theorems are available automatically. The optional
`simplifying_assumptions` clause simplifies hypothesis types with the listed lemmas.
The optional `with` clause applies a grind-mode tactic, such as `finish` or
`try finish`, to each generated VC.

### Verification Condition Reports

Enable `set_option velvet_vcgen.showVCReport true` to see how each VC was handled
in a `prove_correct` proof:

```text
[vcgen:isqrt] 2/3 VCs solved
  ✔ inv_lower: solved by velvet_vcgen
  ✔ by_remaining: solved afterward
  ○ done: 1 remaining
```

The report updates after each edit finishes checking, including for incomplete
proofs. `sorry` is marked as admitted. Find it in the messages at the method name;
VS Code also displays it as you move through the proof.

Outside `prove_correct`, the report covers only the `velvet_vcgen` invocation.

### Branch Hypothesis Naming

Velvet automatically names hypotheses from conditionals:
- `if cond` uses `if_cond` for the positive or negative branch hypothesis.
- `if h : cond` uses the supplied name `h` in either branch.
- `match` preserves usable equation names and gives constructor equalities names such as `h_cons`.

Use ordinary `if` for Boolean conditions too.

> 📁 **Examples**:
> - Interactive discharge: [`IsSorted.lean`](Velvet/Examples/IsSorted.lean), [`IsNonPrime.lean`](Velvet/Examples/IsNonPrime.lean)
> - Intrinsic verification: [`IntrinsicVerification.lean`](Velvet/Examples/IntrinsicVerification.lean)
> - Branch naming: [`HypNaming.lean`](Velvet/Examples/HypNaming.lean)

---

## 8. Monad Lifting & Composition

Velvet supports lifting between monad layers (`Id`, `Option`, `ExceptT`, `StateT`, `ReaderT`, and custom lifts) and interoperates with Lean intrinsic verification.

> 📁 **Examples**: [`LiftingExamples.lean`](Velvet/Examples/LiftingExamples.lean), [`VelvetAndIntrinsicVerification.lean`](Velvet/Examples/VelvetAndIntrinsicVerification.lean)

### Nondeterministic Choice

`let x :| condition` chooses a value satisfying a condition. Use `DemonicT Option`
when the method must meet its contract for every allowed choice:

```lean
import Velvet

method chooseNext (n : Nat) returns (res : Nat) in DemonicT Option
  signals False
  ensures res = n + 1
do
  let (x : Nat) :| x = n + 1
  return x

prove_correct chooseNext by
  velvet_vcgen [chooseNext] with finish

#eval (chooseNext 5).run  -- some 6
```

Here the condition determines `x` exactly, so running `chooseNext 5` with `.run`
returns `some 6`. A condition can also permit several values; the proof must then
work for all of them. `signals False` requires that the choice succeeds.

For proofs that only need to show that **some** choice meets the contract, use
`AngelicT Option`. Executing an angelic method may choose a different value from
the one used in the proof.

See [`NonDet.lean`](Velvet/Examples/NonDet.lean) for choices with several possible
values, choices inside loops, and stateful examples.

---

## 9. Examples Reference

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
| [`Loops.lean`](Velvet/Examples/Loops.lean) | Loop patterns (`while`, `for in`, multi-state) |
| [`LoopsExplicitVCs.lean`](Velvet/Examples/LoopsExplicitVCs.lean) | Explicit subgoal proofs with `case <tag>` |
| [`BindersTest.lean`](Velvet/Examples/BindersTest.lean) | All supported parameter binder kinds and `given` clauses |
| [`Recursion.lean`](Velvet/Examples/Recursion.lean) | Recursive `method rec` definitions |
| [`MatchRecursion.lean`](Velvet/Examples/MatchRecursion.lean) | Pattern matching recursion |
| [`StateT.lean`](Velvet/Examples/StateT.lean) | Stateful verification (`StateT`, `ReaderT`) |
| [`StateTExplicitVCs.lean`](Velvet/Examples/StateTExplicitVCs.lean) | Explicit VC proofs for `StateT` |
| [`AutomaticExceptionInference.lean`](Velvet/Examples/AutomaticExceptionInference.lean) | Exception channel inference |
| [`HypNaming.lean`](Velvet/Examples/HypNaming.lean) | Condition hypothesis naming (`if`, dependent `if`, `match`) |
| [`LiftingExamples.lean`](Velvet/Examples/LiftingExamples.lean) | Monad lifting across transformer stacks |
| [`MemAlloc.lean`](Velvet/Examples/MemAlloc.lean) | Linked-list allocator with ghost pointers |
| [`IntrinsicVerification.lean`](Velvet/Examples/IntrinsicVerification.lean) | Elaboration-time automatic verification (`velvet.verifyOnDefinition`) |
| [`VelvetAndIntrinsicVerification.lean`](Velvet/Examples/VelvetAndIntrinsicVerification.lean) | Interoperability with intrinsic contracts and `given` |
| [`ErrorMsgs.lean`](Velvet/Examples/ErrorMsgs.lean) | Compiler error diagnostic tests |
| [`LoopControl.lean`](Velvet/Examples/LoopControl.lean) | Partial loops, `break`, `continue`, and early return |
| [`SimplestSort.lean`](Velvet/Examples/SimplestSort.lean) | Sorting with interactive invariant proofs |
| [`NonDet.lean`](Velvet/Examples/NonDet.lean) | Demonic/angelic choice, finders, loops, and execution |
| [`Testing.lean`](Velvet/Examples/Testing.lean) | Generated contract checkers and custom decidability |

## 11. Case Studies

Larger case studies live in [`CaseStudies/`](CaseStudies/), which is a **separate
Lake package**. The root `velvet` package does not depend on Mathlib and must
stay that way, so anything needing Mathlib goes there:

```sh
cd CaseStudies
lake exe cache get
lake build
```

`lake build` at the repository root (and therefore CI) never descends into that
directory, and Mathlib never appears in the root `lake-manifest.json`. See
[`CaseStudies/README.md`](CaseStudies/README.md) for the layout and for how to
write a case-study file.