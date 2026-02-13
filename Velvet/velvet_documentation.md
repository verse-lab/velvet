# Velvet Language Documentation

## 1. Introduction

### What is Velvet?

Velvet is a language for writing programs with specifications, shallowly embedded in Lean. It allows you to prove the correctness of your programs with respect to their specifications using Lean's proof capabilities. The syntax is inspired by Dafny.

### The Velvet Advantage: Hybrid Verification

The primary strength of Velvet is its nature as a **shallowly embedded language** within Lean. This enables a powerful hybrid verification workflow that combines automated solving with the full power of Lean's interactive theorem proving.

1.  **Automated Proof:** The `loom_solve` tactic is the first line of attack. It attempts to automatically prove the correctness of the method. For many methods, this is all that is needed.

2.  **Interactive Proving:** If `loom_solve` fails to completely prove the method, you are not stuck. Because you are in the Lean environment, you can seamlessly add interactive Lean tactics to the `prove_correct` block to finish the proof. This allows you to handle complex proofs that are beyond the scope of automated solvers, while still benefiting from automation for the parts that can be automated.

**Example: Falling back to interactive tactics**

In some cases, `loom_solve` may not be able to solve all proof goals. Here, we can add interactive tactics like `grind` to complete the proof.

```lean
prove_correct cbrt by
  loom_solve
  -- Automated solving failed on one goal, but grind succeeds
  grind
```

## 2. Quick Start

### Your First Velvet Method

Let's start with a complete, working example. Here's a simple method that returns the minimum of two integers:

```lean
import Velvet.Std     -- Core Velvet language constructs
import CaseStudies.TestingUtil    -- Property-based testing utilities

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method Minimum (a: Int) (b: Int) return (minValue: Int)
    ensures minValue ≤ a
    ensures minValue ≤ b
    ensures minValue = a ∨ minValue = b
    do
    if a <= b then
        return a
    else
        return b

prove_correct Minimum by
  loom_solve
```

This example shows:
- **Method declaration** with typed parameters and return value
- **Postconditions** (`ensures`) that specify what the method guarantees
- **Implementation** in a `do` block using familiar syntax
- **Verification** using `prove_correct` - Velvet automatically verifies the method is correct!

### Running Your Method

Velvet methods are executable. You can run them using Lean's `#eval`:

```lean
#eval (Minimum 5 10).run  -- Expected: DivM.res 5
#eval (Minimum (-3) (-7)).run  -- Expected: DivM.res -7
```

### Testing Outputs with `#guard_msgs`

For basic testing, you can use `#guard_msgs` to verify that method outputs match expected values:

```lean
/--
info: DivM.res 5
-/
#guard_msgs in
#eval (Minimum 5 10).run

/--
info: DivM.res ((), #[1, 2, 3])
-/
#guard_msgs in
#eval (insertionSort #[3, 2, 1]).run
```

The `#guard_msgs` command verifies that the output matches the expected value in the doc comment. If the output doesn't match, Lean will report an error. 

>NOTE: For #guard_msgs to work, the the opening comment must be `/--` and the closing one must be `-/`.

### Understanding the Output

- The output will look like: `DivM.res 5`. The actual return value (5) is embedded in this structure.
- If the method involves mutable parameters, we would want to capture the changes to that as well in the output.
```lean
method insertionSort
  (mut arr: Array Int) return (u: Unit)
    ...

#eval ( insertionSort #[3,2,1] ).run
```
The output will be like `DivM.res ((), #[1, 2, 3])`. The `()` is the returned value from the method and `#[1,2,3]` is what the array becomes after sorting (it was mutated).

## 3. Setup & Configuration

### Required Imports

A typical Velvet file starts with these imports:

```lean
import Velvet.Std     -- Core Velvet language constructs
import CaseStudies.TestingUtil    -- Property-based testing utilities
```

### Semantics Options

Before writing methods, you must configure the semantics:

```lean
set_option loom.semantics.termination "partial"  -- or "total"
set_option loom.semantics.choice "demonic"
```

**`loom.semantics.termination`** (Required):
- `"partial"` - For potentially non-terminating programs (most common)
- `"total"` - For terminating programs with explicit termination proofs

**`loom.semantics.choice`** (Required):
- `"demonic"` - Standard choice for verification (most common)
- `"angelic"` - For angelic non-determinism

### Solver Configuration

Velvet supports multiple solver backends for automated verification. The solver choice determines which tactic `loom_solve` uses internally.

#### Grind Solver (Default & Recommended)

The `grind` solver uses Lean's built-in `grind` tactic. This is the **default** and works well for most cases:

```lean
set_option loom.solver "grind"  -- Optional, this is the default
set_option loom.solver.grind.splits 20  -- Optional, default is 20
```

**When to increase splits:**
- Complex proofs with many case splits
- Nested conditionals
- Default is 20, try 40-100 for complex proofs

**Example:**
```lean
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver.grind.splits 40  -- Increased for complex proof

method ComplexMethod (...) return (...)
  ...

prove_correct ComplexMethod by
  loom_solve  -- Uses grind with 40 splits
```

#### SMT Solvers (CVC5 or Z3)

**Important:** Z3 and CVC5 are now **auto-installed** when the project is built.

**Configuring SMT as the default solver:**

```lean
set_option loom.solver "cvc5"  -- or "z3"
set_option loom.solver.smt.timeout 4  -- timeout in seconds, default is 1

method ArithmeticMethod (...) return (...)
  ...

prove_correct ArithmeticMethod by
  loom_solve  -- Uses CVC5 SMT solver
```

**Mixing solvers (Hybrid approach):**

You can combine different solvers for different goals. Use `loom_solve` first (with your configured solver), then add other tactics for remaining goals.

Example - Use grind first, then SMT for remaining goals:
```lean
set_option loom.solver "grind"

prove_correct Method by
  loom_solve      -- Uses grind
  loom_auto       -- Uses SMT with solverHint attributes for remaining goals
```

Example - Use SMT first, then grind for remaining goals:
```lean
set_option loom.solver "cvc5"

prove_correct Method by
  loom_solve      -- Uses SMT
  grind           -- Uses grind for remaining goals
```

**SMT Solver Options:**
- `loom.solver.smt.timeout` - Timeout in seconds (default: 1)
- `loom.solver.smt.retryOnUnknown` - Retry with alternative solver on unknown (default: true)
- `loom.solver.smt.seed` - Random seed for solver (default: 0)

#### Custom Solver (Advanced)

For complete control over automation:

```lean
set_option loom.solver "custom"

-- Define your own loom_solver tactic
macro_rules
| `(tactic|loom_solver) => `(tactic|(
  try simp at *
  try grind
  try aesop))
```

**Important:** You MUST define the `loom_solver` macro before calling `prove_correct`.

### Performance Tuning

For complex proofs, you may need to increase Lean's execution limits:

```lean
set_option maxHeartbeats 1000000  -- Default is 200000

prove_correct ComplexMethod by
  loom_solve
```

Or scope it to a specific proof:

```lean
set_option maxHeartbeats 2000000 in
prove_correct VeryComplexMethod by
  loom_solve
```

**When to increase:**
- Complex proofs with nested loops
- Large methods with many invariants
- Timeout errors during verification
- Recursive data structures

**Typical values:**
- Default: 200000 (adequate for simple methods)
- Complex: 1000000-2000000
- Very complex: up to 5000000

## 4. Writing Methods

### Method Signatures

Methods are the basic unit of programs in Velvet:

```lean
method <method_name> (<param1>: <Type1>) (<param2>: <Type2>) ... return (<ret_name>: <RetType>)
```

**Example:**
```lean
method Add (x: Int) (y: Int) return (sum: Int)
```

**Multiple return values using tuples:**

Velvet doesn't support multiple return values directly, but you can return a tuple:

```lean
method DivMod (a: Nat) (b: Nat) return (result: Nat × Nat)
    require b > 0
    ensures result.1 = a / b  -- quotient
    ensures result.2 = a % b  -- remainder
    do
    return (a / b, a % b)
```

Access tuple elements with `.1`, `.2`, etc.:
```lean
let result ← DivMod 10 3
let quotient := result.1  -- 3
let remainder := result.2  -- 1
```

### Mutable Parameters

Parameters can be declared as mutable using the `mut` keyword. When a parameter is mutable, you can access its original value in postconditions and invariants using the `varOld` suffix.

**Simple example with mutable parameter:**
```lean
method Increment (mut x: Int) return (u: Unit)
    ensures x = xOld + 1
    do
    x := x + 1
    return
```

**Array mutation example:**
```lean
method DoubleAll (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
        invariant arr.size = arrOld.size
        invariant 0 ≤ i ∧ i ≤ arr.size
        invariant ∀ k, 0 ≤ k ∧ k < i → arr[k]! = 2 * arrOld[k]!
        invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
        done_with i = arr.size
    do
        arr := arr.set! i (2 * arr[i]!)
        i := i + 1
    return
```

**Sorting example showing multiset preservation:**
```lean
method BubbleSort (mut arr: Array Int) return (u: Unit)
    require arr.size > 0
    ensures ∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!
    ensures arrayToMultiset arrOld = arrayToMultiset arr
    do
    -- implementation with swap operations
    ...
```

**Key points about mutable parameters:**
- Use `mut` keyword before parameter name: `(mut arr: Array Int)`
- Access original value with `Old` suffix: `arrOld`, `xOld`, etc.
- `varOld` is available in both `ensures` and loop `invariant` clauses
- Commonly used to verify that mutations preserve certain properties (like multiset equality for sorting)

### Pre- and Post-conditions

Specify what your method requires and guarantees:

```lean
method CubeSurfaceArea (size: Int) return (area: Int)
    require size > 0
    ensures area = 6 * size * size
    do
    return 6 * size * size
```

**Multiple conditions:**
```lean
method BinarySearch (arr: Array Int) (target: Int) return (result: Bool × Nat)
    require arr.size > 0
    require forall i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!  -- sorted
    ensures result.1 = true → arr[result.2]! = target
    ensures result.1 = false → ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! ≠ target
```

### Data Types

Velvet uses Lean's data types:

- **`Int`**: Signed integers
- **`Nat`** or **`ℕ`**: Non-negative integers
- **`Bool`**: Boolean values
- **`Array <Type>`**: Arrays (e.g., `Array Int`)
- **`Unit`**: Unit type, for methods that don't return a meaningful value
- **`Option <Type>`**: Optional values
- **`List <Type>`**: Lists

**Prefer `Nat` over `Int` when possible** - it eliminates non-negativity preconditions and improves verification.

### Basic Statements

#### Variable Declaration

Mutable variables are declared with `let mut`:

```lean
let mut count := 0
let mut arr := Array.replicate 10 0
```

Immutable bindings:
```lean
let x := 5
let result ← someMethod()  -- For monadic operations
```

#### Conditionals

Standard if/then/else:

```lean
if condition then
    statement1
else
    statement2
```

**Important:** Velvet doesn't support `else if`. Nest conditionals instead:

```lean
-- DON'T: if/else if/then
-- if m = 0 then ... else if n = 0 then ...

-- DO: nested if inside else
if m = 0 then
    return n + 1
else
    if n = 0 then
        return m
    else
        return m + n
```

#### Loops

Use `while` loops for iteration (no `for` loops in Velvet):

```lean
let mut i := 0
while i < arr.size
    invariant 0 ≤ i ∧ i ≤ arr.size
    invariant result.size = arr.size
    done_with i = arr.size
do
    result := result.set! i (arr[i]! * 2)
    i := i + 1
```

**Loop annotations:**
- **`invariant`**: Conditions true at the start of each iteration (required for verification)
- **`done_with`**: Condition true when loop terminates (optional, defaults to negation of loop condition)

#### Loop Control Statements

**Break** - Exit loop early:
```lean
method FindTen (a: Nat) return (res: Nat)
  require a > 0
  ensures res > 0
  do
    let mut x := 0
    let mut t := a
    while t > 0
      invariant x + t = a
      done_with (x = 10 ∨ t = 0)
    do
      x := x + 1
      t := t - 1
      if (x = 10) then break
    return x
```

**Continue** - Skip to next iteration:
```lean
method SumEven (arr: Array Nat) return (res: Nat)
  ensures res = Array.sum (Array.filter (fun x => x % 2 = 0) arr)
  do
    let mut i := 0
    let mut s := 0
    while (i < arr.size)
      invariant i <= arr.size
      invariant s = Array.sum (Array.filter (fun x => x % 2 = 0) (Array.extract arr 0 i))
      done_with (s = Array.sum (Array.filter (fun x => x % 2 = 0) arr))
    do
      if (arr[i]! % 2 != 0) then
        i := i + 1
        continue
      s := s + arr[i]!
      i := i + 1
    return s
```

**Early Return conditionals(not inside loop)** - Return before reaching the end:
```lean
method ProcessArray (mut arr: Array Int) return (u: Unit)
  ensures /* postconditions */
  do
    if arr.size ≤ 1 then
      return  -- Early exit for base case
    else
      -- ... main computation
      return
```


**NOT SUPPORTED: Early return from a loop** - Return before reaching the end:
```lean
method Find10 (mut arr: Array Int) return (u: Unit)
  ensures /* postconditions */
  do
    let mut i := 0
    while (i < arr.size)
        invariant true = true -- skipping writing invariant since this example isn't supported
        do
            if arr[i]! = 10 then
                return true
            i := i + 1
    return false
```

**Important notes:**
- When using `break`, the `done_with` clause must account for the break condition
- Loop invariants must hold when `continue` is executed
- Early returns must satisfy all postconditions at the point of return
- **Early return from within a loop is not supported currently.**

#### Array Operations

**Creation:**
```lean
let arr := Array.replicate 10 0  -- Array of 10 zeros
```

**Size:**
```lean
let n := arr.size
```

**Access** (note the `!`):
```lean
let elem := arr[i]!
```

**Update** (returns a new array):
```lean
arr := arr.set! i value
```

**Complete example:**
```lean
method DoubleElements (a: Array Int) return (result: Array Int)
    ensures result.size = a.size
    ensures ∀ i, 0 ≤ i ∧ i < a.size → result[i]! = 2 * a[i]!
    do
    let mut result := Array.replicate a.size 0
    let mut i := 0
    while i < a.size
        invariant result.size = a.size
        invariant 0 ≤ i ∧ i ≤ a.size
        invariant ∀ k, 0 ≤ k ∧ k < i → result[k]! = 2 * a[k]!
        done_with i = a.size
    do
        result := result.set! i (2 * a[i]!)
        i := i + 1
    return result
```

#### Method Calls

Use monadic syntax to call other methods:

```lean
let result ← otherMethod arg1 arg2
```

**Example:**
```lean
method Factorial (n: Nat) return (res: Nat)
  ensures res > 0
  do
    if n = 0 then
      return 1
    else
      let prev ← Factorial (n - 1)
      return n * prev
```

#### Return Statements

```lean
return value
```

For methods returning `Unit`:
```lean
return
```

## 5. Verification

### The prove_correct Block

After defining a method, prove its correctness:

```lean
prove_correct SimpleMethod by
  loom_solve
  <tactics to solve the remaining goals, if any>
```

### Working Around Incrementality Issues with `prove_correct?`

When working on complex proofs interactively, you may encounter an incrementality issue where `loom_solve` re-runs every time you make changes to the proof script, even when those changes are after `loom_solve`. This can make interactive proving very slow, especially when `loom_solve` takes several seconds to complete.

**The workaround**: Use `prove_correct?` to generate a native Lean theorem statement, which has better incrementality support. This command prints the correctness theorem that `prove_correct` generates internally, allowing you to state and prove it explicitly as a regular Lean theorem.

```lean
prove_correct? SimpleMethod by
    loom_solve
```

This will print the theorem statement in the Lean infoview. You can then copy it and prove it as a regular Lean theorem, which will have proper incrementality - Lean won't re-run `loom_solve` when you edit code that comes after it.

**When to use this workaround**: When `loom_solve` takes more than a few seconds and you need to work interactively on the remaining proof goals after `loom_solve`

For more details, see [issue #21](https://github.com/verse-lab/loom/issues/21).

### Common Tactics

**Primary tactics:**

- **`loom_solve`**: The main automated tactic for Velvet verification. Handles goal introduction, unfolding Loom constructs, and discharging goals using the configured solver (default: grind). Always use this as the first tactic in `prove_correct` blocks.
- **`loom_solve!`**: Same as `loom_solve` but highlights places where automation failed. Useful for debugging, but use `loom_solve` for final proofs
- **`grind`**: Lean's powerful general-purpose tactic. This is the default solver backend used by `loom_solve`. Can also be used manually for remaining goals after `loom_solve`

**SMT solver tactics (for remaining goals after `loom_solve`):**

- **`loom_auto`**: Wrapper around `loom_smt` that automatically uses lemmas marked with `attribute [solverHint]`. Use this for remaining goals when you have solver hints defined.
- **`loom_smt`**: Direct SMT solver tactic (Z3/CVC5). Can be called with explicit hints: `loom_smt [Lemma1, Lemma2]`. The solvers are auto-installed when the project is built.

**Interactive tactics:**

- **`unfold <method_name>`**: Unfolds the definition of a method
- **`simp_all`**: Simplifies all hypotheses and the goal
- **`omega`**: Solves linear arithmetic goals
- **`aesop`**: Tableau-based proof search tactic

**Advanced tactics:**

- **`loom_solver`**: Internal tactic used by `loom_solve`. Automatically configured based on `set_option loom.solver`. Users typically don't call this directly
- **`loom_goals_intro`**: Introduces raw goals for manual inspection
- **`loom_unfold`**: Unfolds `WithName` constructs after `loom_goals_intro`

### Solver Hints

When solvers fail due to missing mathematical knowledge, provide hints using attributes or explicit arguments.

#### Using `attribute [grind]` (For Grind Solver - Default)

Mark helper lemmas to make them available during grind's proof search:

```lean
def SumDigits (n: Nat): Nat :=
  if n = 0 then 0
  else (n % 10) + SumDigits (n / 10)

lemma SumDigits_unfold (n : Nat) (h : n > 0) :
  SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  have h' : n ≠ 0 := Nat.ne_of_gt h
  simp [h']

lemma SumDigits_zero : SumDigits 0 = 0 := by
  unfold SumDigits
  simp

attribute [grind] Nat.mod_add_div SumDigits_unfold SumDigits_zero

method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
    do
    let mut sum := 0
    let mut n := number
    while n > 0
        invariant sum + SumDigits n = SumDigits number
        invariant 0 ≤ sum
        done_with n = 0
    do
        let digit := n % 10
        sum := sum + digit
        n := n / 10
    return sum

prove_correct SumOfDigits by
  loom_solve
```

#### Using hints with SMT Solvers

**Option 1: Using `attribute [solverHint]` with `loom_auto`**

Mark lemmas with `solverHint` and use `loom_auto` (which automatically collects these hints):

```lean
attribute [solverHint] Nat.mod_lt

prove_correct LastDigit by
  loom_solve       -- Uses configured solver (e.g., grind)
  loom_auto        -- Uses SMT with solverHint lemmas
```

Or configure SMT as the default solver:

```lean
set_option loom.solver "cvc5"

attribute [solverHint] Nat.mod_lt

prove_correct LastDigit by
  loom_solve       -- Uses SMT via loom_auto (which uses solverHints)
```

**Option 2: Passing hints explicitly to `loom_smt`**

Pass lemmas directly to `loom_smt`:

```lean
prove_correct LastDigit by
  loom_solve                      -- Uses configured solver
  loom_smt [Nat.mod_lt, Nat.div_le_iff_le_mul_right]   -- Explicit hints
```

### Interactive Proof Strategies

When `loom_solve` can't complete the proof automatically, combine automated and interactive tactics:

**Pattern 1: Fallback to interactive tactics**
```lean
prove_correct MethodName by
  loom_solve
  -- Automation failed on remaining goals, use interactive tactics
  grind
```

**Pattern 2: Manual proof after automation**
```lean
prove_correct MethodName by
  loom_solve <;> simp_all
  -- Handle remaining subgoals manually
  { intros k hk
    by_cases h : k = i <;> simp_all }
```

**Pattern 3: Helper lemmas**
```lean
-- Define helper lemma
lemma adjacent_to_global_sorted (a : Array Int) :
    (∀ k, 0 ≤ k ∧ k < a.size - 1 → a[k]! ≤ a[k+1]!) →
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!) := by
  intro h_adjacent i j h_bounds
  -- proof here...

-- Mark for grind solver (default)
attribute [grind] adjacent_to_global_sorted

prove_correct IsSorted by
  loom_solve
```

**Pattern 4: Switching solvers for specific problems**
```lean
-- If grind struggles with arithmetic, try SMT
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 4

attribute [solverHint] Nat.mod_lt Nat.div_le_iff_le_mul_right

prove_correct ArithmeticMethod by
  loom_solve
```

**Interactive Mode Features:**

To assist the user in interactive mode, Velvet supports:
- **Convenient naming** for hypotheses produced by `invariant`/`ensures`/`require`
- **Incremental mode** (that is, automation won't rerun on each proof change)

To ensure that incremental mode works as expected, we suggest using `{ subgoal_proof }` pattern in manual proofs:

```lean
prove_correct MethodName by
  loom_solve
  -- Manual proof for remaining subgoals
  { intros k hk
    by_cases h : k = i <;> simp_all }
  { -- Another subgoal
    omega }
```

### Debugging Failed Proofs

**Use `loom_solve!` to see what failed:**
```lean
prove_correct MethodName by
  loom_solve!  -- Highlights failing ensures/invariants/requires
```

**Check specific goals:**
```lean
prove_correct MethodName by
  loom_goals_intro  -- See raw goals
  sorry  -- Temporarily skip to see what goals remain
```

**Incremental development:**
- Start with simple invariants, verify they work
- Add complexity gradually
- Test with property-based testing before formal verification

## 6. Testing

### Executing Methods

Velvet methods are executable Lean definitions:

```lean
method Add (x: Int) (y: Int) return (sum: Int)
    ensures sum = x + y
    do
    return x + y

#eval (Add 5 7).run
-- Output: DivM.res 12
```

### Property-Based Testing with Plausible

Test methods against random inputs before formal verification:

```lean
import CaseStudies.TestingUtil

-- Extract executable version
extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort
derive_tester_for insertionSort

-- Run property-based tests
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break
```

**Decidability proof patterns:**

**Auto-solved (recommended):** By default, `prove_precondition_decidable_for` and `prove_postcondition_decidable_for` will apply some heuristics to synthesize the `Decidable` instances for the pre- and postconditions. If the synthesis fails for some instances, then the commands will leave them as proof goals for users. Note that to facilitate the heuristics, the definitions appearing in the pre- or postconditions should be marked with the `loomAbstractionSimp` attribute. 
```lean
prove_precondition_decidable_for Method
prove_postcondition_decidable_for Method
```

**Manual proving:** If there is a single goal left, for example, in the shape of `Decidable (p ↔ q)`:
```lean
prove_postcondition_decidable_for Method by (
  simp_all
  exact instDecidableIff
)
```

If there are multiple goals left:
```lean
prove_postcondition_decidable_for Method by 
  { /- manual proof for the first -/ }
  { /- manual proof for the second -/ }
  /- ... -/
```

**Benefits:**
- Early bug detection before formal verification
- Concrete counterexamples when postconditions fail
- Validates specifications match intended behavior
- Builds confidence before investing time in proofs

## 7. Advanced Topics

### Pattern Matching and Recursion

#### Pattern Matching

```lean
method ProcessOption (x: Option Nat) return (res: Nat)
  ensures res > 0
  do
    match x with
    | some val =>
      pure (val + 1)
    | none =>
      pure 1
```

**Multiple parameter matching:**
```lean
method ListLength (n : β) (l : List α) return (res : Nat)
  ensures res = l.length
  do
    match l, n with
    | [], _ => pure 0
    | _ :: k, _ =>
      let b ← ListLength n k
      pure b.succ
```

#### Recursion

**Simple recursion:**
```lean
method Factorial (n: Nat) return (res: Nat)
  ensures res > 0
  do
    if n = 0 then
      return 1
    else
      let prev ← Factorial (n - 1)
      return n * prev

prove_correct Factorial by
  loom_solve
```

**Termination measures:**

For non-obvious termination, provide explicit measures:

```lean
method GCD (a : Nat) (b : Nat) return (res : Nat)
  require a > 0
  ensures res > 0
  do
    if b = 0 then
      return a
    else
      let remainder := a % b
      let result ← GCD b remainder
      return result
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    grind

attribute [solverHint] Nat.mod_lt

prove_correct GCD
termination_by b
decreasing_by all_goals(
  apply Nat.mod_lt
  grind
  )
by
  loom_solve
```

### Total vs Partial Correctness

**Partial correctness** (default): Proves that *if* the method terminates, it satisfies the postconditions.

**Total correctness**: Proves both termination *and* correctness.

**For recursive methods:**
```lean
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method FactorialTotal (n: Nat) return (res: Nat)
  ensures res > 0
  do
    if n = 0 then
      return 1
    else
      let prev ← FactorialTotal (n - 1)
      return n * prev
  termination_by n
  decreasing_by omega  -- Prove termination measure decreases

set_option loom.solver "cvc5" in
prove_correct FactorialTotal by
  loom_solve
```

**For loops with total correctness:**

Velvet can be used to reason about terminating loops. In this case, each loop should be annotated with a `decreasing <term>` clause, and a goal about the `<term>` being decreased will be generated.

```lean
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method CountDown (n: Nat) return (res: Nat)
  ensures res = 0
  do
    let mut i := n
    while i > 0
      invariant i ≤ n
      decreasing i  -- Termination measure
    do
      i := i - 1
    return i
```

**Separating termination and functional correctness:**

Velvet provides support for proving termination and functional correctness separately by combining `triple`s of different `method`s. For an example on how to prove functional correctness from partial correctness and termination, please refer to `VelvetExample/Total_Partial_example.lean`.

### Custom Data Structures

Define custom structures using Lean's `structure` syntax:

```lean
structure Encoding where
  cnt: Nat
  c: Char
  deriving Inhabited

method EncodeString (str: Array Char) return (res: Array Encoding)
    ensures /* postconditions about encoding */
    do
    -- implementation using Encoding type
    ...
```

### Non-deterministic Operations

Use `:|` syntax for non-deterministic choice:

```lean
method PickGreater (inp: Nat) return (res: Nat)
  ensures res > inp + 10
  do
    let ans :| ans > inp + 200
    return ans

prove_correct PickGreater by
  loom_solve
  exists (inp + 201)
  omega
```

Choose between angelic and demonic non-determinism:
```lean
set_option loom.semantics.choice "demonic"  -- Standard
-- or
set_option loom.semantics.choice "angelic"
```

### Helper Functions and Lemmas

For complex verification, define helper functions and prove lemmas about them:

```lean
def get_cnt_sum (l: List Encoding) :=
  match l with
  | List.nil => 0
  | List.cons x xs => x.cnt + get_cnt_sum xs

lemma get_cnt_sum_append l1 l2:
    get_cnt_sum (l1 ++ l2) = get_cnt_sum l1 + get_cnt_sum l2 := by
  induction l1 with
  | nil => simp; rfl
  | cons e l1' ih =>
    simp [ih]
    grind
```

Use these in specifications:
```lean
method decodeStr' (encoded_str: Array Encoding)
   return (res: Array Char)
   ensures (res.size = get_cnt_sum encoded_str.toList)
```

### Compound Loop Conditions

While loops can have compound conditions that help with termination:

```lean
while i < a.size - 1 ∧ sorted
    invariant 0 ≤ i ∧ i ≤ a.size - 1
    invariant sorted = true → (∀ k, 0 ≤ k ∧ k < i → a[k]! ≤ a[k+1]!)
    invariant sorted = false → ∃ k, 0 ≤ k ∧ k < a.size - 1 ∧ a[k]! > a[k+1]!
    done_with (i = a.size - 1 ∨ sorted = false)
do
    -- loop body
```

### Complex Loop Invariants

For sophisticated algorithms, you may need complex invariants that track multiple properties:

```lean
while j < high
invariant low <= i ∧ i <= j ∧ j <= high
invariant arrayToMultiset arr = arrayToMultiset oldArr
invariant (forall k, low <= k -> k < i -> arr[k]! < pivotVal)
invariant (forall k , i <= k -> k < j -> arr[k]! >= pivotVal)
invariant arr[high]! = oldArr[high]!
do
    -- loop body
```

### Triple-based Reasoning

After `method` declaration, it becomes a regular Lean 4 definition of a monadic computation with the same name and parameters as `method` and with return type `VelvetM`.

You can use it as a Lean definition if needed, for example, to run it with `#eval`.

The `prove_correct` command creates a Lean 4 statement about the related `method`, which has the form of:

```lean
method MethodName (...) return (...)
  requires ...
  ensures ...
  do ...

prove_correct MethodName by ...

-- Creates: lemma MethodName_correct : triple preconditions (MethodName args) postconditions

#print MethodName_correct  -- Inspect the generated triple
```

It can be further used as a Lean 4 definition if needed.

This allows layered proofs and compositional reasoning. For an example on how to do 2 layer proofs using `triple`s produced by Velvet, please refer to `VelvetExamples/SpMSpV_Example.lean`.

Velvet provides support for proving termination and functional correctness separately by combining `triple`s of different `method`s. For an example on how to prove functional correctness from partial correctness and termination, please refer to `VelvetExample/Total_Partial_example.lean`.

## 8. Reference

### Differences from Dafny

While Velvet's syntax is inspired by Dafny, there are several key differences:

| Feature             | Dafny                               | Velvet                                        |
| ------------------- | ----------------------------------- | --------------------------------------------- |
| **Method Body**     | `{ ... }`                           | `do` block                                    |
| **Variable Decl.**  | `var x := 0;`                       | `let mut x := 0`                              |
| **Mutable Param**   | Implicitly mutable                  | `mut` keyword: `(mut arr: Array Int)`         |
| **Old Values**      | `old(var)`                          | `varOld` (e.g., `arrOld`)                     |
| **Loops**           | `for`, `while`                      | `while` (no `for` loop construct)             |
| **Array Type**      | `array<int>`                        | `Array Int`                                   |
| **Array Creation**  | `new int[size]`                     | `Array.replicate size defaultValue`           |
| **Array Access**    | `a[i]`                              | `a[i]!` (Note the `!`)                        |
| **Array Update**    | `a[i] := value;`                    | `a := Array.set! a i value`                   |
| **Loop Post-cond.** | `ensures` on `while` (less common)  | `done_with` clause for `while`                |
| **Loop Control**    | `break`, `continue`, `return`       | `break`, `continue`, `return` (all supported) |
| **Boolean Equivalence** | `<==>`                         | `↔`                                           |
| **Logical And/Or**  | `&&`, `\|\|`                        | `∧`, `∨`                                      |
| **Existential**     | `exists`                            | `∃`                                           |
| **Universal**       | `forall`                            | `∀`                                           |

#### Example: `for` loop translation

**Dafny:**
```dafny
for i := 0 to a.Length {
    // loop body
}
```

**Velvet:**
```lean
let mut i := 0
while i < a.size do
    -- loop body
    i := i + 1
```

#### Example: Mutable parameters and old values

**Dafny:**
```dafny
method Increment(a: array<int>, index: int)
    requires 0 <= index < a.Length
    ensures a[index] == old(a[index]) + 1
    modifies a
{
    a[index] := a[index] + 1;
}
```

**Velvet:**
```lean
method Increment (mut a: Array Int) (index: Nat) return (u: Unit)
    require index < a.size
    ensures a[index]! = aOld[index]! + 1
    do
    a := a.set! index (a[index]! + 1)
    return
```

### Complete Porting Examples

#### Example 1: Simple Arithmetic Method

**Original Dafny (task_id_435):**
```dafny
method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
    d := n % 10;
}
```

**Velvet Translation:**
```lean
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method LastDigit (n: Nat) return (d: Nat)
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10

attribute [grind] Nat.mod_lt

prove_correct LastDigit by
  loom_solve
```

**Key insights:**
- Used `Nat` instead of `Int` to eliminate non-negativity precondition
- Added `Nat.mod_lt` hint for grind solver
- Direct return statement instead of assignment

#### Example 2: Array Processing with Loop

**Original Dafny (task_id_447):**
```dafny
method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures cubed.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{
    var cubedArray := new int[a.Length];
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant cubedArray.Length == a.Length
        invariant forall k :: 0 <= k < i ==> cubedArray[k] == a[k] * a[k] * a[k]
    {
        cubedArray[i] := a[i] * a[i] * a[i];
    }
    return cubedArray;
}
```

**Velvet Translation:**
```lean
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method CubeElements (a: Array Int) return (cubed: Array Int)
    ensures cubed.size = a.size
    ensures ∀ i, 0 ≤ i ∧ i < a.size → cubed[i]! = a[i]! * a[i]! * a[i]!
    do
    let mut cubedArray := Array.replicate a.size 0
    let mut i := 0
    while i < a.size
    invariant cubedArray.size = a.size
    invariant 0 ≤ i ∧ i ≤ a.size
    invariant ∀ k, 0 ≤ k ∧ k < i → cubedArray[k]! = a[k]! * a[k]! * a[k]!
    do
        cubedArray := cubedArray.set! i (a[i]! * a[i]! * a[i]!)
        i := i + 1
    return cubedArray

attribute [grind] Array.size_replicate Array.size_set

prove_correct CubeElements by
  loom_solve <;> simp_all
  -- Additional interactive proving for complex array reasoning
```

**Key insights:**
- `for` loop became `while` loop with manual increment
- Array creation uses `Array.replicate` with default value
- Array update uses `Array.set!` with reassignment
- Added array size hints for grind solver
- Used both automated and interactive proving strategies

### Common Porting Patterns

When porting from Dafny to Velvet, several patterns emerge frequently.

#### Type Translations

**Integer types**: Dafny's `int` typically becomes `Int` in Velvet, but consider using `Nat` for non-negative values to get better solver support:

```lean
-- Dafny: method LastDigit(n: int) requires n >= 0
-- Velvet: better to use Nat directly
method LastDigit (n: Nat) return (d: Nat)
```

**Precondition simplification**: When using `Nat`, non-negativity constraints become unnecessary:
```lean
-- Dafny: requires n >= 0 && size > 0
-- Velvet: just require size > 0 (if n is Nat)
```

#### Loop Invariant Translation

**Basic pattern**: Maintain the logical structure but adapt to Velvet syntax:
```lean
-- Dafny:
-- invariant 0 <= i <= a.Length
-- invariant forall k :: 0 <= k < i ==> result[k] == transform(a[k])

-- Velvet:
invariant 0 ≤ i ∧ i ≤ a.size
invariant ∀ k, 0 ≤ k ∧ k < i → result[k]! = transform a[k]!
```

**Array size invariants**: Always include size preservation invariants:
```lean
invariant result.size = a.size  -- often needed for verification
```

### Best Practices

1. **Start simple**: Port basic structure first, then add complexity
2. **Use `Nat` over `Int`**: When values are non-negative, use `Nat` to eliminate preconditions
3. **Test before verification**: Use property-based testing to catch bugs early
4. **Incremental invariants**: Start with simple invariants, add complexity gradually
5. **Helper lemmas**: Break down complex properties into smaller, provable lemmas
6. **Choose the right solver**: Use grind by default, switch to SMT for arithmetic-heavy code
7. **Increase resources as needed**: Use `maxHeartbeats` and `splits` for complex proofs

## 9. Troubleshooting

### Common Verification Challenges

**Issue**: Solver cannot handle modular arithmetic
**Solution**: Add `Nat.mod_lt` as a hint:
- For grind: `attribute [grind] Nat.mod_lt`
- For SMT: `attribute [solverHint] Nat.mod_lt`

**Issue**: Array size properties not automatically proven
**Solution**: Add explicit size invariants and use hints:
```lean
attribute [grind] Array.size_replicate Array.size_set
```

**Issue**: Complex logical equivalences in specifications
**Solution**: Break down into helper lemmas and prove them separately

**Issue**: Grind solver times out or runs out of splits
**Solution**: Increase splits:
```lean
set_option loom.solver.grind.splits 40
```
Or switch to SMT solver:
```lean
set_option loom.solver "cvc5"
```

**Issue**: Proof times out with "maximum heartbeats exceeded"
**Solution**: Increase heartbeat limit:
```lean
set_option maxHeartbeats 1000000
```

**Issue**: `loom_solve` fails with no clear reason
**Solution**: Use `loom_solve!` to highlight failing parts, or use `loom_goals_intro` to inspect raw goals

### Getting Help

- Check examples in `CaseStudies/Velvet/VelvetExamples/`
- Use `#print` to inspect generated definitions and triples
- Start with simpler specifications and build up
- Test with concrete inputs using `#eval` before verification
