# SpecDSL Documentation

## Overview

SpecDSL is a domain-specific language for defining formal specifications in Lean 4. It provides a structured way to define preconditions and postconditions for functions, with automatic validation and safety checks to ensure specification quality.

## Core Features

### 1. Specification Sections

SpecDSL uses standard Lean sections named `Specs` to encapsulate preconditions, postconditions, and helper definitions:

```lean
section Specs
  -- definitions go here
end Specs
```

### 2. Precondition and Postcondition Definitions

Within a `Specs` section, you define:

- **`def precondition`**: Precondition with input parameters
- **`def postcondition`**: Postcondition with input parameters plus return value parameter

```lean
section Specs
  def precondition (n : Nat) : Prop := n > 0
  def postcondition (n : Nat) (result : Nat) : Prop := result >= n
end Specs
```

The precondition and postcondition functions can be referenced as `precondition` and `postcondition` within their scope.

### 3. Automatic Safety Checks

SpecDSL enforces several safety constraints within `Specs` sections:

**Prohibited constructs:**
- `sorry` (incomplete proofs)
- `admitted` (incomplete tactics)
- `axiom` declarations
- `let rec` (recursive let bindings, by default)
- Recursive function definitions (by default)
- User-registered forbidden functions

**Required constraints:**
- Both `def precondition` and `def postcondition` must be defined
- `postcondition` parameters must extend `precondition` parameters with an additional return value parameter
- First N parameters of `postcondition` must match `precondition` parameters (where N = number of `precondition` parameters)

### 4. Automatic Attributes

All definitions within a `Specs` section automatically receive the `@[loomAbstractionSimp]` attribute for integration with the Loom verification framework.

## Configuration

### Allowing Recursion

By default, recursion is forbidden in `Specs` sections. To allow recursion:

```lean
register_specdef_allow_recursion
```

This disables the recursion checking mechanism.

### Registering Forbidden Functions

You can register specific functions that should not be used in specifications:

```lean
register_specdef_forbidden List.filter
```

This prevents `List.filter` from being used in any `Specs` section definitions.

## Examples

### Example 1: Basic Specification (from test1.lean)

```lean
section Specs
  def precondition (n : Nat) : Prop := n > 0
  def postcondition (n : Nat) (result : Nat) : Prop := result >= n

  def increment (n : Nat) : Nat := n + 1
end Specs

-- Usage
#check precondition      -- (n : Nat) : Prop
#check postcondition     -- (n : Nat) (result : Nat) : Prop
#check increment         -- (n : Nat) : Nat
```

### Example 2: Multiple Parameters

```lean
section Specs
  def precondition (x : Nat) (y : Nat) : Prop := x > 0 ∧ y > 0
  def postcondition (x : Nat) (y : Nat) (result : Nat) : Prop := result = x + y

  def add (x y : Nat) : Nat := x + y
end Specs
```

### Example 3: Complex Specification with Helpers

```lean
section Specs
  -- Helper definitions
  def isValidPath (path: List (Nat × Nat)) (startRow startCol endRow endCol: Nat) : Prop :=
    path.length > 0 ∧
    path.head? = some (startRow, startCol) ∧
    path.getLast? = some (endRow, endCol) ∧
    ∀ i, i + 1 < path.length →
      let curr := path[i]!
      let next := path[i + 1]!
      (next.1 = curr.1 ∧ next.2 = curr.2 + 1) ∨      -- right move
      (next.1 = curr.1 + 1 ∧ next.2 = curr.2) ∨      -- down move
      (next.1 = curr.1 + 1 ∧ next.2 = curr.2 + 1)    -- diagonal move

  def pathCost (cost: Array (Array Nat)) (path: List (Nat × Nat)) : Nat :=
    path.foldl (fun acc (i, j) => acc + (cost[i]!)[j]!) 0

  -- Precondition: cost matrix is valid
  def precondition (cost: Array (Array Nat)) (m: Nat) (n: Nat) : Prop :=
    cost.size > 0 ∧
    (∀ i < cost.size, cost[i]!.size > 0) ∧
    (∀ i < cost.size, cost[i]!.size = cost[0]!.size) ∧
    m < cost.size ∧
    n < cost[0]!.size

  -- Postcondition: result is minimum cost path
  def postcondition (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) : Prop :=
    (∃ path, isValidPath path 0 0 m n ∧ pathCost cost path = minCost) ∧
    (∀ path, isValidPath path 0 0 m n → pathCost cost path ≥ minCost) ∧
    ((m = 0 ∧ n = 0) → minCost = (cost[0]!)[0]!)
end Specs

-- Usage with Loom method
method MinCostPath (cost: Array (Array Nat)) (m: Nat) (n: Nat)
  return (minCost: Nat)
  require precondition cost m n
  ensures postcondition cost m n minCost
  do
    pure 0  -- implementation
```

## Error Detection Examples

The following demonstrate errors that SpecDSL will catch:

```lean
-- ERROR: axiom is not allowed in Specs sections
section Specs
  axiom myAxiom : Nat
end Specs

-- ERROR: sorry is not allowed in Specs sections
section Specs
  def precondition (x : Nat) : Prop := x ≤ 1
  def postcondition (x : Nat) (result : Nat) : Prop := sorry  -- Error!
end Specs

-- ERROR: recursive function is not allowed (by default)
section Specs
  def precondition (n : Nat) : Prop := n > 0
  def postcondition (n : Nat) (result : Nat) : Prop := result > n

  def factorial (n : Nat) : Nat :=
    if n = 0 then 1 else n * factorial (n - 1)  -- Error!
end Specs

-- ERROR: let rec is not allowed (by default)
section Specs
  def precondition : Prop := True
  def postcondition (result : Nat) : Prop := result = 0

  def testLetRec : Nat :=
    let rec f (x : Nat) := if x = 0 then 0 else f (x - 1)  -- Error!
    f 10
end Specs

-- ERROR: forbidden function used
register_specdef_forbidden List.filter

section Specs
  def precondition (xs : List Nat) : Prop := True
  def postcondition (xs : List Nat) (result : List Nat) : Prop := True

  def invalidFunction (xs : List Nat) : List Nat :=
    List.filter (· > 0) xs  -- Error: List.filter is forbidden
end Specs

-- ERROR: Specs section must contain both precondition and postcondition
section Specs
  def precondition : Prop := True
  -- Missing postcondition
end Specs  -- Error!
```

## Best Practices

1. **Structure specifications hierarchically**: Define helper functions and predicates before using them in `precondition` and `postcondition`.

2. **Keep preconditions minimal**: Include only essential requirements for the function to execute correctly.

3. **Make postconditions complete**: Fully specify the expected behavior, including edge cases.

4. **Use descriptive names**: Name helper functions clearly to improve specification readability.

5. **Break down complex conditions**: Use helper definitions to make complex preconditions and postconditions more modular and readable.

## Integration with Loom

SpecDSL is designed to work seamlessly with the Loom verification framework:

- All definitions automatically receive `@[loomAbstractionSimp]` attribute
- Specifications can be directly used in `method` declarations with `require` and `ensures` clauses
- The `prove_correct` tactic can verify implementations against specifications

## Implementation Details

### Environment Extensions

SpecDSL uses Lean's environment extension system to track:

- **`forbiddenFunctions`**: List of forbidden function names
- **`forbidRecursion`**: Whether recursion checking is enabled (default: `true`)
- **`specsSect`**: Boolean flag indicating whether we're in a Specs section
- **`prePostState`**: Current section's precondition/postcondition information

### Syntax Interception

SpecDSL intercepts:
1. **`section` commands**: Detects when a section named `Specs` is opened and activates safety checks
2. **`end` commands**: Validates that both `precondition` and `postcondition` were defined before closing a `Specs` section
3. **All declarations within `Specs` sections** to:
   - Validate against safety constraints
   - Check for forbidden constructs
   - Apply automatic attributes
   - Enforce parameter consistency between `precondition` and `postcondition`
   - Handle special processing for `def precondition` and `def postcondition`
