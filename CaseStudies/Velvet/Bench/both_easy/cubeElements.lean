import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    cubeElements: Replace every element of an integer array with its cube.
    Natural language breakdown:
    1. Input is an array of integers (possibly empty).
    2. Output is an array of integers with the same size as the input.
    3. For each valid index i, the output element at i equals the cube of the input element at i.
    4. Cubing means multiplying the element by itself three times: x * x * x.
    5. There are no additional preconditions; the function must work for any array.
-/

-- Helper: integer cube
-- We use direct multiplication to avoid needing extra exponentiation imports.
def intCube (x : Int) : Int := x * x * x


section Impl
method cubeElements (a : Array Int)
  return (result : Array Int)
  ensures result.size = a.size
  ensures ∀ (i : Nat), i < a.size → result[i]! = intCube (a[i]!)
  do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size
    -- Invariant 1: index i stays within bounds, enabling safe reads/writes and proving termination at exit.
    -- Init: i=0. Preserved: i increments by 1 while condition ensures i<a.size. Exit: i=a.size.
    invariant "i_bounds" (i ≤ a.size)
    -- Invariant 2: result array size is unchanged and matches input size.
    -- Init: replicate has size a.size. Preserved: set! preserves size. Needed for postcondition.
    invariant "size_preserved" (result.size = a.size)
    -- Invariant 3: all positions already processed (< i) satisfy the cube relation.
    -- Init: vacuously true at i=0. Preserved: body sets index i correctly and doesn't change earlier indices.
    -- Exit with i=a.size gives the full pointwise postcondition.
    invariant "prefix_cubed" (∀ (k : Nat), k < i → result[k]! = intCube (a[k]!))
  do
    let x := a[i]!
    result := result.set! i (intCube x)
    i := i + 1
  return result
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct cubeElements by
  loom_solve
end Proof
