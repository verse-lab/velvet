import CaseStudies.Velvet.Std
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    cubeSurfaceArea: compute the surface area of a cube from its edge length.

    Natural language breakdown:
    1. The input is a natural number `size`, the length of an edge of a cube.
    2. The surface area of a cube equals 6 times the area of one face.
    3. Each face is a square with area `size ^ 2`.
    4. Therefore, the surface area equals `6 * (size ^ 2)`.
    5. The output is a natural number.
    6. There are no rejected inputs.
-/

section Impl
method cubeSurfaceArea (size : Nat) return (result : Nat)
  ensures result = 6 * (size ^ 2)
  do
    let area := 6 * (size ^ 2)
    return area
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct cubeSurfaceArea by
  loom_solve_async
end Proof
