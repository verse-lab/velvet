import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

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

section Specs

-- No helper definitions are required beyond standard Nat arithmetic and exponentiation.

def precondition (size : Nat) : Prop :=
  True

def postcondition (size : Nat) (result : Nat) : Prop :=
  result = 6 * (size ^ 2)

end Specs

section Impl

method cubeSurfaceArea (size : Nat) return (result : Nat)
  require precondition size
  ensures postcondition size result
  do
    pure (6 * (size ^ 2))

end Impl

section TestCases

-- Test case 1: example from prompt: size = 3
-- Surface area = 6 * 3^2 = 54

def test1_size : Nat := 3
def test1_Expected : Nat := 54

-- Test case 2: size = 1

def test2_size : Nat := 1
def test2_Expected : Nat := 6

-- Test case 3: size = 10

def test3_size : Nat := 10
def test3_Expected : Nat := 600

-- Test case 4: size = 5

def test4_size : Nat := 5
def test4_Expected : Nat := 150

-- Test case 5: size = 2

def test5_size : Nat := 2
def test5_Expected : Nat := 24

-- Test case 6: edge case size = 0

def test6_size : Nat := 0
def test6_Expected : Nat := 0

-- Test case 7: another typical value

def test7_size : Nat := 7
def test7_Expected : Nat := 294

-- Test case 8: another value to cover arithmetic

def test8_size : Nat := 4
def test8_Expected : Nat := 96

-- Recommend to validate: test1, test2, test6

end TestCases
