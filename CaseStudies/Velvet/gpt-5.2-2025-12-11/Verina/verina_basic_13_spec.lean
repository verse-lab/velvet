import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

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

section Specs

-- Helper: integer cube
-- We use direct multiplication to avoid needing extra exponentiation imports.
def intCube (x : Int) : Int := x * x * x

def precondition (a : Array Int) : Prop :=
  True

-- Postcondition: size preserved and pointwise cube relation.
-- Using Nat indices with a[i]! as recommended.
def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = intCube (a[i]!))

end Specs

section Impl

method cubeElements (a : Array Int)
  return (result : Array Int)
  require precondition a
  ensures postcondition a result
  do
  pure #[]  -- placeholder

end Impl

section TestCases

-- Test case 1: example given in the prompt

def test1_a : Array Int := #[1, 2, 3, 4]
def test1_Expected : Array Int := #[1, 8, 27, 64]

-- Test case 2: includes zero and negative values

def test2_a : Array Int := #[0, -1, -2, 3]
def test2_Expected : Array Int := #[0, -1, -8, 27]

-- Test case 3: empty array

def test3_a : Array Int := #[]
def test3_Expected : Array Int := #[]

-- Test case 4: singleton positive

def test4_a : Array Int := #[5]
def test4_Expected : Array Int := #[125]

-- Test case 5: repeated negative values

def test5_a : Array Int := #[-3, -3]
def test5_Expected : Array Int := #[-27, -27]

-- Test case 6: mixture with sign variety

def test6_a : Array Int := #[-10, 1, 2]
def test6_Expected : Array Int := #[-1000, 1, 8]

-- Test case 7: all zeros

def test7_a : Array Int := #[0, 0, 0]
def test7_Expected : Array Int := #[0, 0, 0]

-- Test case 8: longer mixed values

def test8_a : Array Int := #[2, -4, 0, 7, -1]
def test8_Expected : Array Int := #[8, -64, 0, 343, -1]

-- Recommend to validate: test1, test2, test3

end TestCases
