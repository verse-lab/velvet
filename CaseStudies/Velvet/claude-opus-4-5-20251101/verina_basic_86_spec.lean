import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    rotate: Rotate an array of integers to the left by a specified offset
    Natural language breakdown:
    1. We are given an array of integers and a non-negative offset
    2. Left rotation means elements move to lower indices, with elements that "fall off" the left end wrapping around to the right
    3. The result array has the same length as the input array
    4. For every valid index i in the result, result[i] = input[(i + offset) mod n], where n is the array size
    5. If the array is empty, return an empty array regardless of offset
    6. The offset may be larger than the array size, in which case modular arithmetic handles the wrap-around
    7. Example: [1, 2, 3, 4, 5] with offset 2 becomes [3, 4, 5, 1, 2]
       - result[0] = input[(0 + 2) mod 5] = input[2] = 3
       - result[1] = input[(1 + 2) mod 5] = input[3] = 4
       - result[2] = input[(2 + 2) mod 5] = input[4] = 5
       - result[3] = input[(3 + 2) mod 5] = input[0] = 1
       - result[4] = input[(4 + 2) mod 5] = input[1] = 2
-/

section Specs

-- Precondition: offset must be non-negative
def precondition (a : Array Int) (offset : Int) :=
  offset ≥ 0

-- Postcondition: result has same size and elements are rotated according to modular index formula
def postcondition (a : Array Int) (offset : Int) (result : Array Int) :=
  result.size = a.size ∧
  (∀ i : Nat, i < result.size →
    result[i]! = a[(i + offset.toNat) % a.size]!)

end Specs

section Impl

method rotate (a : Array Int) (offset : Int)
  return (result : Array Int)
  require precondition a offset
  ensures postcondition a offset result
  do
  pure #[]

end Impl

section TestCases

-- Test case 1: Basic rotation by 2 (example from problem)
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_offset : Int := 2
def test1_Expected : Array Int := #[3, 4, 5, 1, 2]

-- Test case 2: Rotation by 1
def test2_a : Array Int := #[10, 20, 30, 40]
def test2_offset : Int := 1
def test2_Expected : Array Int := #[20, 30, 40, 10]

-- Test case 3: Empty array
def test3_a : Array Int := #[]
def test3_offset : Int := 5
def test3_Expected : Array Int := #[]

-- Test case 4: Single element with zero offset
def test4_a : Array Int := #[7]
def test4_offset : Int := 0
def test4_Expected : Array Int := #[7]

-- Test case 5: Negative numbers with offset 3
def test5_a : Array Int := #[-1, -2, -3, -4]
def test5_offset : Int := 3
def test5_Expected : Array Int := #[-4, -1, -2, -3]

-- Test case 6: Offset larger than array size (5 mod 3 = 2)
def test6_a : Array Int := #[5, 10, 15]
def test6_offset : Int := 5
def test6_Expected : Array Int := #[15, 5, 10]

-- Test case 7: Zero offset (no rotation)
def test7_a : Array Int := #[1, 2, 3, 4]
def test7_offset : Int := 0
def test7_Expected : Array Int := #[1, 2, 3, 4]

-- Test case 8: Offset equal to array size (full rotation, same as original)
def test8_a : Array Int := #[1, 2, 3]
def test8_offset : Int := 3
def test8_Expected : Array Int := #[1, 2, 3]

-- Test case 9: Single element with non-zero offset
def test9_a : Array Int := #[42]
def test9_offset : Int := 10
def test9_Expected : Array Int := #[42]

-- Test case 10: Two elements with offset 1
def test10_a : Array Int := #[100, 200]
def test10_offset : Int := 1
def test10_Expected : Array Int := #[200, 100]

-- Recommend to validate: 1, 2, 5

end TestCases
