import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    elementWiseModulo: compute the element-wise modulo (remainder) between two arrays of integers.
    Natural language breakdown:
    1. Inputs are two arrays a and b of integers.
    2. The two arrays must have the same length.
    3. Every element of b must be non-zero so that the modulo operation is defined.
    4. The output is a new array result of integers.
    5. The output has the same length as the input arrays.
    6. For each valid index i, the output element result[i] equals a[i] % b[i].
    7. "Non-null" arrays are implicit in Lean: an Array value always exists, so there is no null case.
-/

section Specs

-- Helper predicate: all entries of an Int array are non-zero.
-- We phrase it pointwise with safe access `b[i]!` guarded by `i < b.size`.
def allNonzero (b : Array Int) : Prop :=
  ∀ (i : Nat), i < b.size → b[i]! ≠ 0

-- Preconditions:
-- 1) Same length
-- 2) No zero divisor in b
-- Note: "non-null" is not meaningful in Lean; arrays are always defined values.
def precondition (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ allNonzero b

-- Postconditions:
-- 1) Result length equals input length.
-- 2) Pointwise remainder property.
def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
    (∀ (i : Nat), i < a.size → result[i]! = a[i]! % b[i]!)

end Specs

section Impl

method elementWiseModulo (a : Array Int) (b : Array Int)
  return (result : Array Int)
  require precondition a b
  ensures postcondition a b result
  do
  pure #[]  -- placeholder body only

end Impl

section TestCases

-- Test case 1: example from prompt
-- a = #[10, 20, 30], b = #[3, 7, 5] => #[1, 6, 0]
def test1_a : Array Int := #[10, 20, 30]
def test1_b : Array Int := #[3, 7, 5]
def test1_Expected : Array Int := #[1, 6, 0]

-- Test case 2: all multiples -> all zeros
-- a = #[100, 200, 300, 400], b = #[10, 20, 30, 50] => #[0, 0, 0, 0]
def test2_a : Array Int := #[100, 200, 300, 400]
def test2_b : Array Int := #[10, 20, 30, 50]
def test2_Expected : Array Int := #[0, 0, 0, 0]

-- Test case 3: negative dividends and a negative divisor (checks Int.mod sign convention)
-- a = #[-10, -20, 30], b = #[3, -7, 5] => #[2, 1, 0]
def test3_a : Array Int := #[-10, -20, 30]
def test3_b : Array Int := #[3, -7, 5]
def test3_Expected : Array Int := #[2, 1, 0]

-- Test case 4: empty arrays (vacuously satisfies nonzero condition)
def test4_a : Array Int := #[]
def test4_b : Array Int := #[]
def test4_Expected : Array Int := #[]

-- Test case 5: single element, positive divisor
def test5_a : Array Int := #[7]
def test5_b : Array Int := #[3]
def test5_Expected : Array Int := #[1]

-- Test case 6: single element, negative divisor
-- Lean's Int.mod uses Euclidean remainder, so 7 % (-3) = 1
def test6_a : Array Int := #[7]
def test6_b : Array Int := #[-3]
def test6_Expected : Array Int := #[1]

-- Test case 7: zeros in dividend (allowed) with non-zero divisors
-- 0 % 2 = 0, 5 % 2 = 1, (-5) % 2 = 1 (Euclidean remainder)
def test7_a : Array Int := #[0, 5, -5]
def test7_b : Array Int := #[2, 2, 2]
def test7_Expected : Array Int := #[0, 1, 1]

-- Test case 8: repeated divisor, various remainders
def test8_a : Array Int := #[17, 18, 19, 20]
def test8_b : Array Int := #[5, 5, 5, 5]
def test8_Expected : Array Int := #[2, 3, 4, 0]

-- Test case 9: sign combinations with positive and negative divisors
-- (-1) % 2 = 1, 1 % 2 = 1, (-1) % (-2) = 1, 1 % (-2) = 1
-- (since Int.mod returns remainder with same sign as the divisor in Lean's Euclidean definition)
def test9_a : Array Int := #[-1, 1, -1, 1]
def test9_b : Array Int := #[2, 2, -2, -2]
def test9_Expected : Array Int := #[1, 1, 1, 1]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test3, test5

end TestCases
