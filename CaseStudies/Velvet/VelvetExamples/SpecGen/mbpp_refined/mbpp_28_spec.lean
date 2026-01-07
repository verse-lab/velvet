import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 28: Compute the binomial coefficient C(n, k)
--
-- Natural language breakdown:
-- 1. The binomial coefficient C(n, k) represents the number of ways to choose k items from n items
-- 2. It is defined as C(n, k) = n! / (k! * (n-k)!)
-- 3. The binomial coefficient only makes sense when 0 ≤ k ≤ n
-- 4. Key mathematical properties:
--    a. C(n, 0) = 1 (there's exactly one way to choose nothing)
--    b. C(n, n) = 1 (there's exactly one way to choose everything)
--    c. C(n, 1) = n (there are n ways to choose one item)
--    d. C(n, n-1) = n (choosing n-1 items is equivalent to leaving out 1 item)
--    e. Symmetry: C(n, k) = C(n, n-k)
--    f. Pascal's identity: C(n, k) = C(n-1, k-1) + C(n-1, k) for 0 < k < n
-- 5. The result is always a positive natural number (at least 1 when the input is valid)
-- 6. The binomial coefficient can grow very large (exponentially with n)
--
-- Property-oriented specification approach:
-- Rather than specifying how to compute C(n, k), we define what C(n, k) IS:
-- C(n, k) is the unique natural number that equals n! / (k! * (n-k)!)

-- Helper function to compute factorial

specdef BinomialCoefficientSpec

-- Helper Functions

register_specdef_allow_recursion

def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => (n' + 1) * factorial n'

-- Helper definition for binomial coefficient
-- This is the mathematical definition: C(n, k) = n! / (k! * (n-k)!)
def binomialCoeff (n: Nat) (k: Nat) : Nat :=
  if k > n then 0
  else factorial n / (factorial k * factorial (n - k))

def require1 (n : Nat) (k : Nat) :=
  k ≤ n  -- k cannot exceed n

-- Postcondition clauses
def ensures1 (n : Nat) (k : Nat) (result : Nat) :=
  result = binomialCoeff n k  -- The result equals the binomial coefficient

def_pre (n : Nat) (k : Nat) :=
  require1 n k
def_post (n : Nat) (k : Nat) (result : Nat) :=
  ensures1 n k result

specend BinomialCoefficientSpec

method BinomialCoefficient (n: Nat) (k: Nat)
  return (result: Nat)
  require BinomialCoefficientSpec.pre n k
  ensures BinomialCoefficientSpec.post n k result
  do
    sorry

prove_correct BinomialCoefficient by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: From problem description
def test0_n : Nat := 5
def test0_k : Nat := 2
def test0_Expected : Nat := 10

-- Test case 1: Edge case - C(n, 0)
def test1_n : Nat := 10
def test1_k : Nat := 0
def test1_Expected : Nat := 1

-- Test case 2: Edge case - C(n, n)
def test2_n : Nat := 7
def test2_k : Nat := 7
def test2_Expected : Nat := 1

-- Test case 3: Edge case - C(n, 1)
def test3_n : Nat := 8
def test3_k : Nat := 1
def test3_Expected : Nat := 8

-- Test case 4: Symmetry test - C(6, 2)
def test4_n : Nat := 6
def test4_k : Nat := 2
def test4_Expected : Nat := 15

-- Test case 5: Complement of test case 4 - C(6, 4)
def test5_n : Nat := 6
def test5_k : Nat := 4
def test5_Expected : Nat := 15

-- Test case 6: Small values - C(4, 2)
def test6_n : Nat := 4
def test6_k : Nat := 2
def test6_Expected : Nat := 6

-- Test case 7: C(n, n-1)
def test7_n : Nat := 9
def test7_k : Nat := 8
def test7_Expected : Nat := 9

-- Test case 8: Moderate values - C(10, 3)
def test8_n : Nat := 10
def test8_k : Nat := 3
def test8_Expected : Nat := 120

-- Test case 9: Moderate values - C(10, 5)
def test9_n : Nat := 10
def test9_k : Nat := 5
def test9_Expected : Nat := 252

-- Test case 10: Larger values - C(12, 4)
def test10_n : Nat := 12
def test10_k : Nat := 4
def test10_Expected : Nat := 495

-- Test case 11: Larger values - C(15, 7)
def test11_n : Nat := 15
def test11_k : Nat := 7
def test11_Expected : Nat := 6435

-- Test case 12: Edge case with small n - C(3, 1)
def test12_n : Nat := 3
def test12_k : Nat := 1
def test12_Expected : Nat := 3

-- Test case 13: Larger n with small k - C(20, 2)
def test13_n : Nat := 20
def test13_k : Nat := 2
def test13_Expected : Nat := 190

-- Test case 14: Large values - C(20, 10)
def test14_n : Nat := 20
def test14_k : Nat := 10
def test14_Expected : Nat := 184756

-- Recommend to validate: 0, 1, 2, 3, 9, 14

end TestCases
