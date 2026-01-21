import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    update_map: Merge two maps where the second map's values take precedence for overlapping keys
    
    Natural language breakdown:
    1. We have two input maps m1 and m2, each represented as a list of key-value pairs (Int × Int)
    2. The result should contain all keys from both m1 and m2
    3. For keys that appear only in m1, the value from m1 is used
    4. For keys that appear only in m2, the value from m2 is used
    5. For keys that appear in both maps, the value from m2 takes precedence
    6. No keys outside of m1 or m2 should appear in the result
    7. The result map should have unique keys (no duplicates)
    8. The entries in the result map should be sorted by key
    
    Property-oriented specification:
    - The set of keys in result equals the union of keys in m1 and m2
    - For each key k in result:
      - If k is in m2, then result[k] = m2[k]
      - If k is only in m1 (not in m2), then result[k] = m1[k]
    - The result is sorted by keys
    - The result has no duplicate keys
-/

section Specs

-- Helper function to check if a key exists in a list of pairs
def hasKey (m : List (Int × Int)) (k : Int) : Bool :=
  m.any (fun p => p.1 == k)

-- Helper function to get the value for a key (returns default if not found)
def getValue (m : List (Int × Int)) (k : Int) (default : Int) : Int :=
  match m.find? (fun p => p.1 == k) with
  | some p => p.2
  | none => default

-- Helper to check if a list of pairs is sorted by first element
def isSortedByKey (lst : List (Int × Int)) : Prop :=
  ∀ i : Nat, i + 1 < lst.length → (lst[i]!).1 ≤ (lst[i + 1]!).1

-- Helper to check if keys are unique in a list of pairs
def hasUniqueKeys (lst : List (Int × Int)) : Prop :=
  ∀ i j : Nat, i < lst.length → j < lst.length → i ≠ j → (lst[i]!).1 ≠ (lst[j]!).1

-- Precondition: no specific constraints required
def precondition (m1 : List (Int × Int)) (m2 : List (Int × Int)) :=
  True

-- Postcondition: defines the merge behavior
def postcondition (m1 : List (Int × Int)) (m2 : List (Int × Int)) (result : List (Int × Int)) :=
  -- 1. Every key in result is from m1 or m2
  (∀ k : Int, hasKey result k → hasKey m1 k ∨ hasKey m2 k) ∧
  -- 2. Every key in m1 is in result
  (∀ k : Int, hasKey m1 k → hasKey result k) ∧
  -- 3. Every key in m2 is in result
  (∀ k : Int, hasKey m2 k → hasKey result k) ∧
  -- 4. For keys in m2, result has m2's value
  (∀ k : Int, hasKey m2 k → getValue result k 0 = getValue m2 k 0) ∧
  -- 5. For keys only in m1 (not in m2), result has m1's value
  (∀ k : Int, hasKey m1 k → ¬hasKey m2 k → getValue result k 0 = getValue m1 k 0) ∧
  -- 6. Result is sorted by key
  isSortedByKey result ∧
  -- 7. Result has unique keys
  hasUniqueKeys result

end Specs

section Impl

method update_map (m1 : List (Int × Int)) (m2 : List (Int × Int))
  return (result : List (Int × Int))
  require precondition m1 m2
  ensures postcondition m1 m2 result
  do
  pure []  -- placeholder

end Impl

section TestCases

-- Test case 1: Basic merge with overlapping key (from problem description)
def test1_m1 : List (Int × Int) := [(1, 10), (2, 20)]
def test1_m2 : List (Int × Int) := [(2, 30), (3, 40)]
def test1_Expected : List (Int × Int) := [(1, 10), (2, 30), (3, 40)]

-- Test case 2: Complete overlap - same key in both maps
def test2_m1 : List (Int × Int) := [(1, 100)]
def test2_m2 : List (Int × Int) := [(1, 200)]
def test2_Expected : List (Int × Int) := [(1, 200)]

-- Test case 3: m2 is empty - result should be m1
def test3_m1 : List (Int × Int) := [(5, 50), (6, 60)]
def test3_m2 : List (Int × Int) := []
def test3_Expected : List (Int × Int) := [(5, 50), (6, 60)]

-- Test case 4: m1 is empty - result should be m2
def test4_m1 : List (Int × Int) := []
def test4_m2 : List (Int × Int) := [(7, 70)]
def test4_Expected : List (Int × Int) := [(7, 70)]

-- Test case 5: Multiple overlaps with some unique keys
def test5_m1 : List (Int × Int) := [(1, 1), (2, 2), (3, 3)]
def test5_m2 : List (Int × Int) := [(2, 20), (4, 40)]
def test5_Expected : List (Int × Int) := [(1, 1), (2, 20), (3, 3), (4, 40)]

-- Test case 6: Both maps empty
def test6_m1 : List (Int × Int) := []
def test6_m2 : List (Int × Int) := []
def test6_Expected : List (Int × Int) := []

-- Test case 7: Disjoint keys - no overlap
def test7_m1 : List (Int × Int) := [(1, 10), (3, 30)]
def test7_m2 : List (Int × Int) := [(2, 20), (4, 40)]
def test7_Expected : List (Int × Int) := [(1, 10), (2, 20), (3, 30), (4, 40)]

-- Test case 8: Negative keys
def test8_m1 : List (Int × Int) := [(-2, 200), (-1, 100)]
def test8_m2 : List (Int × Int) := [(-1, 150), (0, 0)]
def test8_Expected : List (Int × Int) := [(-2, 200), (-1, 150), (0, 0)]

-- Test case 9: Single element maps with no overlap
def test9_m1 : List (Int × Int) := [(10, 100)]
def test9_m2 : List (Int × Int) := [(20, 200)]
def test9_Expected : List (Int × Int) := [(10, 100), (20, 200)]

-- Test case 10: Large values
def test10_m1 : List (Int × Int) := [(1, 1000000), (2, 2000000)]
def test10_m2 : List (Int × Int) := [(2, 9999999), (3, 3000000)]
def test10_Expected : List (Int × Int) := [(1, 1000000), (2, 9999999), (3, 3000000)]

-- Recommend to validate: 1, 2, 5

end TestCases
