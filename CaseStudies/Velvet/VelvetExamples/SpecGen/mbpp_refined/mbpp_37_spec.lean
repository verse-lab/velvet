import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- MBPP Problem 37: Sort a given mixed list of integers and strings
--
-- Natural language breakdown:
-- 1. We have an input list that contains both integers and strings (heterogeneous)
-- 2. Since Lean/Velvet has a strong type system, we need to model this as a sum type
-- 3. We define a custom inductive type IntOrString that can be either an Int or a String
-- 4. The sorting behavior should be: separate integers from strings, sort each group, then combine
-- 5. Integers should be sorted in ascending order (numerically)
-- 6. Strings should be sorted in lexicographic order (alphabetically)
-- 7. Convention: integers appear before strings in the result (standard approach)
-- 8. The result should be a permutation of the input (same elements, different order)
-- 9. All integers in the result should come before all strings
-- 10. The integer portion should be sorted ascendingly
-- 11. The string portion should be sorted lexicographically

-- Custom inductive type for mixed elements

-- Helper function to check if an element is an integer

section Specs

inductive IntOrString where
  | int : Int → IntOrString
  | str : String → IntOrString
  deriving Inhabited, DecidableEq, Repr

-- Helper Functions

def isInt (elem : IntOrString) : Bool :=
  match elem with
  | IntOrString.int _ => true
  | IntOrString.str _ => false
-- Helper function to check if an element is a string

def isString (elem : IntOrString) : Bool :=
  match elem with
  | IntOrString.int _ => false
  | IntOrString.str _ => true

-- Helper function to define ordering on IntOrString
-- Integers are "less than" strings by convention
-- Within integers, use numeric ordering
-- Within strings, use lexicographic ordering
def IntOrString.le (a b : IntOrString) : Prop :=
  match a, b with
  | IntOrString.int i1, IntOrString.int i2 => i1 ≤ i2
  | IntOrString.int _, IntOrString.str _ => True  -- integers come before strings
  | IntOrString.str _, IntOrString.int _ => False -- strings come after integers
  | IntOrString.str s1, IntOrString.str s2 => s1 ≤ s2  -- lexicographic order

-- Helper function to check if a list is sorted according to our ordering
-- A list is sorted if every adjacent pair is in order
def isSorted (lst : List IntOrString) : Prop :=
  ∀ i, i + 1 < lst.length → IntOrString.le lst[i]! lst[i+1]!

-- Helper function to check if two lists are permutations of each other
-- Two lists are permutations if they have the same length and every element
-- appears with the same frequency in both lists
def isPermutation (lst1 lst2 : List IntOrString) : Prop :=
  lst1.length = lst2.length ∧
  (∀ elem ∈ lst1, (lst1.filter (· == elem)).length = (lst2.filter (· == elem)).length) ∧
  (∀ elem ∈ lst2, (lst1.filter (· == elem)).length = (lst2.filter (· == elem)).length)

-- Postcondition clauses
def ensures1 (input : List IntOrString) (result : List IntOrString) :=
  isPermutation input result  -- result is a permutation of input
def ensures2 (input : List IntOrString) (result : List IntOrString) :=
  isSorted result  -- result is sorted according to our ordering
def ensures3 (input : List IntOrString) (result : List IntOrString) :=
  ∀ i j, i < result.length ∧ j < result.length ∧
            isInt result[i]! ∧ isString result[j]! → i < j  -- integers come before strings

def precondition (input : List IntOrString) :=
  True  -- no preconditions
def postcondition (input : List IntOrString) (result : List IntOrString) :=
  ensures1 input result ∧
  ensures2 input result ∧
  ensures3 input result

end Specs

method SortMixedList (input : List IntOrString)
  return (result : List IntOrString)
  require precondition input
  ensures postcondition input result
  do
    sorry

prove_correct SortMixedList by sorry

-- Test cases for specification validation
section TestCases

-- Test case 0: Sample from the problem
def test0_Input : List IntOrString :=
  [IntOrString.int 19, IntOrString.str "red", IntOrString.int 12,
   IntOrString.str "green", IntOrString.str "blue", IntOrString.int 10,
   IntOrString.str "white", IntOrString.str "green", IntOrString.int 1]

def test0_Expected : List IntOrString :=
  [IntOrString.int 1, IntOrString.int 10, IntOrString.int 12, IntOrString.int 19,
   IntOrString.str "blue", IntOrString.str "green", IntOrString.str "green",
   IntOrString.str "red", IntOrString.str "white"]

-- Test case 1: Mixed list with both integers and strings
def test1_Input : List IntOrString :=
  [IntOrString.int 5, IntOrString.str "apple", IntOrString.int 2,
   IntOrString.str "banana", IntOrString.int 8, IntOrString.str "cherry"]

def test1_Expected : List IntOrString :=
  [IntOrString.int 2, IntOrString.int 5, IntOrString.int 8,
   IntOrString.str "apple", IntOrString.str "banana", IntOrString.str "cherry"]

-- Test case 2: Only integers
def test2_Input : List IntOrString :=
  [IntOrString.int 10, IntOrString.int 3, IntOrString.int 7, IntOrString.int 1]

def test2_Expected : List IntOrString :=
  [IntOrString.int 1, IntOrString.int 3, IntOrString.int 7, IntOrString.int 10]

-- Test case 3: Only strings
def test3_Input : List IntOrString :=
  [IntOrString.str "zebra", IntOrString.str "apple", IntOrString.str "mango", IntOrString.str "banana"]

def test3_Expected : List IntOrString :=
  [IntOrString.str "apple", IntOrString.str "banana", IntOrString.str "mango", IntOrString.str "zebra"]

-- Test case 4: Empty list
def test4_Input : List IntOrString := []
def test4_Expected : List IntOrString := []

-- Test case 5a: Single element list (integer)
def test5a_Input : List IntOrString := [IntOrString.int 42]
def test5a_Expected : List IntOrString := [IntOrString.int 42]

-- Test case 5b: Single element list (string)
def test5b_Input : List IntOrString := [IntOrString.str "hello"]
def test5b_Expected : List IntOrString := [IntOrString.str "hello"]

-- Test case 6: Large mixed list with negative integers
def test6_Input : List IntOrString :=
  [IntOrString.int (-5), IntOrString.str "delta", IntOrString.int 100,
   IntOrString.int (-10), IntOrString.str "alpha", IntOrString.int 0, IntOrString.str "beta"]

def test6_Expected : List IntOrString :=
  [IntOrString.int (-10), IntOrString.int (-5), IntOrString.int 0, IntOrString.int 100,
   IntOrString.str "alpha", IntOrString.str "beta", IntOrString.str "delta"]

-- Test case 7: Duplicate elements
def test7_Input : List IntOrString :=
  [IntOrString.int 5, IntOrString.str "apple", IntOrString.int 5,
   IntOrString.str "apple", IntOrString.int 3]

def test7_Expected : List IntOrString :=
  [IntOrString.int 3, IntOrString.int 5, IntOrString.int 5,
   IntOrString.str "apple", IntOrString.str "apple"]

-- Recommend to validate: 0,1,2,3,6,7

-- Verification that our specification captures the correct behavior:
-- 1. Result is a permutation of input (no elements added or removed)
-- 2. Result is sorted according to our custom ordering (integers before strings)
-- 3. Integer portion is sorted in ascending order
-- 4. String portion is sorted in lexicographic order
-- 5. Handles edge cases: empty list, single element, only ints, only strings
-- 6. Handles duplicates correctly
-- 7. Handles negative integers

end TestCases
