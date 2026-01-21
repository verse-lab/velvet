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
    Find: find the first occurrence index of a key in an integer array
    Natural language breakdown:
    1. Inputs are an array of integers `a` and an integer `key`.
    2. The output is an integer index of the first position where `key` occurs in `a`.
    3. If `key` does not occur in `a`, the output is -1.
    4. If the output is not -1, it must be a valid index: 0 ≤ result < a.size.
    5. If the output is not -1, then `a[Int.toNat result]! = key`.
    6. If the output is not -1, then every earlier position `j` with 0 ≤ j < result has `a[Int.toNat j]! ≠ key`.
    7. The array may be empty; there are no input preconditions.
-/

section Specs
-- Helper predicate: `result` is a valid found index of `key` in `a`.
-- Uses `Int.toNat` and explicit range constraints so that `a[...]!` is safe.
def FoundIndex (a : Array Int) (key : Int) (result : Int) : Prop :=
  0 ≤ result ∧
  (Int.toNat result) < a.size ∧
  a[(Int.toNat result)]! = key ∧
  ∀ (j : Int), 0 ≤ j ∧ j < result → a[(Int.toNat j)]! ≠ key

-- Helper predicate: key does not appear anywhere in the array.
def KeyAbsent (a : Array Int) (key : Int) : Prop :=
  ∀ (i : Nat), i < a.size → a[i]! ≠ key

-- No preconditions: array can be empty/non-empty; key arbitrary.
def precondition (a : Array Int) (key : Int) : Prop :=
  True

def postcondition (a : Array Int) (key : Int) (result : Int) : Prop :=
  (result = -1 ∧ KeyAbsent a key) ∨
  (result ≠ -1 ∧ FoundIndex a key result)
end Specs

section Impl
method Find (a: Array Int) (key: Int) return (result: Int)
  require precondition a key
  ensures postcondition a key result
  do
    let mut i : Nat := 0
    let mut found : Bool := false
    let mut res : Int := (-1)

    while i < a.size ∧ (found = false)
      -- Invariant: index stays within bounds (init: i=0; step: i:=i+1; exit gives i=a.size)
      invariant "Find_inv_i_bounds" (i ≤ a.size)
      -- Invariant: if not found yet, all visited positions are not the key
      -- init: vacuously for i=0; step: when a[i] != key, we increment i and extend the range;
      -- if a[i]=key then found becomes true so antecedent false.
      invariant "Find_inv_prefix_no_key" (found = false → (∀ j : Nat, j < i → a[j]! ≠ key))
      -- Invariant: if found then res points to a valid index with key, and all earlier indices are not key
      -- established when we set found:=true and res:=ofNat i; preserved since i doesn't change afterwards.
      invariant "Find_inv_foundindex" (found = true →
        (0 ≤ res ∧ (Int.toNat res) < a.size ∧ a[(Int.toNat res)]! = key ∧
          ∀ (j : Int), 0 ≤ j ∧ j < res → a[(Int.toNat j)]! ≠ key))
      -- Invariant: res is -1 exactly when not found
      -- init: res=-1, found=false; step: when we find, set both; otherwise both unchanged.
      invariant "Find_inv_res_flag" ((res = -1) ↔ (found = false))
      done_with (i = a.size ∨ found = true)
    do
      if a[i]! = key then
        found := true
        res := Int.ofNat i
      else
        i := i + 1

    return res
end Impl

section TestCases
-- Test case 1: example from prompt
-- a = #[1,2,3,4,5], key = 3 -> first index is 2
def test1_a : Array Int := #[1, 2, 3, 4, 5]
def test1_key : Int := 3
def test1_Expected : Int := 2

-- Test case 2: key occurs multiple times; first occurrence is at index 0
def test2_a : Array Int := #[5, 7, 5, 9]
def test2_key : Int := 5
def test2_Expected : Int := 0

-- Test case 3: key not present in a non-empty array
def test3_a : Array Int := #[2, 4, 6, 8]
def test3_key : Int := 5
def test3_Expected : Int := (-1)

-- Test case 4: empty array always yields -1
def test4_a : Array Int := #[]
def test4_key : Int := 10
def test4_Expected : Int := (-1)

-- Test case 5: negative numbers; first occurrence is not at 0
def test5_a : Array Int := #[0, -3, -1, -3]
def test5_key : Int := (-3)
def test5_Expected : Int := 1

-- Test case 6: singleton array where key is present
def test6_a : Array Int := #[42]
def test6_key : Int := 42
def test6_Expected : Int := 0

-- Test case 7: singleton array where key is absent
def test7_a : Array Int := #[42]
def test7_key : Int := 0
def test7_Expected : Int := (-1)

-- Test case 8: key present at last index
def test8_a : Array Int := #[1, 1, 1, 2]
def test8_key : Int := 2
def test8_Expected : Int := 3

-- Test case 9: all elements match key; should return 0
def test9_a : Array Int := #[7, 7, 7]
def test9_key : Int := 7
def test9_Expected : Int := 0

-- Recommend to validate: 1, 5, 9
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((Find test1_a test1_key).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((Find test2_a test2_key).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((Find test3_a test3_key).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((Find test4_a test4_key).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((Find test5_a test5_key).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((Find test6_a test6_key).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((Find test7_a test7_key).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((Find test8_a test8_key).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((Find test9_a test9_key).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for Find
prove_precondition_decidable_for Find
prove_postcondition_decidable_for Find
derive_tester_for Find
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := FindTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct Find by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (key : ℤ)
    (found : Bool)
    (i : ℕ)
    (res : ℤ)
    (invariant_Find_inv_prefix_no_key : found = false → ∀ j < i, ¬a[j]! = key)
    (invariant_Find_inv_foundindex : found = true → 0 ≤ res ∧ res.toNat < a.size ∧ a[res.toNat]! = key ∧ ∀ (j : ℤ), 0 ≤ j → j < res → ¬a[j.toNat]! = key)
    (invariant_Find_inv_res_flag : res = -1 ↔ found = false)
    (done_1 : i = a.size ∨ found = true)
    (i_1 : Bool)
    (i_2 : ℕ)
    (res_1 : ℤ)
    (i_3 : found = i_1 ∧ i = i_2 ∧ res = res_1)
    : postcondition a key res_1 := by
    have hres : res = res_1 := i_3.2.2
    -- prove postcondition for `res`, then rewrite to `res_1`
    have : postcondition a key res := by
      by_cases hfound : found = true
      · -- found branch
        right
        constructor
        · -- res ≠ -1
          intro hEq
          have : found = false := (invariant_Find_inv_res_flag.mp hEq)
          -- contradiction: true = false
          exact False.elim (by cases hfound ▸ this)
        · -- FoundIndex
          -- the invariant gives exactly the components of FoundIndex
          simpa [FoundIndex] using (invariant_Find_inv_foundindex hfound)
      · -- not found branch
        have hfoundFalse : found = false := by
          cases found <;> simp at hfound ⊢
        left
        constructor
        · -- res = -1
          exact (invariant_Find_inv_res_flag.mpr hfoundFalse)
        · -- KeyAbsent
          unfold KeyAbsent
          -- from done_1 and found=false, get i=a.size
          have hi : i = a.size := by
            cases done_1 with
            | inl h => exact h
            | inr ht =>
              exfalso
              exact hfound (by simpa using ht)
          intro n hn
          have hpref := invariant_Find_inv_prefix_no_key hfoundFalse
          -- use prefix_no_key with i=a.size
          have : ¬ a[n]! = key := by
            have hn' : n < i := by simpa [hi] using hn
            exact hpref n hn'
          simpa [Ne, not_false_eq_true] using this
    simpa [hres] using this


prove_correct Find by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a key found i res invariant_Find_inv_prefix_no_key invariant_Find_inv_foundindex invariant_Find_inv_res_flag done_1 i_1 i_2 res_1 i_3)
end Proof
