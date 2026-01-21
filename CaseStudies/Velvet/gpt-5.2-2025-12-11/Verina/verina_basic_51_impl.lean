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
    BinarySearch: determine the insertion index for an integer `key` into a sorted array `a`.
    Natural language breakdown:
    1. Input is an array `a : Array Int` and a value `key : Int`.
    2. The array is assumed to be sorted in non-decreasing order.
    3. The output is an index `idx : Nat` between 0 and `a.size`.
    4. Every element strictly before `idx` is strictly less than `key`.
    5. Every element from `idx` onward (while in bounds) is greater than or equal to `key`.
    6. If `key` is larger than all elements, the result is `a.size`.
    7. This is the first position where `key` can be inserted while preserving sorted order.
-/

section Specs
-- Helper: non-decreasing sortedness for an Int array (index-based).
-- We keep it simple: all earlier indices have values ≤ later indices.
def isSortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

-- Helper: the lower-bound index characterized by a partition w.r.t. `key`.
-- This property is intended to uniquely determine the insertion index.
def isLowerBoundIndex (a : Array Int) (key : Int) (idx : Nat) : Prop :=
  idx ≤ a.size ∧
  (∀ (i : Nat), i < idx → a[i]! < key) ∧
  (∀ (i : Nat), idx ≤ i → i < a.size → key ≤ a[i]!)

-- Preconditions: array must be sorted non-decreasing.
def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNondecreasing a

-- Postconditions: result is a valid lower-bound insertion index.
def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  isLowerBoundIndex a key result
end Specs

section Impl
method BinarySearch (a : Array Int) (key : Int)
  return (result : Nat)
  require precondition a key
  ensures postcondition a key result
  do
  let mut lo : Nat := 0
  let mut hi : Nat := a.size
  let mut mid : Nat := 0
  let mut v : Int := 0

  while lo < hi
    -- Invariant: basic bounds for the search interval
    -- Init: lo=0, hi=a.size. Preserved by updates (lo := mid+1, hi := mid) and mid is within [lo,hi).
    -- Suffices: on exit with lo ≥ hi and lo ≤ hi, we get lo=hi, used with partition invariants.
    invariant "bs_bounds" lo ≤ hi ∧ hi ≤ a.size
    -- Invariant: all indices strictly below lo are proven to be < key (lower bound property - left partition)
    -- Init: vacuously true for lo=0. Preserved: if v<key we move lo to mid+1 and use sortedness to extend the range.
    invariant "bs_left_lt" (∀ (i : Nat), i < lo → a[i]! < key)
    -- Invariant: all indices from hi to end are ≥ key (right partition)
    -- Init: vacuously true for hi=a.size. Preserved: if v≥key we set hi:=mid and use sortedness.
    invariant "bs_right_ge" (∀ (i : Nat), hi ≤ i → i < a.size → key ≤ a[i]!)
    done_with lo ≥ hi
  do
    mid := lo + (hi - lo) / 2
    v := a[mid]!
    if v < key then
      lo := mid + 1
    else
      hi := mid

  return lo
end Impl

section TestCases
-- Test case 1: example from prompt, key present
-- a = [1,3,5,7,9], key=5 -> insertion index 2
-- IMPORTANT example

def test1_a : Array Int := #[1, 3, 5, 7, 9]

def test1_key : Int := 5

def test1_Expected : Nat := 2

-- Test case 2: key absent between elements
-- a = [1,3,5,7,9], key=6 -> insertion index 3
-- IMPORTANT example

def test2_a : Array Int := #[1, 3, 5, 7, 9]

def test2_key : Int := 6

def test2_Expected : Nat := 3

-- Test case 3: key smaller than all elements -> 0

def test3_a : Array Int := #[2, 4, 6, 8]

def test3_key : Int := 1

def test3_Expected : Nat := 0

-- Test case 4: key larger than all elements -> size

def test4_a : Array Int := #[2, 4, 6, 8]

def test4_key : Int := 10

def test4_Expected : Nat := 4

-- Test case 5: all elements equal to key -> first index 0
-- IMPORTANT example

def test5_a : Array Int := #[1, 1, 1, 1]

def test5_key : Int := 1

def test5_Expected : Nat := 0

-- Test case 6: duplicates with key between duplicate runs
-- a = [1,2,2,2,4], key=2 -> first index with a[i]≥2 is 1

def test6_a : Array Int := #[1, 2, 2, 2, 4]

def test6_key : Int := 2

def test6_Expected : Nat := 1

-- Test case 7: empty array -> size 0

def test7_a : Array Int := #[]

def test7_key : Int := 7

def test7_Expected : Nat := 0

-- Test case 8: single element, key less -> 0

def test8_a : Array Int := #[5]

def test8_key : Int := 4

def test8_Expected : Nat := 0

-- Test case 9: single element, key equal -> 0

def test9_a : Array Int := #[5]

def test9_key : Int := 5

def test9_Expected : Nat := 0

-- Recommend to validate: 1, 2, 5
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((BinarySearch test1_a test1_key).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((BinarySearch test2_a test2_key).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((BinarySearch test3_a test3_key).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((BinarySearch test4_a test4_key).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((BinarySearch test5_a test5_key).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((BinarySearch test6_a test6_key).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((BinarySearch test7_a test7_key).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((BinarySearch test8_a test8_key).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((BinarySearch test9_a test9_key).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for BinarySearch
prove_precondition_decidable_for BinarySearch
prove_postcondition_decidable_for BinarySearch
derive_tester_for BinarySearch
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := BinarySearchTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct BinarySearch by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : Array ℤ)
    (key : ℤ)
    (require_1 : precondition a key)
    (hi : ℕ)
    (lo : ℕ)
    (a_2 : hi ≤ a.size)
    (invariant_bs_left_lt : ∀ i < lo, a[i]! < key)
    (if_pos : lo < hi)
    (if_pos_1 : a[lo + (hi - lo) / 2]! < key)
    : ∀ i < lo + (hi - lo) / 2 + 1, a[i]! < key := by
  intro i hi_lt
  by_cases h : i < lo
  · exact invariant_bs_left_lt i h
  · have hle_mid : i ≤ lo + (hi - lo) / 2 := by
      exact Nat.le_of_lt_succ hi_lt
    have himid : i < lo + (hi - lo) / 2 ∨ i = lo + (hi - lo) / 2 :=
      Nat.lt_or_eq_of_le hle_mid
    cases himid with
    | inl hi_lt_mid =>
        have hmid_lt_hi : lo + (hi - lo) / 2 < hi := by
          have hpos : 0 < hi - lo := Nat.sub_pos_of_lt if_pos
          have hdiv_lt : (hi - lo) / 2 < hi - lo := by
            exact Nat.div_lt_self hpos (by decide : 1 < (2 : Nat))
          have h' : lo + (hi - lo) / 2 < lo + (hi - lo) :=
            Nat.add_lt_add_left hdiv_lt lo
          have hlohi : lo ≤ hi := Nat.le_of_lt if_pos
          have hadd : lo + (hi - lo) = hi := by
            exact Nat.add_sub_of_le hlohi
          simpa [hadd] using h'
        have hmid_lt_size : lo + (hi - lo) / 2 < a.size :=
          lt_of_lt_of_le hmid_lt_hi a_2
        have hs : isSortedNondecreasing a := require_1
        have hle_imid :
            a[i]! ≤ a[lo + (hi - lo) / 2]! :=
          hs i (lo + (hi - lo) / 2) hi_lt_mid hmid_lt_size
        exact lt_of_le_of_lt hle_imid if_pos_1
    | inr hi_eq_mid =>
        simpa [hi_eq_mid] using if_pos_1

theorem goal_1
    (a : Array ℤ)
    (key : ℤ)
    (require_1 : precondition a key)
    (hi : ℕ)
    (lo : ℕ)
    (a_1 : lo ≤ hi)
    (a_2 : hi ≤ a.size)
    (invariant_bs_right_ge : ∀ (i : ℕ), hi ≤ i → i < a.size → key ≤ a[i]!)
    (if_pos : lo < hi)
    (if_neg : key ≤ a[lo + (hi - lo) / 2]!)
    : ∀ (i : ℕ), lo + (hi - lo) / 2 ≤ i → i < a.size → key ≤ a[i]! := by
    intro i hmid hisize
    have hsorted : isSortedNondecreasing a := require_1
    set m : Nat := lo + (hi - lo) / 2 with hmdef
    have hm_le_i : m ≤ i := by simpa [hmdef] using hmid
    have hkey_le_am : key ≤ a[m]! := by simpa [m, hmdef] using if_neg
    cases Nat.lt_or_ge i hi with
    | inl hlt =>
        have hm_lt_hi : m < hi := by
          have hpos : 0 < hi - lo := Nat.sub_pos_of_lt if_pos
          have hdiv : (hi - lo) / 2 < (hi - lo) := by
            simpa using (Nat.div_lt_self (n := hi - lo) (k := 2) hpos (by decide))
          have hadd : lo + (hi - lo) / 2 < lo + (hi - lo) :=
            Nat.add_lt_add_left hdiv lo
          have : lo + (hi - lo) / 2 < hi := by
            simpa [Nat.add_sub_of_le a_1] using hadd
          simpa [m, hmdef] using this
        have hm_lt_size : m < a.size := Nat.lt_of_lt_of_le hm_lt_hi a_2
        cases lt_or_eq_of_le hm_le_i with
        | inl hm_lt_i =>
            have ham_le_ai : a[m]! ≤ a[i]! := hsorted m i hm_lt_i hisize
            exact le_trans hkey_le_am ham_le_ai
        | inr hm_eq_i =>
            simpa [hm_eq_i] using hkey_le_am
    | inr hge =>
        exact invariant_bs_right_ge i hge hisize

theorem goal_2
    (a : Array ℤ)
    (key : ℤ)
    (hi : ℕ)
    (lo : ℕ)
    (mid : ℕ)
    (v : ℤ)
    (a_1 : lo ≤ hi)
    (a_2 : hi ≤ a.size)
    (invariant_bs_left_lt : ∀ i < lo, a[i]! < key)
    (invariant_bs_right_ge : ∀ (i : ℕ), hi ≤ i → i < a.size → key ≤ a[i]!)
    (i : ℕ)
    (i_1 : ℕ)
    (i_2 : ℕ)
    (v_1 : ℤ)
    (done_1 : hi ≤ lo)
    (i_3 : hi = i ∧ lo = i_1 ∧ mid = i_2 ∧ v = v_1)
    : postcondition a key i_1 := by
  -- unpack equalities from i_3
  rcases i_3 with ⟨h_hii, h_loi1, h_midi2, h_vv1⟩
  -- reduce postcondition to isLowerBoundIndex, and rewrite i_1 as lo
  subst h_loi1
  unfold postcondition
  unfold isLowerBoundIndex
  -- show lo = hi from invariants
  have h_lo_eq_hi : lo = hi := Nat.le_antisymm a_1 done_1
  constructor
  · -- lo ≤ a.size
    simpa [h_lo_eq_hi] using a_2
  · constructor
    · -- ∀ i < lo, a[i]! < key
      simpa using invariant_bs_left_lt
    · -- ∀ i, lo ≤ i → i < a.size → key ≤ a[i]!
      intro j hjlo hjsz
      have hjhi : hi ≤ j := by simpa [h_lo_eq_hi] using hjlo
      exact invariant_bs_right_ge j hjhi hjsz


prove_correct BinarySearch by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a key require_1 hi lo a_2 invariant_bs_left_lt if_pos if_pos_1)
  exact (goal_1 a key require_1 hi lo a_1 a_2 invariant_bs_right_ge if_pos if_neg)
  exact (goal_2 a key hi lo mid v a_1 a_2 invariant_bs_left_lt invariant_bs_right_ge i i_1 i_2 v_1 done_1 i_3)
end Proof
