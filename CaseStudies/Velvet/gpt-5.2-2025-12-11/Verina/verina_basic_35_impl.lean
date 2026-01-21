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
    MoveZeroesToEnd: Rearrange an array of integers by moving all zero values to the end while preserving
    the relative order of non-zero elements.

    Natural language breakdown:
    1. Input is an Array Int; output is an Array Int of the same size.
    2. The output contains the same multiset of elements as the input, but with all 0 values moved to the end.
    3. The relative order of the non-zero elements is preserved (stable with respect to non-zeros).
    4. In the output, there is a split point k such that indices < k are non-zero and indices ≥ k are zero.
    5. There are no preconditions; the method must work for any array.
-/

section Specs
-- Helper: list of non-zero elements in array order (stable).
-- We use the list view to talk about order.
def nonzerosList (arr : Array Int) : List Int :=
  arr.toList.filter (fun x => x ≠ 0)

-- Helper: all elements from index k onward are zero.
def allZeroFrom (arr : Array Int) (k : Nat) : Prop :=
  ∀ i : Nat, i < arr.size → k ≤ i → arr[i]! = 0

-- No preconditions.
def precondition (arr : Array Int) : Prop :=
  True

-- Postcondition:
-- 1) size is preserved
-- 2) there is a split point k = number of non-zeros in input
-- 3) prefix (0..k-1) equals the input's nonzero list index-wise (order preserved)
-- 4) the suffix (k..end) is all zeros
-- These properties uniquely determine the output.
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∃ k : Nat,
    k = (nonzerosList arr).length ∧
    k ≤ result.size ∧
    (∀ i : Nat, i < k → result[i]! = (nonzerosList arr)[i]!) ∧
    allZeroFrom result k)
end Specs

section Impl
method MoveZeroesToEnd (arr : Array Int)
  return (result : Array Int)
  require precondition arr
  ensures postcondition arr result
  do
  -- First pass: count non-zeros
  let mut k : Nat := 0
  let mut i : Nat := 0
  while i < arr.size
    -- i stays within bounds.
    -- init: i=0; preserved by i:=i+1; useful for array indexing.
    invariant "mz_count_bounds" i ≤ arr.size
    -- k counts non-zeros seen so far, hence bounded by i.
    -- init: k=0; if nonzero then both increase appropriately; otherwise only i increases.
    invariant "mz_count_k_le_i" k ≤ i
    -- Strong functional invariant: k is exactly the number of nonzeros in the processed prefix.
    -- init: both sides = 0 on empty prefix; preserved by filter behavior when extending by
    -- a zero (length unchanged) or a nonzero (length increases by 1).
    invariant "mz_count_k_eq_len" k = (nonzerosList (arr.extract 0 i)).length
  do
    if arr[i]! ≠ 0 then
      k := k + 1
    i := i + 1

  -- Second pass: write non-zeros in order
  let mut result := Array.replicate arr.size (0 : Int)
  let mut write : Nat := 0
  i := 0
  while i < arr.size
    -- Bounds for indices.
    -- init: i=0, write=0; preserved: i increases each iter; write increases only on nonzero.
    invariant "mz_write_bounds" i ≤ arr.size ∧ write ≤ i
    -- result size is preserved by set!
    invariant "mz_result_size" result.size = arr.size
    -- write tracks the number of nonzeros in the processed prefix.
    -- This is crucial to justify that the next nonzero is written exactly at index `write`.
    invariant "mz_write_eq_len" write = (nonzerosList (arr.extract 0 i)).length
    -- Functional invariant: written prefix matches the nonzero list of the processed prefix.
    -- With write = length, all indices < write are in-bounds for the nonzero list.
    invariant "mz_prefix_pointwise" (∀ j : Nat, j < write → result[j]! = (nonzerosList (arr.extract 0 i))[j]!)
    -- Remaining positions beyond write stay 0 (replicate + set! only at index write).
    invariant "mz_suffix_zero" (∀ j : Nat, write ≤ j → j < result.size → result[j]! = 0)
  do
    if arr[i]! = 0 then
      i := i + 1
      continue
    result := result.set! write (arr[i]!)
    write := write + 1
    i := i + 1

  -- Remaining suffix is already zeros due to replicate
  return result
end Impl

section TestCases
-- Test case 1: example from prompt
-- Input: #[0, 1, 0, 3, 12] -> #[1, 3, 12, 0, 0]
def test1_arr : Array Int := #[0, 1, 0, 3, 12]
def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

-- Test case 2: leading zeros then one element
-- #[0,0,1] -> #[1,0,0]
def test2_arr : Array Int := #[0, 0, 1]
def test2_Expected : Array Int := #[1, 0, 0]

-- Test case 3: already has no zeros
-- #[1,2,3] -> unchanged
def test3_arr : Array Int := #[1, 2, 3]
def test3_Expected : Array Int := #[1, 2, 3]

-- Test case 4: all zeros
-- #[0,0,0] -> unchanged
def test4_arr : Array Int := #[0, 0, 0]
def test4_Expected : Array Int := #[0, 0, 0]

-- Test case 5: empty array
-- #[] -> #[]
def test5_arr : Array Int := #[]
def test5_Expected : Array Int := #[]

-- Test case 6: zeros already at end
-- #[1,2,0,0] -> #[1,2,0,0]
def test6_arr : Array Int := #[1, 2, 0, 0]
def test6_Expected : Array Int := #[1, 2, 0, 0]

-- Test case 7: interleaved zeros with negatives
-- #[0,-1,0,-2,3,0] -> #[-1,-2,3,0,0,0]
def test7_arr : Array Int := #[0, -1, 0, -2, 3, 0]
def test7_Expected : Array Int := #[-1, -2, 3, 0, 0, 0]

-- Test case 8: single element non-zero
-- #[5] -> #[5]
def test8_arr : Array Int := #[5]
def test8_Expected : Array Int := #[5]

-- Test case 9: single element zero
-- #[0] -> #[0]
def test9_arr : Array Int := #[0]
def test9_Expected : Array Int := #[0]

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test3, test7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((MoveZeroesToEnd test1_arr).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((MoveZeroesToEnd test2_arr).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((MoveZeroesToEnd test3_arr).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((MoveZeroesToEnd test4_arr).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((MoveZeroesToEnd test5_arr).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((MoveZeroesToEnd test6_arr).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((MoveZeroesToEnd test7_arr).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((MoveZeroesToEnd test8_arr).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((MoveZeroesToEnd test9_arr).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for MoveZeroesToEnd
prove_precondition_decidable_for MoveZeroesToEnd
prove_postcondition_decidable_for MoveZeroesToEnd
derive_tester_for MoveZeroesToEnd
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := MoveZeroesToEndTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct MoveZeroesToEnd by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (if_pos : i < arr.size)
    (if_pos_1 : ¬arr[i]! = 0)
    (hk_succ : k = (nonzerosList (arr.extract 0 i)).length)
    (hnonzeros_def_i : nonzerosList (arr.extract 0 i) = List.filter (fun x ↦ !decide (x = 0)) (List.take i arr.toList))
    (hnonzeros_def_succ : nonzerosList (arr.extract 0 (i + 1)) = List.filter (fun x ↦ !decide (x = 0)) (List.take (i + 1) arr.toList))
    (htoList_extract_succ : True)
    (htoList_extract_i : True)
    : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!] := by
    have hi' : i < arr.toList.length := by
      simpa [Array.length_toList] using if_pos

    have htake :
        List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr.toList[i]] :=
      List.take_succ_eq_append_getElem (l := arr.toList) hi'

    -- `arr.toList[i]` is definitionally `arr[i]` (in-bounds), and `arr[i]!` reduces to `arr[i]` (in-bounds).
    have h_toList_get : arr.toList[i] = arr[i]! := by
      simp [Array.getElem_toList (xs := arr) (i := i) if_pos, if_pos]

    simpa [h_toList_get] using htake

theorem goal_0_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (if_pos : i < arr.size)
    (if_pos_1 : ¬arr[i]! = 0)
    (hk_succ : k = (nonzerosList (arr.extract 0 i)).length)
    (hnonzeros_def_i : nonzerosList (arr.extract 0 i) = List.filter (fun x ↦ !decide (x = 0)) (List.take i arr.toList))
    (hnonzeros_def_succ : nonzerosList (arr.extract 0 (i + 1)) = List.filter (fun x ↦ !decide (x = 0)) (List.take (i + 1) arr.toList))
    (htoList_extract_succ : True)
    (htoList_extract_i : True)
    (hList_extract_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!])
    (htoList_grow : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!])
    (hfilter_append : True)
    : (List.filter (fun x ↦ !decide (x = 0)) [arr[i]!]).length = 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (if_pos : i < arr.size)
    (if_pos_1 : ¬arr[i]! = 0)
    (hk_succ : k = (nonzerosList (arr.extract 0 i)).length)
    (hnonzeros_def_i : nonzerosList (arr.extract 0 i) = List.filter (fun x ↦ !decide (x = 0)) (List.take i arr.toList))
    (hnonzeros_def_succ : nonzerosList (arr.extract 0 (i + 1)) = List.filter (fun x ↦ !decide (x = 0)) (List.take (i + 1) arr.toList))
    (htoList_extract_succ : True)
    (htoList_extract_i : True)
    (hList_extract_succ : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!])
    (htoList_grow : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!])
    (hfilter_append : True)
    (hsingleton_filter_len : (List.filter (fun x ↦ !decide (x = 0)) [arr[i]!]).length = 1)
    : (nonzerosList (arr.extract 0 (i + 1))).length = (nonzerosList (arr.extract 0 i)).length + 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (if_pos : i < arr.size)
    (if_pos_1 : ¬arr[i]! = 0)
    : k + 1 = (nonzerosList (arr.extract 0 (i + 1))).length := by
    -- Step 1: rewrite the target using the invariant k = length(nonzeros of prefix i)
    have hk_succ : k + 1 = (nonzerosList (arr.extract 0 i)).length + 1 := by
        -- add 1 to both sides of invariant_mz_count_k_eq_len
        simpa [invariant_mz_count_k_eq_len]
    -- Step 2: express nonzerosList via toList.filter (definition)
    have hnonzeros_def_i :
        nonzerosList (arr.extract 0 i) = (arr.extract 0 i).toList.filter (fun x => x ≠ 0) := by
        -- unfold nonzerosList
        simp [nonzerosList]
    -- Step 3: same definition for prefix (i+1)
    have hnonzeros_def_succ :
        nonzerosList (arr.extract 0 (i + 1)) =
          (arr.extract 0 (i + 1)).toList.filter (fun x => x ≠ 0) := by
        -- unfold nonzerosList
        simp [nonzerosList]
    -- Step 4: relate extract-toList at i+1 to extract-toList at i using List.extract on arr.toList
    have htoList_extract_succ :
        (arr.extract 0 (i + 1)).toList =
          arr.toList.extract 0 (i + 1) := by
        -- Array.toList_extract
        simpa using (Array.toList_extract (xs := arr) (start := 0) (stop := i + 1))
    -- Step 5: same for i
    have htoList_extract_i :
        (arr.extract 0 i).toList =
          arr.toList.extract 0 i := by
        -- Array.toList_extract
        simpa using (Array.toList_extract (xs := arr) (start := 0) (stop := i))
    -- Step 6: list-extract growth: extract 0 (i+1) = extract 0 i ++ [arr[i]!] (at the List level)
    have hList_extract_succ :
        arr.toList.extract 0 (i + 1) =
          arr.toList.extract 0 i ++ [arr[i]!] := by
        -- uses i < arr.size to identify the newly added element at position i
        -- (typical lemma: List.extract_succ / take_succ / extract_eq_take_drop; proof omitted)
        (try simp at *; expose_names); exact (goal_0_0 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len if_pos if_pos_1 hk_succ hnonzeros_def_i hnonzeros_def_succ htoList_extract_succ htoList_extract_i); done
    -- Step 7: transfer the growth fact back to Array.extract toLists
    have htoList_grow :
        (arr.extract 0 (i + 1)).toList =
          (arr.extract 0 i).toList ++ [arr[i]!] := by
        -- combine steps 4,5,6
        -- (rewrite both sides via htoList_extract_* and hList_extract_succ)
        (try simp at *; expose_names); exact hList_extract_succ; done
    -- Step 8: filter distributes over append
    have hfilter_append :
        ((arr.extract 0 i).toList ++ [arr[i]!]).filter (fun x => x ≠ 0) =
          ((arr.extract 0 i).toList.filter (fun x => x ≠ 0)) ++
            ([arr[i]!].filter (fun x => x ≠ 0)) := by
        -- List.filter_append
        simpa using (List.filter_append (p := fun x : ℤ => x ≠ 0) (l₁ := (arr.extract 0 i).toList) (l₂ := [arr[i]!]))
    -- Step 9: since arr[i]! ≠ 0, filtering the singleton keeps it (length 1)
    have hsingleton_filter_len :
        ([arr[i]!].filter (fun x => x ≠ 0)).length = 1 := by
        -- simp using if_pos_1
        -- (List.filter on singleton reduces to if; hypothesis makes it true)
        (try simp at *; expose_names); exact (goal_0_1 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len if_pos if_pos_1 hk_succ hnonzeros_def_i hnonzeros_def_succ htoList_extract_succ htoList_extract_i hList_extract_succ htoList_grow hfilter_append); done
    -- Step 10: conclude the length increases by 1 when extending by a nonzero element
    have hlen_nonzeros_succ :
        (nonzerosList (arr.extract 0 (i + 1))).length =
          (nonzerosList (arr.extract 0 i)).length + 1 := by
        -- unfold nonzerosList on both sides, rewrite toList growth, use filter_append and singleton length
        (try simp at *; expose_names); exact (goal_0_2 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len if_pos if_pos_1 hk_succ hnonzeros_def_i hnonzeros_def_succ htoList_extract_succ htoList_extract_i hList_extract_succ htoList_grow hfilter_append hsingleton_filter_len); done
    -- Step 11: finish by rewriting with hk_succ and hlen_nonzeros_succ
    calc
      k + 1
          = (nonzerosList (arr.extract 0 i)).length + 1 := by
              simpa using hk_succ
      _   = (nonzerosList (arr.extract 0 (i + 1))).length := by
              -- symmetric of hlen_nonzeros_succ
              simpa [hlen_nonzeros_succ]

theorem goal_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (if_pos : i < arr.size)
    (if_neg : arr[i]! = 0)
    : k = (nonzerosList (arr.extract 0 (i + 1))).length := by
  -- rewrite k using the invariant
  rw [invariant_mz_count_k_eq_len]
  -- reduce to showing the nonzero-filtered length doesn't change when the next element is 0
  have hiList : i < arr.toList.length := by
    simpa using if_pos

  -- decompose take (i+1) on the underlying list
  have htake :
      arr.toList.take (i + 1) = arr.toList.take i ++ [arr.toList[i]] := by
    simpa using (List.take_succ_eq_append_getElem (l := arr.toList) (i := i) hiList)

  -- identify toList of extract with List.extract on toList, then simplify extract 0 n = take n
  have hextract_i :
      (arr.extract 0 i).toList = arr.toList.take i := by
    simpa [List.extract, List.take] using
      (Array.toList_extract (xs := arr) (start := 0) (stop := i))
  have hextract_succ :
      (arr.extract 0 (i + 1)).toList = arr.toList.take (i + 1) := by
    simpa [List.extract, List.take] using
      (Array.toList_extract (xs := arr) (start := 0) (stop := i + 1))

  -- bridge array indexing to list indexing
  have hget : arr.toList[i] = arr[i]! := by
    -- `getElem!` is definitionaly `getD` of `getElem?`; and `getElem?` agrees with toList
    have hopt : arr.toList[i]? = arr[i]? := by
      simpa using (Array.getElem?_eq_getElem?_toList (xs := arr) (i := i)).symm
    have hs : (i < arr.toList.length) := hiList
    have hs' : (i < arr.size) := if_pos
    -- convert option equality to value equality using `getD` with the in-bounds simp lemmas
    simpa [List.getElem?_eq_getElem, Array.getElem?_eq_getElem, hs, hs'] using congrArg (fun o => o.getD 0) hopt

  have if_neg_list : arr.toList[i] = 0 := by
    simpa [hget] using if_neg

  -- now compute lengths via filter over append and the fact the singleton filters to []
  have hlen :
      (nonzerosList (arr.extract 0 (i + 1))).length =
        (nonzerosList (arr.extract 0 i)).length := by
    -- unfold and rewrite extracts; use take decomposition and filter_append
    simp [nonzerosList, hextract_i, hextract_succ, htake, List.filter_append, List.length_append,
      List.filter_singleton, if_neg_list]

  -- finish
  simpa [hlen]

theorem goal_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    : 0 = (nonzerosList #[]).length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_3
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    : write = (nonzerosList (arr.extract 0 (i_3 + 1))).length := by
    intros; expose_names; exact (goal_1 arr require_1 i_3 write a a_1 invariant_mz_write_eq_len if_pos if_pos_1); done

theorem goal_4_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write)
    (hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (hiList : i_3 < arr.toList.length)
    : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr[i_3]] := by
    -- Start from the list lemma, then rewrite the last element using Array.getElem_toList.
    have h :=
      (List.take_succ_eq_append_getElem (l := arr.toList) (i := i_3) hiList)
    -- h : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr.toList[i_3]]
    -- Rewrite `arr.toList[i_3]` to `arr[i_3]`.
    simpa [Array.getElem_toList (xs := arr) (i := i_3) if_pos] using h

theorem goal_4_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write)
    (hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (hiList : i_3 < arr.toList.length)
    (htake : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr.toList[i_3]])
    (hget_toList : arr.toList[i_3] = arr[i_3]!)
    : (arr.extract 0 i_3).toList = List.take i_3 arr.toList := by
    simpa [List.extract, Nat.zero_eq, Nat.sub_zero] using
      (Array.toList_extract (xs := arr) (start := 0) (stop := i_3))

theorem goal_4_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write)
    (hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (hiList : i_3 < arr.toList.length)
    (htake : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr.toList[i_3]])
    (hget_toList : arr.toList[i_3] = arr[i_3]!)
    (hextract_i : (arr.extract 0 i_3).toList = List.take i_3 arr.toList)
    : (arr.extract 0 (i_3 + 1)).toList = List.take (i_3 + 1) arr.toList := by
    simpa [List.extract, Nat.zero_eq, Nat.sub_zero] using
      (Array.toList_extract (xs := arr) (start := 0) (stop := i_3 + 1))

theorem goal_4_3
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write)
    (hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (hiList : i_3 < arr.toList.length)
    (htake : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr[i_3]])
    (hget_toList : arr[i_3] = arr[i_3]!)
    (hextract_i : True)
    (hextract_succ : True)
    : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr[i_3]!] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_4_4
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write)
    (hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (hiList : i_3 < arr.toList.length)
    (htake : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr[i_3]])
    (hget_toList : arr[i_3] = arr[i_3]!)
    (hextract_i : True)
    (hextract_succ : True)
    (htoList_grow : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr[i_3]!])
    (hfilter_singleton_zero : arr[i_3]! = 0)
    : nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) := by
    -- unfold nonzerosList and reduce to a statement about filtering lists
    unfold nonzerosList
    -- rewrite extracts to list.extract, then use the provided growth equation for `take`
    simp [Array.toList_extract, List.filter_append, htoList_grow, hfilter_singleton_zero]

theorem goal_4
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_pos_1 : arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 := by
    intro j hj

    have hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
      (try simp at *; expose_names); exact invariant_mz_prefix_pointwise j hj; done

    have hiList : i_3 < arr.toList.length := by
      (try simp at *; expose_names); exact if_pos; done

    have htake : List.take (i_3 + 1) arr.toList = List.take i_3 arr.toList ++ [arr.toList[i_3]] := by
      (try simp at *; expose_names); exact (goal_4_0 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise j hj hprefix_old hiList); done

    have hget_toList : arr.toList[i_3] = arr[i_3]! := by
      (try simp at *; expose_names); exact Eq.symm (getElem!_pos arr i_3 hiList); done

    have hextract_i : (arr.extract 0 i_3).toList = List.take i_3 arr.toList := by
      (try simp at *; expose_names); exact (goal_4_1 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise j hj hprefix_old hiList htake hget_toList); done

    have hextract_succ : (arr.extract 0 (i_3 + 1)).toList = List.take (i_3 + 1) arr.toList := by
      (try simp at *; expose_names); exact (goal_4_2 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise j hj hprefix_old hiList htake hget_toList hextract_i); done

    have htoList_grow : (arr.extract 0 (i_3 + 1)).toList = (arr.extract 0 i_3).toList ++ [arr[i_3]!] := by
      (try simp at *; expose_names); exact (goal_4_3 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise j hj hprefix_old hiList htake hget_toList hextract_i hextract_succ); done

    have hfilter_singleton_zero : ([arr[i_3]!].filter (fun x : ℤ => x ≠ 0)) = [] := by
      (try simp at *; expose_names); exact if_pos_1; done

    have hnonzerosList_eq :
        nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) := by
      (try simp at *; expose_names); exact (goal_4_4 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise j hj hprefix_old hiList htake hget_toList hextract_i hextract_succ htoList_grow hfilter_singleton_zero); done

    have hgetD_eq :
        (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 =
          (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
      (try simp at *; expose_names); exact (congrFun (congrArg Option.getD (congrFun (congrArg getElem? hnonzerosList_eq) j)) 0); done

    calc
      result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
        simpa using hprefix_old
      _ = (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 := by
        simpa [hgetD_eq]

theorem goal_5
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_neg : ¬arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    : write + 1 = (nonzerosList (arr.extract 0 (i_3 + 1))).length := by
    intros; expose_names; exact (goal_0 arr require_1 i_3 write a a_1 invariant_mz_write_eq_len if_pos if_neg); done

theorem goal_6_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_neg : ¬arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write + 1)
    (hj_le_write : j ≤ write)
    (hwrite_lt_arr_size : write < arr.size)
    (hwrite_lt_result_size : write < result.size)
    (hwrite_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (hnonzeros_len_succ : write + 1 = (nonzerosList (arr.extract 0 (i_3 + 1))).length)
    (hnonzeros_append : nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) ++ [arr[i_3]!])
    (hj_lt : j < write)
    (hj_ne_write : ¬write = j)
    (hget?_unchanged : (result.setIfInBounds write arr[i_3]!)[j]? = result[j]?)
    : (result.setIfInBounds write arr[i_3]!)[j]! = result[j]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_6_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_neg : ¬arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write + 1)
    (hj_le_write : j ≤ write)
    (hwrite_lt_arr_size : write < arr.size)
    (hwrite_lt_result_size : write < result.size)
    (hwrite_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (hnonzeros_len_succ : write + 1 = (nonzerosList (arr.extract 0 (i_3 + 1))).length)
    (hnonzeros_append : nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) ++ [arr[i_3]!])
    (hj_eq : j = write)
    (hget?_at_write : (result.setIfInBounds write arr[i_3]!)[write]? = some arr[i_3]!)
    : (result.setIfInBounds write arr[i_3]!)[write]! = arr[i_3]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_6_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_neg : ¬arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (j : ℕ)
    (hj : j < write + 1)
    (hj_le_write : j ≤ write)
    (hj_lt_or_eq : j < write ∨ j = write)
    (hwrite_lt_arr_size : write < arr.size)
    (hwrite_lt_result_size : write < result.size)
    (hwrite_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (hnonzeros_len_succ : write + 1 = (nonzerosList (arr.extract 0 (i_3 + 1))).length)
    : nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) ++ [arr[i_3]!] := by
    sorry

theorem goal_6
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (if_pos : i_3 < arr.size)
    (if_neg : ¬arr[i_3]! = 0)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    : ∀ j < write + 1, (result.setIfInBounds write arr[i_3]!)[j]! = (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 := by
  intro j hj

  have hj_le_write : j ≤ write := by
    (try simp at *; expose_names); exact Nat.le_of_lt_succ hj; done

  have hj_lt_or_eq : j < write ∨ j = write := by
    (try simp at *; expose_names); exact Nat.lt_succ_iff_lt_or_eq.mp hj; done

  have hwrite_lt_arr_size : write < arr.size := by
    (try simp at *; expose_names); exact Nat.lt_of_le_of_lt a_1 if_pos; done

  have hwrite_lt_result_size : write < result.size := by
    -- use invariant_mz_result_size to transfer hwrite_lt_arr_size
    (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq hwrite_lt_arr_size (id (Eq.symm invariant_mz_result_size))); done

  have hwrite_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length := by
    simpa using invariant_mz_write_eq_len

  have hnonzeros_len_succ : write + 1 = (nonzerosList (arr.extract 0 (i_3 + 1))).length := by
    simpa using
      (goal_5 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len
        i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg
        done_1 i_2 invariant_mz_prefix_pointwise)

  have hnonzeros_append :
      nonzerosList (arr.extract 0 (i_3 + 1)) = nonzerosList (arr.extract 0 i_3) ++ [arr[i_3]!] := by
    (try simp at *; expose_names); exact (goal_6_0 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg done_1 i_2 invariant_mz_prefix_pointwise j hj hj_le_write hj_lt_or_eq hwrite_lt_arr_size hwrite_lt_result_size hwrite_eq_len hnonzeros_len_succ); done

  cases hj_lt_or_eq with
  | inl hj_lt =>
      have hj_ne_write : write ≠ j := by
        (try simp at *; expose_names); exact Nat.ne_of_lt' hj_lt; done

      have hget?_unchanged : (result.setIfInBounds write arr[i_3]!)[j]? = result[j]? := by
        simpa using
          (Array.getElem?_setIfInBounds_ne (xs := result) (i := write) (j := j) hj_ne_write (a := arr[i_3]!))

      have hget!_unchanged : (result.setIfInBounds write arr[i_3]!)[j]! = result[j]! := by
        (try simp at *; expose_names); exact (goal_6_1 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg done_1 i_2 invariant_mz_prefix_pointwise j hj hj_le_write hwrite_lt_arr_size hwrite_lt_result_size hwrite_eq_len hnonzeros_len_succ hnonzeros_append hj_lt hj_ne_write hget?_unchanged); done

      have hprefix_old : result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
        simpa using invariant_mz_prefix_pointwise j hj_lt

      have hj_lt_len_old : j < (nonzerosList (arr.extract 0 i_3)).length := by
        -- rewrite hj_lt using hwrite_eq_len
        (try simp at *; expose_names); exact Nat.lt_of_lt_of_eq hj_lt invariant_mz_write_eq_len; done

      have hnonzeros_get?_left :
          (nonzerosList (arr.extract 0 (i_3 + 1)))[j]? = (nonzerosList (arr.extract 0 i_3))[j]? := by
        simpa [hnonzeros_append] using
          (List.getElem?_append_left (l₁ := nonzerosList (arr.extract 0 i_3)) (l₂ := [arr[i_3]!]) hj_lt_len_old)

      have hnonzeros_getD_left :
          (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
        -- apply congrArg (fun o => o.getD 0) to hnonzeros_get?_left
        (try simp at *; expose_names); exact (congrFun (congrArg Option.getD hnonzeros_get?_left) 0); done

      calc
        (result.setIfInBounds write arr[i_3]!)[j]! = result[j]! := by
          simpa using hget!_unchanged
        _ = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0 := by
          simpa using hprefix_old
        _ = (nonzerosList (arr.extract 0 (i_3 + 1)))[j]?.getD 0 := by
          simpa [hnonzeros_getD_left]
  | inr hj_eq =>
      have hget?_at_write :
          (result.setIfInBounds write arr[i_3]!)[write]? = some (arr[i_3]!) := by
        -- use the explicit characterization lemma for getElem?_setIfInBounds at j=i, and hwrite_lt_result_size
        -- (it becomes `if write = write then if write < result.size then some ... else none else ...`)
        (try simp at *; expose_names); exact (Array.getElem?_setIfInBounds_self_of_lt hwrite_lt_result_size); done

      have hget!_set_idx : (result.setIfInBounds write arr[i_3]!)[write]! = arr[i_3]! := by
        -- turn the get? fact into a get! fact
        (try simp at *; expose_names); exact (goal_6_2 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg done_1 i_2 invariant_mz_prefix_pointwise j hj hj_le_write hwrite_lt_arr_size hwrite_lt_result_size hwrite_eq_len hnonzeros_len_succ hnonzeros_append hj_eq hget?_at_write); done

      have hget?_at_boundary :
          (nonzerosList (arr.extract 0 (i_3 + 1)))[write]? = some (arr[i_3]!) := by
        simpa [hnonzeros_append, hwrite_eq_len] using
          (List.getElem?_concat_length (l := nonzerosList (arr.extract 0 i_3)) (a := arr[i_3]!))

      have hgetD_at_boundary :
          (nonzerosList (arr.extract 0 (i_3 + 1)))[write]?.getD 0 = arr[i_3]! := by
        simpa [hget?_at_boundary] using (Option.getD_some (a := arr[i_3]!) (b := (0 : ℤ)))

      -- finish, rewriting j = write
      simpa [hj_eq] using (Eq.trans hget!_set_idx (Eq.symm hgetD_at_boundary))

theorem goal_7
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    : 0 = (nonzerosList #[]).length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_8_0
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    : result = i_5 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_8_1
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    (hres : result = i_5)
    (hi3_eq : i_3 = arr.size)
    (hextract_full : arr = #[] ∨ arr.size ≤ i_3)
    : nonzerosList (arr.extract 0 i_3) = nonzerosList arr := by
    -- i_3 is the full size, so extract 0 i_3 is the whole array
    subst hi3_eq
    simp [nonzerosList, Array.extract_size]

theorem goal_8_2
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    (hres : result = i_5)
    (hi3_eq : i_3 = arr.size)
    (hnonzeros_extract_full : nonzerosList (arr.extract 0 i_3) = nonzerosList arr)
    (hextract_full : arr = #[] ∨ arr.size ≤ i_3)
    : write = (nonzerosList arr).length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_8_3
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    (hres : result = i_5)
    (hi3_eq : i_3 = arr.size)
    (hnonzeros_extract_full : nonzerosList (arr.extract 0 i_3) = nonzerosList arr)
    (hwrite_eq_nonzeros_len : write = (nonzerosList arr).length)
    (hextract_full : arr = #[] ∨ arr.size ≤ i_3)
    : write ≤ result.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_8_4
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    (hres : result = i_5)
    (hi3_eq : i_3 = arr.size)
    (hnonzeros_extract_full : nonzerosList (arr.extract 0 i_3) = nonzerosList arr)
    (hwrite_eq_nonzeros_len : write = (nonzerosList arr).length)
    (hwrite_le_result_size : write ≤ result.size)
    (hextract_full : arr = #[] ∨ arr.size ≤ i_3)
    : ∀ j < write, result[j]! = (nonzerosList arr)[j]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_8_5
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    (hres : result = i_5)
    (hi3_eq : i_3 = arr.size)
    (hnonzeros_extract_full : nonzerosList (arr.extract 0 i_3) = nonzerosList arr)
    (hwrite_eq_nonzeros_len : write = (nonzerosList arr).length)
    (hwrite_le_result_size : write ≤ result.size)
    (hprefix_getD : ∀ j < write, result[j]! = (nonzerosList arr)[j]?.getD 0)
    (hextract_full : arr = #[] ∨ arr.size ≤ i_3)
    (hprefix_bang : ∀ j < write, result[j]! = (nonzerosList arr)[j]?.getD 0)
    : allZeroFrom result write := by
    intro idx hidx_lt hwrite_le
    exact invariant_mz_suffix_zero idx hwrite_le hidx_lt

theorem goal_8
    (arr : Array ℤ)
    (require_1 : precondition arr)
    (i : ℕ)
    (k : ℕ)
    (invariant_mz_count_bounds : i ≤ arr.size)
    (invariant_mz_count_k_le_i : k ≤ i)
    (invariant_mz_count_k_eq_len : k = (nonzerosList (arr.extract 0 i)).length)
    (i_1 : ℕ)
    (k_1 : ℕ)
    (i_3 : ℕ)
    (result : Array ℤ)
    (write : ℕ)
    (a : i_3 ≤ arr.size)
    (a_1 : write ≤ i_3)
    (invariant_mz_result_size : result.size = arr.size)
    (invariant_mz_write_eq_len : write = (nonzerosList (arr.extract 0 i_3)).length)
    (invariant_mz_suffix_zero : ∀ (j : ℕ), write ≤ j → j < result.size → result[j]! = 0)
    (i_4 : ℕ)
    (i_5 : Array ℤ)
    (write_1 : ℕ)
    (done_1 : arr.size ≤ i)
    (i_2 : i = i_1 ∧ k = k_1)
    (invariant_mz_prefix_pointwise : ∀ j < write, result[j]! = (nonzerosList (arr.extract 0 i_3))[j]?.getD 0)
    (done_2 : arr.size ≤ i_3)
    (i_6 : i_3 = i_4 ∧ result = i_5 ∧ write = write_1)
    : postcondition arr i_5 := by
    have hres : result = i_5 := by (try simp at *; expose_names); exact (goal_8_0 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6); done
    have hi3_eq : i_3 = arr.size := by (try simp at *; expose_names); exact (Nat.le_antisymm a done_2); done
    have hextract_full : arr.extract 0 i_3 = arr := by (try simp at *; expose_names); exact (Or.inr done_2); done
    have hnonzeros_extract_full : nonzerosList (arr.extract 0 i_3) = nonzerosList arr := by (try simp at *; expose_names); exact (goal_8_1 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6 hres hi3_eq hextract_full); done
    have hwrite_eq_nonzeros_len : write = (nonzerosList arr).length := by (try simp at *; expose_names); exact (goal_8_2 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6 hres hi3_eq hnonzeros_extract_full hextract_full); done
    have hwrite_le_result_size : write ≤ result.size := by (try simp at *; expose_names); exact (goal_8_3 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6 hres hi3_eq hnonzeros_extract_full hwrite_eq_nonzeros_len hextract_full); done
    have hprefix_getD : ∀ j < write, result[j]! = (nonzerosList arr)[j]?.getD 0 := by (try simp at *; expose_names); exact (goal_8_4 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6 hres hi3_eq hnonzeros_extract_full hwrite_eq_nonzeros_len hwrite_le_result_size hextract_full); done
    have hprefix_bang : ∀ j < write, result[j]! = (nonzerosList arr)[j]! := by (try simp at *; expose_names); exact (fun j a ↦ hprefix_getD j a); done
    have hsuffix_allZeroFrom : allZeroFrom result write := by (try simp at *; expose_names); exact (goal_8_5 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6 hres hi3_eq hnonzeros_extract_full hwrite_eq_nonzeros_len hwrite_le_result_size hprefix_getD hextract_full hprefix_bang); done
    have hpost_result : postcondition arr result := by
      refine And.intro invariant_mz_result_size ?_
      refine ⟨write, ?_⟩
      refine And.intro hwrite_eq_nonzeros_len ?_
      refine And.intro hwrite_le_result_size ?_
      refine And.intro hprefix_bang hsuffix_allZeroFrom
    simpa [hres] using hpost_result


prove_correct MoveZeroesToEnd by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len if_pos if_pos_1)
  exact (goal_1 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len if_pos if_neg)
  exact (goal_2 arr require_1)
  exact (goal_3 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise)
  exact (goal_4 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_pos_1 done_1 i_2 invariant_mz_prefix_pointwise)
  exact (goal_5 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg done_1 i_2 invariant_mz_prefix_pointwise)
  exact (goal_6 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero if_pos if_neg done_1 i_2 invariant_mz_prefix_pointwise)
  exact (goal_7 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 done_1 i_2)
  exact (goal_8 arr require_1 i k invariant_mz_count_bounds invariant_mz_count_k_le_i invariant_mz_count_k_eq_len i_1 k_1 i_3 result write a a_1 invariant_mz_result_size invariant_mz_write_eq_len invariant_mz_suffix_zero i_4 i_5 write_1 done_1 i_2 invariant_mz_prefix_pointwise done_2 i_6)
end Proof
