module

public import Velvet
public meta import Velvet

/-!
## Program description

Rearrange an integer array `nums` into three parts: elements less than `pivot`,
elements equal to `pivot`, and elements greater than `pivot`, while preserving
the relative order of the elements in each partition.

The program is expected to run in O(n) time and O(n) extra space.
-/

namespace PartitionArrayAccordingToGivenPivot

section Specs

public def countLt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x < pivot)

public def countEq (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => x = pivot)

public def countGt (nums : Array Int) (pivot : Int) : Nat :=
  nums.countP (fun x => pivot < x)

public def isThreeBlockPartition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  let cL : Nat := countLt nums pivot
  let cE : Nat := countEq nums pivot
  result.size = nums.size ∧
  (∀ (i : Nat), i < result.size →
      (i < cL → result[i]! < pivot) ∧
      ((cL ≤ i ∧ i < cL + cE) → result[i]! = pivot) ∧
      (cL + cE ≤ i → pivot < result[i]!))

public def sameElementCounts (nums : Array Int) (result : Array Int) : Prop :=
  ∀ (x : Int), result.count x = nums.count x

public def precondition (_nums : Array Int) (_pivot : Int) : Prop :=
  True

public def postcondition (nums : Array Int) (pivot : Int) (result : Array Int) : Prop :=
  isThreeBlockPartition nums pivot result ∧
  sameElementCounts nums result

end Specs

section Implementation

public def collectGo (nums : Array Int) (pivot : Int) (i : Nat)
    (lt eq gt : Array Int) : Array Int × Array Int × Array Int :=
  if i < nums.size then
    let x := nums[i]!
    if x < pivot then
      collectGo nums pivot (i + 1) (lt.push x) eq gt
    else if x = pivot then
      collectGo nums pivot (i + 1) lt (eq.push x) gt
    else
      collectGo nums pivot (i + 1) lt eq (gt.push x)
  else
    (lt, eq, gt)
termination_by nums.size - i

public def pivotArrayPure (nums : Array Int) (pivot : Int) : Array Int :=
  let (lt, eq, gt) := collectGo nums pivot 0 #[] #[] #[]
  (lt ++ eq) ++ gt

method pivotArray (nums : Array Int) (pivot : Int)
  returns (result : Array Int)
  requires valid: precondition nums pivot
  ensures partitioned: postcondition nums pivot result
do
  let mut lt : Array Int := #[]
  let mut eq : Array Int := #[]
  let mut gt : Array Int := #[]
  let mut i : Nat := 0
  while' collecting: i < nums.size
    invariant bounds: i ≤ nums.size
    invariant continuation:
      collectGo nums pivot i lt eq gt = collectGo nums pivot 0 #[] #[] #[]
    decreasing remaining: nums.size - i
    done_with done: i = nums.size
  do
    let x := nums[i]!
    if is_lt: x < pivot then
      lt := lt.push x
    else if is_eq: x = pivot then
      eq := eq.push x
    else
      gt := gt.push x
    i := i + 1
  return (lt ++ eq) ++ gt

end Implementation

section Proof

theorem list_partition_length (l : List Int) (pivot : Int) :
    (l.filter (· < pivot)).length + (l.filter (· = pivot)).length + (l.filter (pivot < ·)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h1 : x < pivot
    · have h2 : ¬ x = pivot := by omega
      have h3 : ¬ pivot < x := by omega
      have hd1 : decide (x < pivot) = true := decide_eq_true h1
      have hd2 : decide (x = pivot) = false := decide_eq_false h2
      have hd3 : decide (pivot < x) = false := decide_eq_false h3
      simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
      omega
    · by_cases h2 : x = pivot
      · have h3 : ¬ pivot < x := by omega
        have hd1 : decide (x < pivot) = false := decide_eq_false h1
        have hd2 : decide (x = pivot) = true := decide_eq_true h2
        have hd3 : decide (pivot < x) = false := decide_eq_false h3
        simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
        omega
      · have h3 : pivot < x := by omega
        have hd1 : decide (x < pivot) = false := decide_eq_false h1
        have hd2 : decide (x = pivot) = false := decide_eq_false h2
        have hd3 : decide (pivot < x) = true := decide_eq_true h3
        simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
        omega

theorem list_partition_count (l : List Int) (pivot : Int) (x : Int) :
    (l.filter (· < pivot)).count x +
    (l.filter (· = pivot)).count x +
    (l.filter (pivot < ·)).count x = l.count x := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.filter_cons, List.count_cons]
    by_cases hlt : y < pivot
    · have hneq : ¬ y = pivot := by omega
      have hngt : ¬ pivot < y := by omega
      have hd1 : decide (y < pivot) = true := decide_eq_true hlt
      have hd2 : decide (y = pivot) = false := decide_eq_false hneq
      have hd3 : decide (pivot < y) = false := decide_eq_false hngt
      simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.count_cons]
      by_cases hxy : y = x
      · have hdxy : (y == x) = true := by simp [hxy]
        simp only [hdxy, ite_true]
        omega
      · have hdxy : (y == x) = false := by simp [hxy]
        simp only [hdxy, Bool.false_eq_true, ite_false]
        omega
    · by_cases heq : y = pivot
      · have hngt : ¬ pivot < y := by omega
        have hd1 : decide (y < pivot) = false := decide_eq_false hlt
        have hd2 : decide (y = pivot) = true := decide_eq_true heq
        have hd3 : decide (pivot < y) = false := decide_eq_false hngt
        simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.count_cons]
        by_cases hxy : y = x
        · have hdxy : (y == x) = true := by simp [hxy]
          simp only [hdxy, ite_true]
          omega
        · have hdxy : (y == x) = false := by simp [hxy]
          simp only [hdxy, Bool.false_eq_true, ite_false]
          omega
      · have hgt : pivot < y := by omega
        have hd1 : decide (y < pivot) = false := decide_eq_false hlt
        have hd2 : decide (y = pivot) = false := decide_eq_false heq
        have hd3 : decide (pivot < y) = true := decide_eq_true hgt
        simp only [hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false, List.count_cons]
        by_cases hxy : y = x
        · have hdxy : (y == x) = true := by simp [hxy]
          simp only [hdxy, ite_true]
          omega
        · have hdxy : (y == x) = false := by simp [hxy]
          simp only [hdxy, Bool.false_eq_true, ite_false]
          omega

theorem drop_succ_getElem! (nums : Array Int) (i : Nat) (hi : i < nums.size) :
    nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
  have hlen : i < nums.toList.length := by simpa using hi
  have hd := List.drop_eq_getElem_cons (l := nums.toList) (i := i) hlen
  have hget : nums.toList[i] = nums[i]! := by
    rw [getElem!_pos nums i hi]
    rfl
  rw [← hget]
  exact hd

theorem array_push_append_toArray (acc : Array Int) (x : Int) (xs : List Int) :
    acc.push x ++ xs.toArray = acc ++ (x :: xs).toArray := by
  apply Array.ext'
  simp

theorem collectGo_eq (nums : Array Int) (pivot : Int) (i : Nat) (lt eq gt : Array Int) :
    collectGo nums pivot i lt eq gt =
      (lt ++ ((nums.toList.drop i).filter (· < pivot)).toArray,
       eq ++ ((nums.toList.drop i).filter (· = pivot)).toArray,
       gt ++ ((nums.toList.drop i).filter (pivot < ·)).toArray) := by
  fun_induction collectGo nums pivot i lt eq gt
  case case1 i lt eq gt hi x hlt ih =>
    have hdrop := drop_succ_getElem! nums i hi
    have hd1 : decide (nums[i]! < pivot) = true := decide_eq_true hlt
    have hd2 : decide (nums[i]! = pivot) = false := decide_eq_false (by omega)
    have hd3 : decide (pivot < nums[i]!) = false := decide_eq_false (by omega)
    rw [ih, hdrop]
    simp only [List.filter_cons, hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false,
      array_push_append_toArray]
    rfl
  case case2 i lt eq gt hi x hnlt heq ih =>
    have hdrop := drop_succ_getElem! nums i hi
    have hd1 : decide (nums[i]! < pivot) = false := decide_eq_false hnlt
    have hd2 : decide (nums[i]! = pivot) = true := decide_eq_true heq
    have hd3 : decide (pivot < nums[i]!) = false := decide_eq_false (by omega)
    rw [ih, hdrop]
    simp only [List.filter_cons, hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false,
      array_push_append_toArray]
    rfl
  case case3 i lt eq gt hi x hnlt hneq ih =>
    have hdrop := drop_succ_getElem! nums i hi
    have hgt : pivot < x := by omega
    have hd1 : decide (nums[i]! < pivot) = false := decide_eq_false hnlt
    have hd2 : decide (nums[i]! = pivot) = false := decide_eq_false hneq
    have hd3 : decide (pivot < nums[i]!) = true := decide_eq_true hgt
    rw [ih, hdrop]
    simp only [List.filter_cons, hd1, hd2, hd3, Bool.false_eq_true, ite_true, ite_false,
      array_push_append_toArray]
    rfl
  case case4 i lt eq gt hnot =>
    have hlen : nums.toList.length ≤ i := by simpa using (Nat.le_of_not_gt hnot)
    have hdrop : nums.toList.drop i = [] := List.drop_eq_nil_of_le hlen
    simp [hdrop]

theorem collectGo_zero (nums : Array Int) (pivot : Int) :
    collectGo nums pivot 0 #[] #[] #[] =
      ((nums.toList.filter (· < pivot)).toArray,
       (nums.toList.filter (· = pivot)).toArray,
       (nums.toList.filter (pivot < ·)).toArray) := by
  have h := collectGo_eq nums pivot 0 #[] #[] #[]
  simp [h]

theorem pivotArrayPure_eq_toArray (nums : Array Int) (pivot : Int) :
    pivotArrayPure nums pivot =
      ((nums.toList.filter (· < pivot)) ++
       (nums.toList.filter (· = pivot)) ++
       (nums.toList.filter (pivot < ·))).toArray := by
  unfold pivotArrayPure
  rw [collectGo_zero]
  apply Array.ext'
  simp

theorem countLt_eq (nums : Array Int) (pivot : Int) :
    countLt nums pivot = (nums.toList.filter (· < pivot)).length := by
  unfold countLt
  rw [← Array.countP_toList, List.countP_eq_length_filter]

theorem countEq_eq (nums : Array Int) (pivot : Int) :
    countEq nums pivot = (nums.toList.filter (· = pivot)).length := by
  unfold countEq
  rw [← Array.countP_toList, List.countP_eq_length_filter]

theorem countGt_eq (nums : Array Int) (pivot : Int) :
    countGt nums pivot = (nums.toList.filter (pivot < ·)).length := by
  unfold countGt
  rw [← Array.countP_toList, List.countP_eq_length_filter]

theorem list_filter_getElem!_mem (l : List Int) (p : Int → Bool) (k : Nat) (hk : k < (l.filter p).length) :
    p (l.filter p)[k]! = true := by
  have hpos : (l.filter p)[k]! = (l.filter p)[k] := by
    rw [getElem!_pos (l.filter p) k hk]
  rw [hpos]
  have hmem : (l.filter p)[k] ∈ l.filter p := List.getElem_mem hk
  rw [List.mem_filter] at hmem
  exact hmem.2

theorem getElem_three_block_left (a b c : Array Int) (i : Nat) (hi : i < a.size)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i] = a[i] := by
  have hi_ab : i < (a ++ b).size := by
    simp only [Array.size_append]
    omega
  rw [Array.getElem_append_left hi_ab, Array.getElem_append_left hi]

theorem getElem_three_block_mid (a b c : Array Int) (i : Nat)
    (hle : a.size ≤ i) (hlt : i < a.size + b.size)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i] = b[i - a.size] := by
  have hi_ab : i < (a ++ b).size := by
    simp only [Array.size_append]
    omega
  rw [Array.getElem_append_left hi_ab, Array.getElem_append_right (by omega)]

theorem getElem_three_block_right (a b c : Array Int) (i : Nat)
    (hle : a.size + b.size ≤ i)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i] = c[i - (a.size + b.size)]'(by
      have := h_total
      simp only [Array.size_append] at this
      omega) := by
  have hab_sz : (a ++ b).size = a.size + b.size := Array.size_append
  rw [Array.getElem_append_right (by rw [hab_sz]; exact hle)]
  congr 1
  omega

theorem getElem!_three_block_left (a b c : Array Int) (i : Nat) (hi : i < a.size)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b ++ c) i h_total, getElem!_pos a i hi]
  exact getElem_three_block_left a b c i hi h_total

theorem getElem!_three_block_mid (a b c : Array Int) (i : Nat)
    (hle : a.size ≤ i) (hlt : i < a.size + b.size)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by omega
  rw [getElem!_pos (a ++ b ++ c) i h_total, getElem!_pos b (i - a.size) hb]
  exact getElem_three_block_mid a b c i hle hlt h_total

theorem getElem!_three_block_right (a b c : Array Int) (i : Nat)
    (hle : a.size + b.size ≤ i)
    (h_total : i < (a ++ b ++ c).size) :
    (a ++ b ++ c)[i]! = c[i - (a.size + b.size)]! := by
  have hc : i - (a.size + b.size) < c.size := by
    have := h_total
    simp only [Array.size_append] at this
    omega
  rw [getElem!_pos (a ++ b ++ c) i h_total, getElem!_pos c (i - (a.size + b.size)) hc]
  exact getElem_three_block_right a b c i hle h_total

theorem getElem!_toArray (l : List Int) (k : Nat) (hk : k < l.length) :
    l.toArray[k]! = l[k]! := by
  have hk_arr : k < l.toArray.size := by simpa using hk
  rw [getElem!_pos l.toArray k hk_arr, getElem!_pos l k hk]
  rfl

theorem pivotArrayPure_isThreeBlockPartition (nums : Array Int) (pivot : Int) :
    isThreeBlockPartition nums pivot (pivotArrayPure nums pivot) := by
  let l1 := nums.toList.filter (· < pivot)
  let l2 := nums.toList.filter (· = pivot)
  let l3 := nums.toList.filter (pivot < ·)
  have h_len : l1.length + l2.length + l3.length = nums.size := by
    have h := list_partition_length nums.toList pivot
    have hsz : nums.toList.length = nums.size := nums.length_toList
    omega
  have h_pure : pivotArrayPure nums pivot = (l1.toArray ++ l2.toArray ++ l3.toArray) := by
    rw [pivotArrayPure_eq_toArray]
    apply Array.ext'
    simp [l1, l2, l3]
  have h_sz : (pivotArrayPure nums pivot).size = nums.size := by
    rw [h_pure]
    simp only [Array.size_append]
    omega
  have h_c_lt : countLt nums pivot = l1.length := countLt_eq nums pivot
  have h_c_eq : countEq nums pivot = l2.length := countEq_eq nums pivot
  refine ⟨h_sz, ?_⟩
  intro i hi_sz
  refine ⟨?_, ?_, ?_⟩
  · intro hi
    rw [h_c_lt] at hi
    rw [h_pure]
    have h_tot : i < (l1.toArray ++ l2.toArray ++ l3.toArray).size := by
      rw [← h_pure]
      exact hi_sz
    have h_get := getElem!_three_block_left l1.toArray l2.toArray l3.toArray i (by simpa using hi) h_tot
    rw [h_get, getElem!_toArray l1 i hi]
    have h_mem := list_filter_getElem!_mem nums.toList (· < pivot) i hi
    exact of_decide_eq_true h_mem
  · intro hi
    rw [h_c_lt, h_c_eq] at hi
    rw [h_pure]
    have h_tot : i < (l1.toArray ++ l2.toArray ++ l3.toArray).size := by
      rw [← h_pure]
      exact hi_sz
    have h_get := getElem!_three_block_mid l1.toArray l2.toArray l3.toArray i
      (by simpa using hi.1) (by simpa using hi.2) h_tot
    have hi_sub : i - l1.length < l2.length := by omega
    have h_l1_sz : l1.toArray.size = l1.length := by simp
    rw [h_l1_sz] at h_get
    rw [h_get, getElem!_toArray l2 (i - l1.length) hi_sub]
    have h_mem := list_filter_getElem!_mem nums.toList (· = pivot) (i - l1.length) hi_sub
    exact of_decide_eq_true h_mem
  · intro hi
    rw [h_c_lt, h_c_eq] at hi
    rw [h_pure]
    have h_tot : i < (l1.toArray ++ l2.toArray ++ l3.toArray).size := by
      rw [← h_pure]
      exact hi_sz
    have h_get := getElem!_three_block_right l1.toArray l2.toArray l3.toArray i
      (by simpa using hi) h_tot
    have hi_sub : i - (l1.length + l2.length) < l3.length := by
      have : i < nums.size := by
        have := hi_sz
        rw [h_sz] at this
        exact this
      omega
    have h_sub_arr : i - (l1.toArray.size + l2.toArray.size) = i - (l1.length + l2.length) := by simp
    rw [h_sub_arr] at h_get
    rw [h_get, getElem!_toArray l3 (i - (l1.length + l2.length)) hi_sub]
    have h_mem := list_filter_getElem!_mem nums.toList (pivot < ·) (i - (l1.length + l2.length)) hi_sub
    exact of_decide_eq_true h_mem

theorem pivotArrayPure_sameElementCounts (nums : Array Int) (pivot : Int) :
    sameElementCounts nums (pivotArrayPure nums pivot) := by
  intro x
  have h1 : (pivotArrayPure nums pivot).count x = (pivotArrayPure nums pivot).toList.count x := by
    rw [← Array.count_toList]
  have h2 : nums.count x = nums.toList.count x := by
    rw [← Array.count_toList]
  rw [h1, h2, pivotArrayPure_eq_toArray]
  simp [List.count_append]
  have h := list_partition_count nums.toList pivot x
  omega

theorem pivotArrayPure_postcondition (nums : Array Int) (pivot : Int) :
    postcondition nums pivot (pivotArrayPure nums pivot) := by
  refine ⟨pivotArrayPure_isThreeBlockPartition nums pivot, pivotArrayPure_sameElementCounts nums pivot⟩

theorem collectGo_step_lt (nums : Array Int) (pivot : Int) (i : Nat) (lt eq gt : Array Int)
    (hi : i < nums.size) (hlt : nums[i]! < pivot) :
    collectGo nums pivot i lt eq gt = collectGo nums pivot (i + 1) (lt.push nums[i]!) eq gt := by
  rw [collectGo]
  simp only [hi, hlt, ↓reduceIte]

theorem collectGo_step_eq (nums : Array Int) (pivot : Int) (i : Nat) (lt eq gt : Array Int)
    (hi : i < nums.size) (_hnlt : ¬ nums[i]! < pivot) (heq : nums[i]! = pivot) :
    collectGo nums pivot i lt eq gt = collectGo nums pivot (i + 1) lt (eq.push nums[i]!) gt := by
  have hp : ¬ pivot < pivot := by omega
  rw [collectGo]
  simp only [hi, heq, hp, ↓reduceIte]

theorem collectGo_step_gt (nums : Array Int) (pivot : Int) (i : Nat) (lt eq gt : Array Int)
    (hi : i < nums.size) (hnlt : ¬ nums[i]! < pivot) (hneq : ¬ nums[i]! = pivot) :
    collectGo nums pivot i lt eq gt = collectGo nums pivot (i + 1) lt eq (gt.push nums[i]!) := by
  rw [collectGo]
  simp only [hi, hnlt, hneq, ↓reduceIte]

theorem collectGo_step_exit (nums : Array Int) (pivot : Int) (i : Nat) (lt eq gt : Array Int)
    (hni : ¬ i < nums.size) :
    collectGo nums pivot i lt eq gt = (lt, eq, gt) := by
  rw [collectGo]
  split <;> rename_i h1
  · contradiction
  · rfl

prove_correct pivotArray by
  velvet_vcgen [pivotArray, postcondition]
  · omega
  · rename_i nums pivot
    have h_exit := collectGo_step_exit nums pivot i lt eq gt (by omega)
    rw [h_exit] at continuation
    have h_eq : lt ++ eq ++ gt = pivotArrayPure nums pivot := by
      unfold pivotArrayPure
      rw [← continuation]
    rw [h_eq]
    exact pivotArrayPure_postcondition nums pivot
  · omega
  · omega
  · rename_i nums pivot
    rw [← continuation]
    rw [collectGo_step_lt nums pivot i lt eq gt collecting is_lt]
  · omega
  · omega
  · rename_i nums pivot
    rw [← continuation]
    rw [collectGo_step_eq nums pivot i lt eq gt collecting is_lt is_eq]
  · omega
  · omega
  · rename_i nums pivot
    rw [← continuation]
    rw [collectGo_step_gt nums pivot i lt eq gt collecting is_lt is_eq]
  · omega
  · exact continuation
  · omega

end Proof

end PartitionArrayAccordingToGivenPivot
