import Lean
import Mathlib.Tactic

-- Helper Functions

def countOccurrences (value: Int) (lists: List (List Int)) : Nat :=
  lists.flatten.count value

-- Find the first occurrence index of a value in the flattened list
def firstOccurrenceIndex (value: Int) (lists: List (List Int)) : Nat :=
  let flattened := lists.flatten
  match flattened.findIdx? (· = value) with
  | some idx => idx
  | none => flattened.length

-- Check if a list is sorted by: frequency (descending), then first occurrence (ascending) for ties
def isSortedByFreqThenOccurrence (sorted: List Int) (lists: List (List Int)) : Prop :=
  ∀ i j, i < j → j < sorted.length →
    let vi := sorted[i]!
    let vj := sorted[j]!
    let fi := countOccurrences vi lists
    let fj := countOccurrences vj lists
    let idxi := firstOccurrenceIndex vi lists
    let idxj := firstOccurrenceIndex vj lists
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

def require1 (lists : List (List Int)) (k : Nat) :=
  ∀ lst ∈ lists, lst.Sorted (· ≤ ·)
def require2 (lists : List (List Int)) (k : Nat) :=
  ∀ lst ∈ lists, lst.Nodup

-- Postcondition clauses
def ensures1 (lists : List (List Int)) (k : Nat) (result : List Int) :=
  ∃ sorted : List Int,
    (∀ elem ∈ lists.flatten, ∃! p ∈ sorted, p = elem) ∧
    (∀ p ∈ result, p ∈ lists.flatten) ∧
    isSortedByFreqThenOccurrence sorted lists ∧
    result = sorted.take k

def precondition (lists: List (List Int)) (k: Nat) :=
  require1 lists k ∧ require2 lists k

def postcondition (lists: List (List Int)) (k: Nat) (result: List Int) :=
  ensures1 lists k result

-- Test Cases
def test0_lists : List (List Int) := [[1, 2, 6], [1, 3, 4, 5, 7, 8], [1, 3, 5, 6, 8, 9], [2, 5, 7, 11], [1, 4, 7, 8, 12]]

def test0_k : Nat := 3

def test0_Expected : List Int := [1, 5, 7]

def test1_lists : List (List Int) := [[1, 2, 3], [2, 3, 4], [3, 4, 5]]

def test1_k : Nat := 2

def test1_Expected : List Int := [3, 2]

def test2_lists : List (List Int) := [[1], [2], [3], [4]]

def test2_k : Nat := 2

def test2_Expected : List Int := [1, 2]

def test4_lists : List (List Int) := [[1, 2, 3, 4, 5]]

def test4_k : Nat := 3

def test4_Expected : List Int := [1, 2, 3]

def test6_lists : List (List Int) := [[-3, -1, 0], [-1, 0, 2], [0, 2, 4]]

def test6_k : Nat := 2

def test6_Expected : List Int := [0, -1]

def test9_lists : List (List Int) := [[1, 2], [3, 4], [1, 2], [3, 4]]

def test9_k : Nat := 3

def test9_Expected : List Int := [1, 2, 3]

def test16_lists : List (List Int) := [[1, 2], [3, 4]]

def test16_k : Nat := 0

def test16_Expected : List Int := []

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test0
----------------------------
lemma test0_precondition :
  precondition test0_lists test0_k := by
  -- Check that each list in `test0_lists` is sorted and has no duplicates.
  simp [precondition, test0_lists];
  -- Check that each list in `test0_lists` is sorted and has no duplicates by examining each list individually.
  simp [require1, require2, test0_lists]

noncomputable section AristotleLemmas

/-
The sorted list for test0, sorted by frequency then first occurrence.
-/
def test0_witness : List Int := [1, 5, 7, 8, 2, 6, 3, 4, 9, 11, 12]

end AristotleLemmas

lemma test0_postcondition :
  postcondition test0_lists test0_k test0_Expected := by
  refine' ⟨ test0_witness, _, _, _ ⟩ <;> norm_cast;
  unfold isSortedByFreqThenOccurrence;
  simp [test0_lists, test0_k, test0_witness];
  exact ⟨ by intro i j hij hj; interval_cases j <;> interval_cases i <;> decide, rfl ⟩

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lists test1_k := by
  -- Check that each list in `test1_lists` is sorted and has no duplicates.
  simp [precondition, require1, require2];
  native_decide

lemma test1_postcondition :
  postcondition test1_lists test1_k test1_Expected := by
  constructor;
  case w => exact [ 3, 2, 4, 1, 5 ];
  simp +decide [ ExistsUnique ];
  rintro ( _ | _ | _ | _ | _ | i ) ( _ | _ | _ | _ | _ | j ) <;> simp +arith +decide

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_lists test2_k := by
  unfold precondition;
  -- Check that all lists in `test2_lists` are sorted.
  simp [require1, require2, test2_lists]

lemma test2_postcondition :
  postcondition test2_lists test2_k test2_Expected := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact [ 1, 2, 3, 4 ];
  · native_decide +revert;
  · native_decide;
  · rintro ( _ | _ | _ | _ | i ) ( _ | _ | _ | _ | j ) <;> norm_num;
    all_goals native_decide;
  · rfl

----------------------------
-- Verification: test4
----------------------------
lemma test4_precondition :
  precondition test4_lists test4_k := by
  -- Check that the list [1, 2, 3, 4, 5] is sorted and has no duplicates.
  simp [precondition, require1, require2];
  decide +revert

lemma test4_postcondition :
  postcondition test4_lists test4_k test4_Expected := by
  -- Let's choose the sorted list [1, 2, 3, 4, 5] and show it satisfies the conditions.
  use [1, 2, 3, 4, 5];
  unfold isSortedByFreqThenOccurrence; simp +decide ;
  intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_lists test6_k := by
  -- Check that each list in test6_lists is sorted and has no duplicates.
  have h_sorted : ∀ lst ∈ test6_lists, lst.Sorted (· ≤ ·) := by
    native_decide
  have h_nodup : ∀ lst ∈ test6_lists, lst.Nodup := by
    native_decide;
  exact ⟨ h_sorted, h_nodup ⟩

lemma test6_postcondition :
  postcondition test6_lists test6_k test6_Expected := by
  constructor;
  -- Let's verify the postcondition for the given test case. We need to show that the list [0, -1, 2, 4, -3] satisfies the conditions.
  constructor;
  swap;
  rotate_right;
  exact [ 0, -1, 2, -3, 4 ];
  · unfold isSortedByFreqThenOccurrence; simp +decide ;
    intro i j hij hj; interval_cases j <;> interval_cases i <;> native_decide;
  · decide +revert

----------------------------
-- Verification: test9
----------------------------
lemma test9_precondition :
  precondition test9_lists test9_k := by
  constructor;
  · -- Each list in `test9_lists` is sorted.
    simp [require1, test9_lists];
  · -- Each list in the list of lists is nodup because they are all pairs of distinct numbers.
    simp [require2, test9_lists]

lemma test9_postcondition :
  postcondition test9_lists test9_k test9_Expected := by
  -- Let's verify that the result [1, 2, 3] satisfies the postcondition.
  use [1, 2, 3, 4];
  -- Let's verify that the list [1, 2, 3, 4] satisfies the conditions for the postcondition.
  simp [test9_lists, test9_Expected, test9_k];
  -- Let's verify that the list [1, 2, 3, 4] is sorted by frequency and then by first occurrence.
  simp [isSortedByFreqThenOccurrence];
  simp +decide [ ExistsUnique ];
  intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

----------------------------
-- Verification: test16
----------------------------
lemma test16_precondition :
  precondition test16_lists test16_k := by
  simp [precondition, test16_lists, test16_k];
  -- Check that each list is sorted and has no duplicates.
  simp [require1, require2]

lemma test16_postcondition :
  postcondition test16_lists test16_k test16_Expected := by
  -- The empty list is trivially sorted by frequency and first occurrence.
  simp [postcondition, test16_lists, test16_k, test16_Expected];
  -- Since $k = 0$, the result should be the empty list. The ensures1 condition requires that the sorted list is a permutation of the flattened lists. The flattened lists here are [1, 2, 3, 4]. The empty list can't be a permutation of that, so there's a contradiction.
  use [1, 2, 3, 4];
  -- Since the list [1, 2, 3, 4] is already sorted by frequency and first occurrence, the conjunction holds.
  simp [isSortedByFreqThenOccurrence];
  -- Let's verify each part of the conjunction.
  apply And.intro;
  · exact ⟨ ⟨ 1, by norm_num ⟩, ⟨ 2, by norm_num ⟩, ⟨ 3, by norm_num ⟩, ⟨ 4, by norm_num ⟩ ⟩;
  · intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

-----------------------------
-- Uniqueness Verification --
-----------------------------
noncomputable section AristotleLemmas

def sortKey (lists : List (List Int)) (x : Int) : Int × Nat :=
  (- (countOccurrences x lists : Int), firstOccurrenceIndex x lists)

lemma sortKey_injective {lists : List (List Int)} {x y : Int}
  (hx : x ∈ lists.flatten) (hy : y ∈ lists.flatten)
  (h : sortKey lists x = sortKey lists y) : x = y := by
    -- Since the countOccurrences is the same, we have countOccurrences x lists = countOccurrences y lists.
    -- Also, since the firstOccurrenceIndex is the same, we have firstOccurrenceIndex x lists = firstOccurrenceIndex y lists.
    -- This implies that x and y are actually the same element.
    have h_eq : firstOccurrenceIndex x lists = firstOccurrenceIndex y lists := by
      injection h;
    unfold firstOccurrenceIndex at h_eq;
    have h_eq : ∀ {l : List ℤ}, x ∈ l → y ∈ l → List.findIdx? (fun z => z = x) l = List.findIdx? (fun z => z = y) l → x = y := by
      -- If the findIdx? of x and y in the list are the same, then the positions of x and y in the list are the same. Since the list is sorted and has no duplicates, this implies x and y are the same element.
      intros l hx hy h_eq
      induction' l with hd tl ih;
      · contradiction;
      · by_cases hx' : x = hd <;> by_cases hy' : y = hd <;> simp_all +decide [ List.findIdx?_cons ];
        · cases h : List.findIdx? ( fun z => Decidable.decide ( z = y ) ) tl <;> simp_all +decide;
        · split_ifs at h_eq <;> simp_all +decide [ ne_comm ];
          cases h : List.findIdx? ( fun z => Decidable.decide ( z = x ) ) tl <;> cases h' : List.findIdx? ( fun z => Decidable.decide ( z = y ) ) tl <;> aesop;
    grind

lemma neg_int_lt_iff_nat_gt (a b : Nat) : (- (a : Int)) < - (b : Int) ↔ a > b := by
  -- By simplifying, we can see that $-(a : ℤ) < -(b : ℤ)$ is equivalent to $a > b$.
  simp [neg_lt_neg_iff]

lemma neg_int_eq_iff_nat_eq (a b : Nat) : (- (a : Int)) = - (b : Int) ↔ a = b := by
  -- The negation function is injective, so if -(a : ℤ) = -(b : ℤ), then a = b.
  simp [Int.neg_inj]

def rel (lists : List (List Int)) (x y : Int) : Prop :=
  Prod.Lex (· < ·) (· < ·) (sortKey lists x) (sortKey lists y)

lemma rel_def (lists : List (List Int)) (x y : Int) :
  rel lists x y ↔
  (countOccurrences x lists > countOccurrences y lists) ∨
  (countOccurrences x lists = countOccurrences y lists ∧ firstOccurrenceIndex x lists < firstOccurrenceIndex y lists) := by
    -- By definition of `rel`, we have that `rel lists x y` holds if and only if the first element of `sortKey` for `x` is less than the first element for `y`, or if they are equal, then the second element for `x` is less than the second element for `y`. This follows directly from the definition of `sortKey`.
    simp [rel, sortKey];
    grind

lemma isSorted_implies_sorted_rel {lists : List (List Int)} {sorted : List Int} :
  isSortedByFreqThenOccurrence sorted lists → sorted.Sorted (rel lists) := by
    intro h;
    -- By definition of `isSortedByFreqThenOccurrence`, if `sorted` is sorted according to the relation `rel lists`, then for any `i < j` in the range of `sorted`, the elements at `i` and `j` satisfy the conditions in `h`.
    have h_sorted : ∀ i j : ℕ, i < j → i < sorted.length → j < sorted.length → rel lists (sorted[i]!) (sorted[j]!) := by
      -- By definition of `rel`, if `fi > fj` or `fi = fj ∧ idxi < idxj`, then `rel lists (sorted[i]!) (sorted[j]!)`.
      intros i j hij hi hj
      specialize h i j hij hj;
      -- By definition of `rel`, if `fi > fj` or `fi = fj ∧ idxi < idxj`, then `rel lists (sorted[i]!) (sorted[j]!)` holds.
      apply (rel_def lists (sorted[i]!) (sorted[j]!)).mpr h;
    refine' List.pairwise_iff_get.mpr _;
    aesop

lemma rel_trans {lists : List (List Int)} : Transitive (rel lists) := by
  -- To prove transitivity, we need to show that if rel lists x y and rel lists y z, then rel lists x z.
  intros x y z hxy hyz;
  -- By definition of Prod.Lex, if (a, b) < (c, d) and (c, d) < (e, f), then (a, b) < (e, f).
  apply Prod.Lex.trans hxy hyz

lemma rel_antisym {lists : List (List Int)} : ∀ x y, rel lists x y → rel lists y x → False := by
  -- If rel lists x y holds, then either the count of x is greater than y's, or their counts are equal and x's first occurrence is earlier.
  intros x y hxy hyx
  simp [rel] at hxy hyx;
  grind

lemma rel_total_on_S {lists : List (List Int)} {x y : Int}
  (hx : x ∈ lists.flatten) (hy : y ∈ lists.flatten) :
  rel lists x y ∨ rel lists y x ∨ x = y := by
    unfold rel;
    -- By definition of `sortKey`, we know that `sortKey lists x` and `sortKey lists y` are either equal or not.
    by_cases h_eq : sortKey lists x = sortKey lists y;
    · exact Or.inr <| Or.inr <| sortKey_injective hx hy h_eq;
    · grind

lemma rel_mem_not_mem {lists : List (List Int)} {x y : Int}
  (hx : x ∈ lists.flatten) (hy : y ∉ lists.flatten) :
  rel lists x y := by
    -- Since y is not in the flattened list, its count is zero. The count of x is at least one because x is in the flattened list. Therefore, the first part of the disjunction holds.
    have h_count : countOccurrences x lists > 0 ∧ countOccurrences y lists = 0 := by
      exact ⟨ List.count_pos_iff.mpr hx, List.count_eq_zero_of_not_mem hy ⟩;
    -- Since the count of x is greater than zero and the count of y is zero, the first part of the disjunction holds.
    simp [rel_def, h_count]

instance rel_decidable (lists : List (List Int)) : DecidableRel (rel lists) :=
  fun x y => inferInstanceAs (Decidable (Prod.Lex (· < ·) (· < ·) (sortKey lists x) (sortKey lists y)))

lemma rel_irreflexive (lists : List (List Int)) : Irreflexive (rel lists) := by
  -- By definition of `rel`, we know that `rel lists x x` is false for all `x`.
  intros x
  simp [rel];
  grind

lemma sorted_valid_part_unique (lists : List (List Int)) (sorted1 sorted2 : List Int)
  (h1 : isSortedByFreqThenOccurrence sorted1 lists)
  (h2 : isSortedByFreqThenOccurrence sorted2 lists)
  (h_perm1 : ∀ x ∈ lists.flatten, ∃! p ∈ sorted1, p = x)
  (h_perm2 : ∀ x ∈ lists.flatten, ∃! p ∈ sorted2, p = x) :
  sorted1.filter (· ∈ lists.flatten) = sorted2.filter (· ∈ lists.flatten) := by
    have h_unique_filter : ∀ x, x ∈ List.filter (fun x => x ∈ lists.flatten) sorted1 ↔ x ∈ List.filter (fun x => x ∈ lists.flatten) sorted2 := by
      intros x
      simp [h_perm1, h_perm2];
      intro y hy hx; specialize h_perm1 x ( List.mem_flatten.mpr ⟨ y, hy, hx ⟩ ) ; specialize h_perm2 x ( List.mem_flatten.mpr ⟨ y, hy, hx ⟩ ) ; cases h_perm1 ; cases h_perm2 ; aesop;
    have h_unique_filter : List.Nodup (List.filter (fun x => x ∈ lists.flatten) sorted1) ∧ List.Nodup (List.filter (fun x => x ∈ lists.flatten) sorted2) := by
      have h_unique_filter : List.Nodup sorted1 ∧ List.Nodup sorted2 := by
        have h_unique_filter : ∀ {l : List ℤ}, isSortedByFreqThenOccurrence l lists → List.Nodup l := by
          intros l hl; exact (by
          -- If the list l is sorted by the given criteria, then for any i < j, the element at i is not equal to the element at j. Hence, l is nodup.
          have h_nodup : ∀ i j, i < j → j < l.length → l[i]! ≠ l[j]! := by
            intros i j hij hjl; specialize hl i j hij hjl; aesop;
          rw [ List.nodup_iff_injective_get ];
          intros i j hij;
          exact le_antisymm ( le_of_not_gt fun hi => h_nodup _ _ hi ( by simp ) <| by simpa [ List.get ] using hij.symm ) ( le_of_not_gt fun hj => h_nodup _ _ hj ( by simp ) <| by simpa [ List.get ] using hij ));
        exact ⟨ h_unique_filter h1, h_unique_filter h2 ⟩;
      exact ⟨ h_unique_filter.1.filter _, h_unique_filter.2.filter _ ⟩;
    have h_unique_filter : List.Perm (List.filter (fun x => x ∈ lists.flatten) sorted1) (List.filter (fun x => x ∈ lists.flatten) sorted2) := by
      grind;
    have h_unique_filter : ∀ {l1 l2 : List ℤ}, List.Sorted (rel lists) l1 → List.Sorted (rel lists) l2 → List.Perm l1 l2 → l1 = l2 := by
      intros l1 l2 hl1 hl2 hperm; exact (by
      apply_rules [ List.eq_of_perm_of_sorted ];
      exact ⟨ fun x y hxy hyx => by have := rel_antisym x y hxy hyx; contradiction ⟩);
    apply h_unique_filter;
    · have h_sorted1 : List.Sorted (rel lists) sorted1 := by
        exact?;
      exact h_sorted1.filter _;
    · exact List.Pairwise.filter _ ( isSorted_implies_sorted_rel h2 );
    · assumption

lemma take_eq_filter_take {α} (l : List α) (k : Nat) (p : α → Prop) [DecidablePred p] :
  (∀ x ∈ l.take k, p x) → l.take k = (l.filter p).take k := by
    induction' k with k ih generalizing l <;> cases l <;> aesop

end AristotleLemmas

lemma uniqueness (lists: List (List Int)) (k: Nat):
  precondition lists k →
  (∀ ret1 ret2,
    postcondition lists k ret1 →
    postcondition lists k ret2 →
    ret1 = ret2) := by
  intro h_precondition ret1 ret2 hret1 hret2
  obtain ⟨sorted1, hsorted1, hret1_eq⟩ := hret1
  obtain ⟨sorted2, hsorted2, hret2_eq⟩ := hret2;
  -- By `sorted_valid_part_unique`, `sorted1.filter (· ∈ lists.flatten) = sorted2.filter (· ∈ lists.flatten)`.
  have h_filter_eq : sorted1.filter (· ∈ lists.flatten) = sorted2.filter (· ∈ lists.flatten) := by
    convert sorted_valid_part_unique lists sorted1 sorted2 hret1_eq.2.1 hret2_eq.2.1 _ _ using 1;
    · exact hsorted1;
    · exact hsorted2;
  have h_take_eq : List.take k sorted1 = List.take k (sorted1.filter (· ∈ lists.flatten)) ∧ List.take k sorted2 = List.take k (sorted2.filter (· ∈ lists.flatten)) := by
    apply And.intro;
    · apply take_eq_filter_take;
      grind;
    · apply take_eq_filter_take;
      grind;
  aesop
