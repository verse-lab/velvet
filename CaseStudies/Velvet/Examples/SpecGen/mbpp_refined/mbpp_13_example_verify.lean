import Lean
import Mathlib.Tactic

-- Helper Functions

def countWord (list : List String) (w : String) : Nat :=
  list.count w

def firstIndex (list : List String) (w : String) : Nat :=
  match list.findIdx? (· = w) with
  | some idx => idx
  | none => list.length

def isSortedByCountAndOccurrence
  (words : List String)
  (result : List (String × Nat)) : Prop :=
  ∀ i j, i < j → j < result.length →
    let wi := result[i]!.1
    let wj := result[j]!.1
    let fi := result[i]!.2
    let fj := result[j]!.2
    let idxi := firstIndex words wi
    let idxj := firstIndex words wj
    (fi > fj) ∨ (fi = fj ∧ idxi < idxj)

-- Postcondition clauses
def ensures1 (words : List String) (result : List (String × Nat)) : Prop :=
  ∃ sorted : List (String × Nat),
    (∀ p ∈ sorted, p.2 = countWord words p.1) ∧
    (∀ p ∈ words, ∃! q ∈ sorted, q.1 = p) ∧
    (∀ p ∈ sorted, p.1 ∈ words) ∧
    isSortedByCountAndOccurrence words sorted ∧
    result = sorted.take 4

def precondition (words: List String) :=
  True

def postcondition (words: List String) (result: List (String × Nat)) :=
  ensures1 words result

-- Test Cases
def test1_words : List String :=
  ["red","green","black","pink","black","white","black","eyes","white","black",
   "orange","pink","pink","red","red","white","orange","white","black","pink",
   "green","green","pink","green","pink","white","orange","orange","red"]

def test1_Expected : List (String × Nat) :=
  [("pink", 6), ("black", 5), ("white", 5), ("red", 4)]

def test2_words : List String := []

def test2_Expected : List (String × Nat) := []

def test3_words : List String := ["hello"]

def test3_Expected : List (String × Nat) := [("hello", 1)]

def test7_words : List String := ["alpha", "beta", "gamma", "delta", "epsilon"]

def test7_Expected : List (String × Nat) := [("alpha", 1), ("beta", 1), ("gamma", 1), ("delta", 1)]

def test8_words : List String := ["dog", "bird", "cat", "dog", "cat", "fish"]

def test8_Expected : List (String × Nat) := [("dog", 2), ("cat", 2), ("bird", 1), ("fish", 1)]

def test11_words : List String := ["a", "b", "a", "c", "a", "d", "b", "c", "e"]

def test11_Expected : List (String × Nat) := [("a", 3), ("b", 2), ("c", 2), ("d", 1)]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_words := by
  -- The precondition is defined as True, so it's always true.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_words test1_Expected := by
  -- Let's construct the sorted list and show it meets all conditions.
  use [("pink", 6), ("black", 5), ("white", 5), ("red", 4), ("green", 4), ("orange", 4), ("eyes", 1)];
  -- Let's verify each part of the conjunction.
  constructor;
  · native_decide;
  · constructor;
    · decide +revert;
    · unfold isSortedByCountAndOccurrence; simp +decide ;
      intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_words := by
  -- The precondition is always true by definition.
  simp [precondition]

lemma test2_postcondition :
  postcondition test2_words test2_Expected := by
  -- Let's choose the empty list for `sorted`.
  use []
  simp [test2_words, test2_Expected];
  -- In the base case, when the list is empty, the result is trivially sorted.
  simp [isSortedByCountAndOccurrence]

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_words := by
  exact?

lemma test3_postcondition :
  postcondition test3_words test3_Expected := by
  -- Let's choose the sorted list to be [("hello", 1)].
  use [("hello", 1)];
  -- Verify that the count of "hello" in test3_words is 1.
  simp [countWord, test3_words];
  -- Show that the list [("hello", 1)] is sorted by count and first occurrence.
  simp [isSortedByCountAndOccurrence];
  -- Show that the list [("hello", 1)] is sorted by count and first occurrence. Since there is only one element, the condition is trivially satisfied.
  simp [ExistsUnique];
  -- Let's simplify the goal.
  aesop

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_words := by
  exact?

lemma test7_postcondition :
  postcondition test7_words test7_Expected := by
  -- Let's choose the sorted list of words based on their counts.
  use [("alpha", 1), ("beta", 1), ("gamma", 1), ("delta", 1), ("epsilon", 1)];
  -- Let's verify the first part of the conjunction.
  simp [isSortedByCountAndOccurrence];
  refine' ⟨ _, _, _, _ ⟩;
  · native_decide;
  · unfold test7_words;
    -- For each p in the list, the unique q is (p, 1).
    intro p hp
    use (p, 1)
    aesop;
  · native_decide;
  · exact ⟨ fun i j hij hj => by interval_cases j <;> interval_cases i <;> trivial, rfl ⟩

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_words := by
  exact?

lemma test8_postcondition :
  postcondition test8_words test8_Expected := by
  use [("dog", 2), ("cat", 2), ("bird", 1), ("fish", 1)];
  unfold isSortedByCountAndOccurrence; simp +decide ;
  -- Let's consider all possible pairs (i, j) where i < j and j < 4.
  intro i j hij hj
  interval_cases j <;> interval_cases i <;> simp +decide

----------------------------
-- Verification: test11
----------------------------
lemma test11_precondition :
  precondition test11_words := by
  trivial

lemma test11_postcondition :
  postcondition test11_words test11_Expected := by
  constructor;
  constructor;
  case w => exact [ ( "a", 3 ), ( "b", 2 ), ( "c", 2 ), ( "d", 1 ), ( "e", 1 ) ];
  · native_decide;
  · simp +decide [ isSortedByCountAndOccurrence ];
    intro i j hij hj; interval_cases j <;> interval_cases i <;> trivial;

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (words: List String):
  precondition words →
  (∀ ret1 ret2,
    postcondition words ret1 →
    postcondition words ret2 →
    ret1 = ret2) := by
  rintro - ret1 ret2 ⟨ sorted1, h1, h2, h3, h4, rfl ⟩ ⟨ sorted2, h5, h6, h7, h8, rfl ⟩;
  -- Since both sorted1 and sorted2 are sorted by count and first occurrence, and they contain the same elements (because they both satisfy the conditions), they must be permutations of each other. Therefore, their first four elements must be the same.
  have h_perm : sorted1.Perm sorted2 := by
    have h_perm : List.Nodup sorted1 ∧ List.Nodup sorted2 := by
      constructor;
      · rw [ List.nodup_iff_injective_get ];
        intro i j hij;
        have := h4 i j;
        contrapose! this;
        cases lt_or_gt_of_ne this <;> simp_all +decide [ Fin.ext_iff ];
        have := h4 _ _ ‹_› ( by simp ) ; aesop;
      · rw [ List.nodup_iff_count_le_one ];
        intro p; by_cases hp : p ∈ sorted2 <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
        rw [ List.count_eq_one_of_mem ];
        · rw [ List.nodup_iff_injective_get ];
          intros i j hij;
          by_contra h_neq;
          cases lt_or_gt_of_ne h_neq <;> have := h8 i j <;> simp_all +decide;
          have := h8 _ _ ‹_› ( by simp ) ; simp_all +decide [ Prod.ext_iff ] ;
        · assumption;
    have h_perm : List.toFinset sorted1 = List.toFinset sorted2 := by
      ext ⟨p, n⟩; simp [h1, h5];
      constructor <;> intro hp;
      · obtain ⟨ q, hq1, hq2 ⟩ := h6 p ( h3 _ hp );
        grind;
      · obtain ⟨ q, hq1, hq2 ⟩ := h2 p ( h7 _ hp );
        grind;
    rw [ List.perm_iff_count ];
    intro p; by_cases hp : p ∈ sorted1 <;> by_cases hp' : p ∈ sorted2 <;> simp_all +decide [ Finset.ext_iff ] ;
    · grind;
    · rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
  have h_sorted_eq : List.Sorted (fun p q => p.2 > q.2 ∨ (p.2 = q.2 ∧ firstIndex words p.1 < firstIndex words q.1)) sorted1 ∧ List.Sorted (fun p q => p.2 > q.2 ∨ (p.2 = q.2 ∧ firstIndex words p.1 < firstIndex words q.1)) sorted2 := by
    use ?_, ?_;
    · refine' List.pairwise_iff_get.mpr _;
      intro i j hij; specialize h4 i j hij; aesop;
    · refine' List.pairwise_iff_get.mpr _;
      intro i j hij; specialize h8 i j hij; aesop;
  have h_sorted_eq : sorted1 = sorted2 := by
    apply_rules [ List.eq_of_perm_of_sorted ];
    exact h_sorted_eq.1;
    · exact h_sorted_eq.2;
    · constructor;
      grind;
  rw [h_sorted_eq]
