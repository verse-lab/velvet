import Lean
import Mathlib.Tactic


-- Postcondition clauses
def ensures1 (lst : List Int) (result : List Int) :=
  result.Sublist lst ∧
  ∀ x,
    (x % 2 = 0 → result.count x = lst.count x) ∧
    (x % 2 ≠ 0 → result.count x = 0)

def precondition (lst: List Int) :=
  True

def postcondition (lst: List Int) (result: List Int) :=
  ensures1 lst result

-- Test Cases
def test1_lst : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def test1_Expected : List Int := [2, 4, 6, 8, 10]

def test2_lst : List Int := [2, 4, 6, 8]

def test2_Expected : List Int := [2, 4, 6, 8]

def test3_lst : List Int := [1, 3, 5, 7, 9]

def test3_Expected : List Int := []

def test7_lst : List Int := [-4, -3, -2, -1, 0, 1, 2]

def test7_Expected : List Int := [-4, -2, 0, 2]

def test8_lst : List Int := [2, 2, 3, 4, 4, 4]

def test8_Expected : List Int := [2, 2, 4, 4, 4]

def test12_lst : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

def test12_Expected : List Int := [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_lst := by
  trivial

lemma test1_postcondition :
  postcondition test1_lst test1_Expected := by
  simp [postcondition, ensures1, test1_lst, test1_Expected]
  constructor;
  · native_decide +revert;
  · intro x;
    by_cases h : x % 2 = 1 <;> simp_all +decide;
    · rw [ List.count_eq_zero ] ; aesop;
    · -- Since x is even, we can check each element in the lists to see if it matches x.
      by_cases hx : x = 2 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 10;
      · rcases hx with ( rfl | rfl | rfl | rfl | rfl ) <;> decide;
      · rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_lst := by
  trivial

lemma test2_postcondition :
  postcondition test2_lst test2_Expected := by
  simp [postcondition, ensures1, test2_lst, test2_Expected]
  grind

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_lst := by
  trivial

lemma test3_postcondition :
  postcondition test3_lst test3_Expected := by
  simp [postcondition, ensures1, test3_lst, test3_Expected]
  -- Since the list [1, 3, 5, 7, 9] contains no even numbers, the count of any even number x in this list is 0.
  intros x hx_even
  simp [List.count];
  -- Since x is even, it cannot be equal to any of the elements in the list [1, 3, 5, 7, 9], which are all odd.
  have h_not_in_list : x ≠ 1 ∧ x ≠ 3 ∧ x ≠ 5 ∧ x ≠ 7 ∧ x ≠ 9 := by
    aesop;
  -- Since x is not equal to any of the elements in the list [1, 3, 5, 7, 9], the count of x in this list is zero.
  simp [List.countP_cons, h_not_in_list];
  -- Since x is not equal to any of the elements in the list [1, 3, 5, 7, 9], each if statement evaluates to 0.
  simp [h_not_in_list, eq_comm]

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_lst := by
  trivial

lemma test7_postcondition :
  postcondition test7_lst test7_Expected := by
  simp [postcondition, ensures1, test7_lst, test7_Expected]
  -- Let's split into cases based on whether x is even or odd.
  intro x
  by_cases hx_even : 2 ∣ x;
  · grind;
  · grind

----------------------------
-- Verification: test8
----------------------------
lemma test8_precondition :
  precondition test8_lst := by
  trivial

lemma test8_postcondition :
  postcondition test8_lst test8_Expected := by
  simp [postcondition, ensures1, test8_lst, test8_Expected]
  -- Let's split into cases based on whether x is even or odd.
  intro x
  by_cases hx_even : 2 ∣ x;
  · grind;
  · grind

----------------------------
-- Verification: test12
----------------------------
lemma test12_precondition :
  precondition test12_lst := by
  trivial

lemma test12_postcondition :
  postcondition test12_lst test12_Expected := by
  simp [postcondition, ensures1, test12_lst, test12_Expected]
  simp +decide [ List.count_cons ];
  -- Let's simplify the goal.
  intro x
  by_cases hx : 2 ∣ x;
  · rcases hx with ⟨ k, rfl ⟩ ; norm_num [ Int.add_emod, Int.mul_emod ] ;
    grind;
  · grind

-----------------------------
-- Uniqueness Verification --
-----------------------------

lemma uniqueness (lst: List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  unfold postcondition;
  -- By definition of `ensures1`, both `ret1` and `ret2` must contain exactly the even numbers from `lst`.
  have h_even_sublists : ∀ (ret : List ℤ), ensures1 lst ret → ret = List.filter (fun x => x % 2 = 0) lst := by
    intro ret hret
    obtain ⟨h_sublist, h_count⟩ := hret
    have h_even_sublist : ret = List.filter (fun x => x % 2 = 0) lst := by
      refine' List.Sublist.eq_of_length_le _ _;
      · -- Since ret is a sublist of lst and contains only even numbers, it must be a sublist of the filtered list.
        have h_even_sublist : ∀ x ∈ ret, x % 2 = 0 := by
          exact fun x hx => Classical.not_not.1 fun hx' => absurd ( h_count x |>.2 hx' ) ( by linarith [ List.count_pos_iff.2 hx ] );
        have h_even_sublist : ret.Sublist (List.filter (fun x => x % 2 = 0) lst) := by
          have h_filter : ∀ {l : List ℤ}, (∀ x ∈ l, x % 2 = 0) → l.Sublist (List.filter (fun x => x % 2 = 0) l) := by
            intros l hl; induction l <;> aesop
          exact List.Sublist.trans ( h_filter h_even_sublist ) ( List.Sublist.filter _ h_sublist );
        assumption;
      · have h_even_sublist : List.length (List.filter (fun x => x % 2 = 0) lst) = ∑ x ∈ lst.toFinset, (List.count x lst) * (if x % 2 = 0 then 1 else 0) := by
          have h_even_sublist : ∀ (l : List ℤ), List.length (List.filter (fun x => x % 2 = 0) l) = ∑ x ∈ l.toFinset, (List.count x l) * (if x % 2 = 0 then 1 else 0) := by
            intros l
            induction' l with x l ih;
            · rfl;
            · by_cases hx : x ∈ l <;> simp_all +decide [ List.count_cons ];
              · by_cases h : 2 ∣ x <;> simp_all +decide [ Finset.sum_add_distrib, Finset.sum_ite ];
              · split_ifs <;> simp_all +decide [ List.count_eq_zero_of_not_mem ];
                · rw [ add_comm, Finset.sum_congr rfl ] ; aesop;
                · exact Finset.sum_congr rfl fun y hy => by aesop;
          apply h_even_sublist;
        have h_even_sublist : List.length ret = ∑ x ∈ lst.toFinset, (List.count x ret) := by
          have h_even_sublist : ∀ (l : List ℤ), List.length l = ∑ x ∈ l.toFinset, (List.count x l) := by
            exact?;
          rw [ h_even_sublist, Finset.sum_subset ];
          · exact fun x hx => by have := h_sublist.subset ( List.mem_toFinset.mp hx ) ; exact List.mem_toFinset.mpr this;
          · simp +contextual [ List.count_eq_zero ];
        grind
    exact h_even_sublist;
  exact fun _ ret1 ret2 h1 h2 => h_even_sublists ret1 h1 ▸ h_even_sublists ret2 h2 ▸ rfl
