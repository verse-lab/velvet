import Lean
import Mathlib.Tactic


namespace VerinaSpec

@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  True

-- !benchmark @end precond

@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  -- !benchmark @start postcond
  let evens := result.fst
  let odds := result.snd
  -- All elements from nums are in evens ++ odds, no extras
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)

-- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Predicate: a natural number is even
def isEven (n : Nat) : Bool := n % 2 = 0

-- Predicate: a natural number is odd
def isOdd (n : Nat) : Bool := n % 2 ≠ 0

-- Postcondition: result.1 contains exactly the even numbers from nums in order
-- and result.2 contains exactly the odd numbers from nums in order
def ensures1 (nums : List Nat) (result : List Nat × List Nat) :=
  result.1.Sublist nums ∧ result.2.Sublist nums

-- All elements in first list are even, all in second are odd
def ensures2 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ result.1, x % 2 = 0) ∧ (∀ x ∈ result.2, x % 2 ≠ 0)

-- Every even element from nums is in result.1, every odd element is in result.2
def ensures3 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x ∈ nums, x % 2 = 0 → x ∈ result.1) ∧
  (∀ x ∈ nums, x % 2 ≠ 0 → x ∈ result.2)

-- Counts are preserved
def ensures4 (nums : List Nat) (result : List Nat × List Nat) :=
  (∀ x, x % 2 = 0 → result.1.count x = nums.count x) ∧
  (∀ x, x % 2 ≠ 0 → result.2.count x = nums.count x)

def precondition (nums : List Nat) :=
  nums.Nodup

-- no duplicates in input

def postcondition (nums : List Nat) (result : List Nat × List Nat) :=
  ensures1 nums result ∧ ensures2 nums result ∧ ensures3 nums result ∧ ensures4 nums result

end LeetProofSpec

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Equivalence theorems
-/
theorem precondition_equiv (nums : List Nat):
  VerinaSpec.partitionEvensOdds_precond nums ↔ LeetProofSpec.precondition nums := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any `nums` such that `nums` contains duplicates.
  use [1, 2, 2, 3];
  -- Let's simplify the goal.
  simp [VerinaSpec.partitionEvensOdds_precond, LeetProofSpec.precondition]

-/
-- Equivalence theorems

theorem precondition_equiv (nums : List Nat):
  VerinaSpec.partitionEvensOdds_precond nums ↔ LeetProofSpec.precondition nums := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



def postcondition_equiv : False := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Prove that Lemma 25 holds for r = 4.
  simp [Finset.card_univ] at *

-/
noncomputable section AristotleLemmas

/-
If two lists are concatenated to form the same list, and the first parts satisfy a predicate `p` while the second parts satisfy `¬p`, then the split is unique.
-/
theorem list_split_unique {α} (l1 l2 l3 l4 : List α) (p : α → Bool)
  (h_eq : l1 ++ l2 = l3 ++ l4)
  (h1 : ∀ x ∈ l1, p x) (h2 : ∀ x ∈ l2, ¬ p x)
  (h3 : ∀ x ∈ l3, p x) (h4 : ∀ x ∈ l4, ¬ p x) :
  l1 = l3 ∧ l2 = l4 := by
    induction' l1 with x l1 ih generalizing l3 <;> induction' l3 with y l3 ih' <;> aesop

/-
If a sublist contains all elements of the original list that satisfy `p` (preserving counts) and contains only elements satisfying `p`, then it must be equal to `filter p`. This requires `DecidableEq` for `count`.
-/
theorem list_filter_unique_sublist {α} [DecidableEq α] (l sub : List α) (p : α → Bool)
  (h_sub : List.Sublist sub l)
  (h_all : ∀ x ∈ sub, p x)
  (h_count : ∀ x, p x → sub.count x = l.count x) :
  sub = l.filter p := by
    refine' List.Sublist.antisymm _ _;
    · induction h_sub ; aesop;
      · by_cases h : p ‹_› <;> simp_all +decide [ List.count_cons ];
        · grind;
        · exact ‹ ( ∀ x, p x = Bool.true → ¬_ ) → List.Sublist _ _ › fun x hx => by aesop;
      · simp_all +decide [ List.count_cons ];
    · -- Since `sub` is a sublist of `l` and contains exactly the elements of `l` that satisfy `p`, we can conclude that `sub` is a permutation of `filter p l`.
      have h_perm : List.Perm sub (List.filter p l) := by
        rw [ List.perm_iff_count ];
        intro x; by_cases hx : p x <;> simp_all +decide [ List.countP_eq_length_filter ] ;
        rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
      have h_perm_sublist : List.Perm sub (List.filter p l) → List.Sublist (List.filter p l) sub := by
        intro h_perm
        have h_perm_sublist : List.Sublist (List.filter p l) sub := by
          have h_perm_sublist : ∀ {l1 l2 : List α}, List.Perm l1 l2 → List.Sublist l1 l2 → List.Sublist l2 l1 := by
            intros l1 l2 h_perm h_sublist;
            have h_perm_sublist : ∀ {l1 l2 : List α}, List.Perm l1 l2 → List.Sublist l1 l2 → l1 = l2 := by
              intros l1 l2 h_perm h_sublist; exact List.Sublist.eq_of_length_le h_sublist (by simp [h_perm.length_eq]);
            rw [ h_perm_sublist h_perm h_sublist ]
          apply h_perm_sublist;
          · assumption;
          · convert h_sub.filter p using 1;
            rw [ List.filter_eq_self.mpr ] ; aesop;
        exact h_perm_sublist;
      exact h_perm_sublist h_perm

end AristotleLemmas

def postcondition_equiv (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : VerinaSpec.partitionEvensOdds_precond (nums)) :
  VerinaSpec.partitionEvensOdds_postcond nums result h_precond ↔ LeetProofSpec.postcondition nums result := by
  constructor;
  · intro h;
    -- By definition of `VerinaSpec.partitionEvensOdds_postcond`, we know that `result.1` and `result.2` are the even and odd lists from `nums`, respectively.
    obtain ⟨heven, hodd⟩ : result.1 = nums.filter (fun n => n % 2 == 0) ∧ result.2 = nums.filter (fun n => n % 2 == 1) := by
      have := list_split_unique _ _ _ _ ( fun n => n % 2 == 0 ) h.1 ?_ ?_ ?_ ?_ <;> aesop;
    constructor;
    · constructor <;> aesop;
    · unfold LeetProofSpec.ensures2 LeetProofSpec.ensures3 LeetProofSpec.ensures4; aesop;
  · intro h_leet
    obtain ⟨h_sub, h_all_even, h_all_odd, h_count⟩ := h_leet;
    -- By `list_filter_unique_sublist`, we know that `result.1 = nums.filter (fun n => n % 2 == 0)` and `result.2 = nums.filter (fun n => n % 2 == 1)`.
    have h_filter_unique : result.1 = nums.filter (fun n => n % 2 == 0) ∧ result.2 = nums.filter (fun n => n % 2 == 1) := by
      apply And.intro;
      · apply list_filter_unique_sublist;
        · exact h_sub.1;
        · exact fun x hx => by simpa using h_all_even.1 x hx;
        · exact fun x hx => h_count.1 x <| by simpa using hx;
      · apply list_filter_unique_sublist;
        · exact h_sub.2;
        · exact fun x hx => by have := h_all_even.2 x hx; aesop;
        · exact fun x hx => h_count.2 x ( by simpa using hx );
    unfold VerinaSpec.partitionEvensOdds_postcond; aesop;
