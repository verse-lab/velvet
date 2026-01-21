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
    isPerfectSquare: determine whether a natural number is a perfect square
    Natural language breakdown:
    1. The input n is a natural number (so it is non-negative).
    2. The output is a Boolean value.
    3. The output should be true exactly when there exists a natural number k such that k*k = n.
    4. The output should be false exactly when there is no natural number k such that k*k = n.
    5. Edge cases: 0 and 1 are perfect squares.
    6. Examples: 4, 9, 16, 25 are perfect squares; 2, 3, 10, 26 are not.
-/

section Specs
-- A natural number n is a perfect square iff it is the square of some natural number.
-- We use k*k rather than k^2 to keep the predicate simple.
def IsSquareNat (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

-- No preconditions.
def precondition (n : Nat) : Prop :=
  True

-- Postcondition: the boolean result reflects existence of a square root in Nat.
-- Two clauses together uniquely determine the Bool result.
def postcondition (n : Nat) (result : Bool) : Prop :=
  (result = true ↔ IsSquareNat n) ∧
  (result = false ↔ ¬ IsSquareNat n)
end Specs

section Impl
method isPerfectSquare (n : Nat) return (result : Bool)
  require precondition (n)
  ensures postcondition (n) (result)
  do
    let mut k : Nat := 0
    let mut isSq : Bool := false
    while k * k <= n ∧ isSq = false
      -- k is a Nat, so it is always nonnegative; keeping it explicit helps arithmetic/bounds reasoning.
      invariant "inv_k_bound" k ≤ n + 1
      -- If we have set the flag, then we have found a witness square root.
      invariant "inv_true_witness" (isSq = true → IsSquareNat n)
      -- While the flag is still false, all tested values 0..k-1 were not square roots.
      invariant "inv_false_no_prev_root" (isSq = false → ∀ j : Nat, j < k → j * j ≠ n)
      done_with (k * k > n ∨ isSq = true)
    do
      if k * k = n then
        isSq := true
      else
        k := k + 1
    return isSq
end Impl

section TestCases
-- Test case 1: example from prompt: n=0 is a perfect square (0*0)
def test1_n : Nat := 0
def test1_Expected : Bool := true

-- Test case 2: n=1 is a perfect square (1*1)
def test2_n : Nat := 1
def test2_Expected : Bool := true

-- Test case 3: n=4 is a perfect square (2*2)
def test3_n : Nat := 4
def test3_Expected : Bool := true

-- Test case 4: n=9 is a perfect square (3*3)
def test4_n : Nat := 9
def test4_Expected : Bool := true

-- Test case 5: n=2 is not a perfect square
def test5_n : Nat := 2
def test5_Expected : Bool := false

-- Test case 6: n=3 is not a perfect square
def test6_n : Nat := 3
def test6_Expected : Bool := false

-- Test case 7: n=10 is not a perfect square
def test7_n : Nat := 10
def test7_Expected : Bool := false

-- Test case 8: n=16 is a perfect square (4*4)
def test8_n : Nat := 16
def test8_Expected : Bool := true

-- Test case 9: n=25 is a perfect square (5*5)
def test9_n : Nat := 25
def test9_Expected : Bool := true

-- Test case 10: n=26 is not a perfect square
def test10_n : Nat := 26
def test10_Expected : Bool := false

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test5, test8
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((isPerfectSquare test1_n).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((isPerfectSquare test2_n).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((isPerfectSquare test3_n).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((isPerfectSquare test4_n).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((isPerfectSquare test5_n).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((isPerfectSquare test6_n).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((isPerfectSquare test7_n).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((isPerfectSquare test8_n).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((isPerfectSquare test9_n).run), DivM.res test9_Expected ]

-- Test case 10

#assert_same_evaluation #[((isPerfectSquare test10_n).run), DivM.res test10_Expected ]
end Assertions

section Pbt
-- PBT disabled due to build error:
-- [ERROR] Line 148, Column 0
-- Message: unsolved goals
-- case refine_1
-- n : ℕ
-- result : Bool
-- ⊢ Decidable (result = true ↔ IsSquareNat n)
-- 
-- case refine_2
-- n : ℕ
-- result : Bool
-- ⊢ Decidable (result = false ↔ ¬IsSquareNat n)
-- Line: prove_postcondition_decidable_for isPerfectSquare
-- [ERROR] Line 150, Column 0
-- Message: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-- 
-- To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-- Line: run_elab do

-- extract_program_for isPerfectSquare
-- prove_precondition_decidable_for isPerfectSquare
-- prove_postcondition_decidable_for isPerfectSquare
-- derive_tester_for isPerfectSquare
-- run_elab do
--   let g : Plausible.Gen (_ × Bool) := do
--     let arg_0 ← Plausible.SampleableExt.interpSample (Nat)
--     let res := isPerfectSquareTester arg_0
--     pure ((arg_0), res)
--   for _ in [1: 200] do
--     let res ← Plausible.Gen.run g 20
--     unless res.2 do
--       IO.println s!"Postcondition violated for input {res.1}"
--       break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct isPerfectSquare by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (n : ℕ)
    (k : ℕ)
    (if_pos : k * k = n)
    : IsSquareNat n := by
    refine ⟨k, ?_⟩
    simpa [if_pos]

theorem goal_1
    (n : ℕ)
    (isSq : Bool)
    (k : ℕ)
    (invariant_inv_k_bound : k ≤ n + 1)
    (invariant_inv_false_no_prev_root : isSq = false → ∀ j < k, ¬j * j = n)
    (a : k * k ≤ n)
    (if_neg : ¬k * k = n)
    : k ≤ n := by
    cases k with
    | zero =>
        simp
    | succ k' =>
        have hk_le_hk_sq : Nat.succ k' ≤ Nat.succ k' * Nat.succ k' := by
          -- k'+1 ≤ (k'+1)^2, since 1 ≤ k'+1 and multiply on the left by (k'+1)
          have h1 : (1 : Nat) ≤ Nat.succ k' := by
            simp
          simpa [Nat.mul_one, Nat.mul_assoc] using (Nat.mul_le_mul_left (Nat.succ k') h1)
        exact le_trans hk_le_hk_sq a

theorem goal_2
    (n : ℕ)
    (isSq : Bool)
    (k : ℕ)
    (invariant_inv_false_no_prev_root : isSq = false → ∀ j < k, ¬j * j = n)
    (if_neg : ¬k * k = n)
    : isSq = false → ∀ j < k + 1, ¬j * j = n := by
  intro hfalse
  intro j hj
  have hj' : j < k ∨ j = k := by
    -- `k + 1 = Nat.succ k`
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.lt_add_one_iff_lt_or_eq (m := j) (n := k)).1 hj
  cases hj' with
  | inl hjlt =>
      exact (invariant_inv_false_no_prev_root hfalse) j hjlt
  | inr hjeq =>
      simpa [hjeq] using if_neg

theorem goal_3
    (n : ℕ)
    (isSq : Bool)
    (k : ℕ)
    (invariant_inv_true_witness : isSq = true → IsSquareNat n)
    (invariant_inv_false_no_prev_root : isSq = false → ∀ j < k, ¬j * j = n)
    (i : Bool)
    (k_1 : ℕ)
    (done_1 : n < k * k ∨ isSq = true)
    (i_1 : isSq = i ∧ k = k_1)
    : postcondition n i := by
    rcases i_1 with ⟨hisq_i, hk_k1⟩
    -- rewrite the returned value `i` to `isSq`
    subst hisq_i
    unfold postcondition
    constructor
    · -- (isSq = true ↔ IsSquareNat n)
      constructor
      · intro htrue
        exact invariant_inv_true_witness htrue
      · intro hSq
        cases done_1 with
        | inr htrue =>
            exact htrue
        | inl hnlt =>
            -- if we stopped because n < k*k, then `isSq` must still be false;
            -- but then the "no previous root" invariant contradicts any square witness
            by_contra hne_true
            have hfalse : isSq = false := by
              cases hbe : isSq with
              | false => simpa [hbe]
              | true =>
                  exfalso
                  exact hne_true (by simpa [hbe])
            rcases hSq with ⟨t, ht⟩
            have htlt : t * t < k * k := by
              simpa [ht] using hnlt
            have htk : t < k :=
              (Nat.mul_self_lt_mul_self_iff).1 htlt
            have hno : ¬ t * t = n :=
              (invariant_inv_false_no_prev_root hfalse) t htk
            exact hno (by simpa [ht])
    · -- (isSq = false ↔ ¬ IsSquareNat n)
      constructor
      · intro hfalse
        intro hSq
        cases done_1 with
        | inr htrue =>
            -- contradiction: isSq can't be both false and true
            have : False := by
              have : (false : Bool) = true := by
                calc
                  (false : Bool) = isSq := by simpa [hfalse] using (rfl : isSq = isSq).symm
                  _ = true := by simpa using htrue
              exact Bool.noConfusion this
            exact this.elim
        | inl hnlt =>
            rcases hSq with ⟨t, ht⟩
            have htlt : t * t < k * k := by
              simpa [ht] using hnlt
            have htk : t < k :=
              (Nat.mul_self_lt_mul_self_iff).1 htlt
            have hno : ¬ t * t = n :=
              (invariant_inv_false_no_prev_root hfalse) t htk
            exact hno (by simpa [ht])
      · intro hnotSq
        -- if isSq were true, invariant gives a witness, contradicting ¬IsSquareNat n
        by_contra hne_false
        have htrue : isSq = true := by
          cases hbe : isSq with
          | true => simpa [hbe]
          | false =>
              exfalso
              exact hne_false (by simpa [hbe])
        have hs : IsSquareNat n := invariant_inv_true_witness htrue
        exact hnotSq hs


prove_correct isPerfectSquare by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 n k if_pos)
  exact (goal_1 n isSq k invariant_inv_k_bound invariant_inv_false_no_prev_root a if_neg)
  exact (goal_2 n isSq k invariant_inv_false_no_prev_root if_neg)
  exact (goal_3 n isSq k invariant_inv_true_witness invariant_inv_false_no_prev_root i k_1 done_1 i_1)
end Proof
