import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isSortedNonDecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

def occurs (arr : Array Int) (target : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = target

def intIndexInBounds (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ (idx.toNat) < arr.size



def precondition (arr : Array Int) (target : Int) : Prop :=
  isSortedNonDecreasing arr




def postcondition (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = (-1) ↔ ¬ occurs arr target) ∧
  (result ≠ (-1) →
    intIndexInBounds arr result ∧
    arr[result.toNat]! = target ∧
    (∀ (j : Nat), j < result.toNat → arr[j]! ≠ target))


def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]

def test1_target : Int := 2

def test1_Expected : Int := 1

def test6_arr : Array Int := #[]

def test6_target : Int := 10

def test6_Expected : Int := (-1)

def test8_arr : Array Int := #[-5, -3, -3, 0, 2]

def test8_target : Int := (-3)

def test8_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_arr test1_target := by
  -- Step 1: unfold `precondition`; it suffices to prove `isSortedNonDecreasing test1_arr`
  have h_sorted : isSortedNonDecreasing test1_arr := by
    -- Step 2: unfold the definition of sortedness
    intro i j hij hj
    -- Step 2 (concrete size): `test1_arr.size = 6`, hence `j < 6`
    have hsize : test1_arr.size = 6 := by
      simp [test1_arr]
    have hj6 : j < 6 := by
      simpa [hsize] using hj
    -- Step 4: split on the finite possibilities for `j` (since `j < 6`)
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
      omega
    cases hj_cases with
    | inl hj0 =>
      -- j = 0 contradicts i < j
      subst hj0
      have hFalse : False := by
        omega
      exact False.elim hFalse
    | inr hj_rest =>
      cases hj_rest with
      | inl hj1 =>
        subst hj1
        -- then i = 0; check arr[0] ≤ arr[1]
        have hi0 : i = 0 := by
          omega
        subst hi0
        simpa [test1_arr]
      | inr hj_rest2 =>
        cases hj_rest2 with
        | inl hj2 =>
          subst hj2
          -- then i = 0 or 1; check each directly
          have hi_cases : i = 0 ∨ i = 1 := by
            omega
          cases hi_cases with
          | inl hi0 => subst hi0; simpa [test1_arr]
          | inr hi1 => subst hi1; simpa [test1_arr]
        | inr hj_rest3 =>
          cases hj_rest3 with
          | inl hj3 =>
            subst hj3
            -- then i = 0 or 1 or 2; check each directly
            have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
              omega
            cases hi_cases with
            | inl hi0 => subst hi0; simpa [test1_arr]
            | inr hi12 =>
              cases hi12 with
              | inl hi1 => subst hi1; simpa [test1_arr]
              | inr hi2 => subst hi2; simpa [test1_arr]
          | inr hj_rest4 =>
            cases hj_rest4 with
            | inl hj4 =>
              subst hj4
              -- then i = 0 or 1 or 2 or 3; check each directly
              have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
                omega
              cases hi_cases with
              | inl hi0 => subst hi0; simpa [test1_arr]
              | inr hi123 =>
                cases hi123 with
                | inl hi1 => subst hi1; simpa [test1_arr]
                | inr hi23 =>
                  cases hi23 with
                  | inl hi2 => subst hi2; simpa [test1_arr]
                  | inr hi3 => subst hi3; simpa [test1_arr]
            | inr hj5 =>
              subst hj5
              -- then i = 0 or 1 or 2 or 3 or 4; check each directly
              have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
                omega
              cases hi_cases with
              | inl hi0 => subst hi0; simpa [test1_arr]
              | inr hi1234 =>
                cases hi1234 with
                | inl hi1 => subst hi1; simpa [test1_arr]
                | inr hi234 =>
                  cases hi234 with
                  | inl hi2 => subst hi2; simpa [test1_arr]
                  | inr hi34 =>
                    cases hi34 with
                    | inl hi3 => subst hi3; simpa [test1_arr]
                    | inr hi4 => subst hi4; simpa [test1_arr]
  -- Step 5: conclude the original goal
  simpa [precondition] using h_sorted

theorem test1_postcondition_0
    (h_goal_simp : postcondition test1_arr test1_target test1_Expected = postcondition test1_arr 2 1)
    : (1 = -1) = False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition :
  postcondition test1_arr test1_target test1_Expected := by
  -- Step 1: unfold concrete inputs and reduce the goal to the concrete postcondition
  have h_goal_simp :
      postcondition test1_arr test1_target test1_Expected =
        postcondition test1_arr (2 : Int) (1 : Int) := by
    simp [test1_target, test1_Expected]
  -- We will work directly with the unfolded form for `arr = test1_arr`, `target = 2`, `result = 1`.
  -- Step 2: unfold `postcondition` and prove both conjuncts
  refine And.intro ?h1 ?h2

  · -- Step 3: first conjunct: (1 = -1 ↔ ¬ occurs test1_arr 2)
    have h_eq_false : ((1 : Int) = (-1 : Int)) = False := by
      (try simp at *; expose_names); exact (test1_postcondition_0 h_goal_simp); done
    have h_size : test1_arr.size = 6 := by
      (try simp at *; expose_names); exact rfl; done
    have h_occurs : occurs test1_arr (2 : Int) := by
      refine ⟨1, ?_, ?_⟩
      have h1lt6 : (1 : Nat) < 6 := by
        (try simp at *; expose_names); exact Nat.one_lt_succ_succ 4; done
      · -- bounds
        simpa [h_size] using h1lt6
      · -- value at index 1
        simp [test1_arr]
    have h_not_occurs_false : (¬ occurs test1_arr (2 : Int)) = False := by
      (try simp at *; expose_names); exact h_occurs; done
    -- conclude the ↔ by rewriting both sides to False
    have h_iff : ((1 : Int) = (-1 : Int) ↔ ¬ occurs test1_arr (2 : Int)) := by
      -- rewrite the propositions by the equalities to False, then close
      -- (this stays as a sketch step)
      (try simp at *; expose_names); exact h_occurs; done
    exact h_iff

  · -- Step 4: second conjunct:
    --   1 ≠ -1 → intIndexInBounds test1_arr 1 ∧ arr[1.toNat]! = 2 ∧ ∀ j < 1.toNat, arr[j]! ≠ 2
    intro hne
    have h_size : test1_arr.size = 6 := by
      (try simp at *; expose_names); exact rfl; done
    have h_toNat : (1 : Int).toNat = 1 := by
      (try simp at *; expose_names); exact rfl; done
    have h_nonneg : (0 : Int) ≤ (1 : Int) := by
      (try simp at *; expose_names); exact Int.one_nonneg; done
    have h_toNat_lt_size : (1 : Int).toNat < test1_arr.size := by
      have h1lt6 : (1 : Nat) < 6 := by
        (try simp at *; expose_names); exact Nat.one_lt_succ_succ 4; done
      simpa [h_toNat, h_size] using h1lt6
    have h_inBounds : intIndexInBounds test1_arr (1 : Int) := by
      -- unfold intIndexInBounds := 0 ≤ idx ∧ idx.toNat < arr.size
      -- and assemble the pair from the two facts above
      simpa [intIndexInBounds] using And.intro h_nonneg h_toNat_lt_size
    have h_at_idx : test1_arr[(1 : Int).toNat]! = (2 : Int) := by
      -- reduce to index 1 and compute in the concrete array
      simpa [h_toNat, test1_arr]
    have h_min : ∀ (j : Nat), j < (1 : Int).toNat → test1_arr[j]! ≠ (2 : Int) := by
      intro j hj
      have hj' : j < 1 := by
        simpa [h_toNat] using hj
      have hj0 : j = 0 := by
        -- only Nat < 1 is 0
        (try simp at *; expose_names); exact hj; done
      subst hj0
      -- compute array[0]! = 1 ≠ 2
      simp [test1_arr]
    refine And.intro h_inBounds ?_
    refine And.intro h_at_idx ?_
    exact h_min

theorem test6_precondition :
  precondition test6_arr test6_target := by
  unfold precondition
  unfold isSortedNonDecreasing
  intro i j hij hj
  simp [test6_arr, Array.size_empty] at hj

theorem test6_postcondition :
  postcondition test6_arr test6_target test6_Expected := by
  -- expand postcondition; keep the two conjuncts as goals
  refine And.intro ?_ ?_
  · -- (result = -1 ↔ ¬ occurs arr target)
    -- reduce to showing ¬ occurs on the empty array
    have hno : ¬ occurs test6_arr test6_target := by
      intro hocc
      rcases hocc with ⟨i, hi, _⟩
      -- test6_arr is empty, so size = 0, contradiction with i < 0
      have : i < 0 := by simpa [test6_arr] using hi
      exact (Nat.not_lt_zero i) this
    -- now simplify using result = -1
    simpa [postcondition, test6_Expected, test6_target, hno]
  · -- (result ≠ -1 → ...)
    -- antecedent is false since result = -1
    intro hne
    exfalso
    exact hne (by simp [test6_Expected])

theorem test8_precondition :
  precondition test8_arr test8_target := by
  unfold precondition
  intro i j hij hj
  -- `simp` will compute `test8_arr.size` and the array entries at concrete indices.
  -- Then `omega`/`decide` can finish the resulting linear arithmetic on `Nat` and `Int`.
  have hj' : j < 5 := by simpa [test8_arr] using hj
  have hij' : i < j := hij
  -- enumerate the finite possibilities for `j` and `i`
  have : (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exfalso; omega
  · -- j = 1, so i = 0
    have : i = 0 := by omega
    subst this
    simp [isSortedNonDecreasing, test8_arr]
  · -- j = 2, so i = 0 or 1
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [isSortedNonDecreasing, test8_arr]
  · -- j = 3, so i = 0 or 1 or 2
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [isSortedNonDecreasing, test8_arr]
  · -- j = 4, so i = 0 or 1 or 2 or 3
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [isSortedNonDecreasing, test8_arr]

theorem test8_postcondition_0
    (hne : ¬test8_Expected = -1)
    (h_size : test8_arr.size = 5)
    (h_toNat_lt_size : 1 < test8_arr.size)
    (h_goal_simp : postcondition test8_arr test8_target test8_Expected ↔ postcondition test8_arr (-3) 1)
    (h_nonneg : True)
    (h_toNat : True)
    : intIndexInBounds test8_arr 1 := by
    unfold intIndexInBounds
    constructor
    · simpa using (Int.one_nonneg : (0 : Int) ≤ 1)
    · simpa using h_toNat_lt_size

theorem test8_postcondition :
  postcondition test8_arr test8_target test8_Expected := by
  -- Step 1: unfold concrete target/expected; keep `test8_arr` as the concrete array
  have h_goal_simp : postcondition test8_arr test8_target test8_Expected = postcondition test8_arr (-3 : Int) (1 : Int) := by
    (try simp at *; expose_names); exact Eq.to_iff rfl; done

  -- Step 2: unfold `postcondition` and split into the two required conjuncts
  refine And.intro ?h1 ?h2

  · -- Step 3: first conjunct: (1 = -1 ↔ ¬ occurs test8_arr (-3))
    have h_ne : (1 : Int) ≠ (-1 : Int) := by
      (try simp at *; expose_names); exact not_eq_of_beq_eq_false rfl; done
    have h_size : test8_arr.size = 5 := by
      (try simp at *; expose_names); exact rfl; done
    have h_occurs : occurs test8_arr (-3 : Int) := by
      refine ⟨1, ?_, ?_⟩
      · have h1lt5 : (1 : Nat) < 5 := by
          (try simp at *; expose_names); exact Nat.one_lt_succ_succ 3; done
        simpa [h_size] using h1lt5
      · -- compute the concrete array entry at index 1
        simp [test8_arr]
    have h_not_occurs : ¬ occurs test8_arr (-3 : Int) = False := by
      (try simp at *; expose_names); exact h_occurs; done
    have h_eq_neg1 : ((1 : Int) = (-1 : Int)) = False := by
      (try simp at *; expose_names); exact test1_postcondition_0 rfl; done
    have h_iff : ((1 : Int) = (-1 : Int) ↔ ¬ occurs test8_arr (-3 : Int)) := by
      (try simp at *; expose_names); exact h_occurs; done
    exact h_iff

  · -- Step 4: second conjunct: 1 ≠ -1 → inBounds ∧ correct value ∧ minimality
    intro hne
    have h_nonneg : (0 : Int) ≤ (1 : Int) := by
      (try simp at *; expose_names); exact Int.one_nonneg; done
    have h_toNat : (1 : Int).toNat = 1 := by
      (try simp at *; expose_names); exact rfl; done
    have h_size : test8_arr.size = 5 := by
      (try simp at *; expose_names); exact rfl; done
    have h_toNat_lt_size : (1 : Int).toNat < test8_arr.size := by
      (try simp at *; expose_names); exact Nat.one_lt_succ_succ [-3, 0, 2].length; done
    have h_inBounds : intIndexInBounds test8_arr (1 : Int) := by
      (try simp at *; expose_names); exact (test8_postcondition_0 hne h_size h_toNat_lt_size h_goal_simp h_nonneg h_toNat); done
    have h_at_idx : test8_arr[(1 : Int).toNat]! = (-3 : Int) := by
      (try simp at *; expose_names); exact rfl; done
    have h_min : ∀ (j : Nat), j < (1 : Int).toNat → test8_arr[j]! ≠ (-3 : Int) := by
      intro j hj
      have hj1 : j < 1 := by
        (try simp at *; expose_names); exact hj; done
      have hj0 : j = 0 := by
        (try simp at *; expose_names); exact hj; done
      subst hj0
      simp [test8_arr]
    refine And.intro h_inBounds ?_
    refine And.intro h_at_idx ?_
    exact h_min

theorem uniqueness_0
    (arr : Array ℤ)
    (target : ℤ)
    (hpre : precondition arr target)
    (ret1 : ℤ)
    (ret2 : ℤ)
    (hpost1 : postcondition arr target ret1)
    (hpost2 : postcondition arr target ret2)
    (hsorted : isSortedNonDecreasing arr)
    (hpost1_neg1 : ret1 = -1 ↔ ¬occurs arr target)
    (hpost2_neg1 : ret2 = -1 ↔ ¬occurs arr target)
    (hneg1_iff : ret1 = -1 ↔ ret2 = -1)
    (hret1neg1 : ¬ret1 = -1)
    (hret1ne : ¬ret1 = -1)
    (hpost1_imp : ¬ret1 = -1 → intIndexInBounds arr ret1 ∧ arr[ret1.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ret1 → ¬arr[j]! = target)
    (hpost2_imp : ¬ret2 = -1 → intIndexInBounds arr ret2 ∧ arr[ret2.toNat]! = target ∧ ∀ (j : ℕ), ↑j < ret2 → ¬arr[j]! = target)
    : occurs arr target := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (arr : Array Int) (target : Int):
  precondition arr target →
  (∀ ret1 ret2,
    postcondition arr target ret1 →
    postcondition arr target ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2

  -- Step 2: unfold precondition (sortedness is not needed for uniqueness, but we unpack it per plan)
  have hsorted : isSortedNonDecreasing arr := by
    simpa [precondition] using hpre

  -- Step 3: extract the two main parts of each postcondition
  have hpost1_neg1 : (ret1 = (-1) ↔ ¬ occurs arr target) := by
    exact hpost1.left
  have hpost2_neg1 : (ret2 = (-1) ↔ ¬ occurs arr target) := by
    exact hpost2.left
  have hpost1_imp : (ret1 ≠ (-1) → intIndexInBounds arr ret1 ∧ arr[ret1.toNat]! = target ∧ (∀ (j : Nat), j < ret1.toNat → arr[j]! ≠ target)) := by
    exact hpost1.right
  have hpost2_imp : (ret2 ≠ (-1) → intIndexInBounds arr ret2 ∧ arr[ret2.toNat]! = target ∧ (∀ (j : Nat), j < ret2.toNat → arr[j]! ≠ target)) := by
    exact hpost2.right

  -- Step 5: derive a clean equivalence ret1=-1 ↔ ret2=-1 via the shared proposition ¬ occurs
  have hneg1_iff : (ret1 = (-1) ↔ ret2 = (-1)) := by
    have : (ret1 = (-1) ↔ ¬ occurs arr target) ∧ (ret2 = (-1) ↔ ¬ occurs arr target) := by
      exact And.intro hpost1_neg1 hpost2_neg1
    -- use transitivity/symmetry of ↔
    -- (ret1=-1 ↔ ¬occurs) and (ret2=-1 ↔ ¬occurs) gives (ret1=-1 ↔ ret2=-1)
    -- sketch: (hpost1_neg1.trans hpost2_neg1.symm)
    (try simp at *; expose_names); exact Iff.trans hpost1_neg1 (id (Iff.symm hpost2_neg1)); done

  -- Step 6/7: case split on whether ret1 = -1
  by_cases hret1neg1 : ret1 = (-1)
  · -- Case 1: ret1 = -1, then ret2 = -1, so ret1 = ret2
    have hret2neg1 : ret2 = (-1) := by
      have : ret1 = (-1) ↔ ret2 = (-1) := hneg1_iff
      exact (this.mp hret1neg1)
    calc
      ret1 = (-1) := hret1neg1
      _ = ret2 := by simpa [hret2neg1]
  · -- Case 2: ret1 ≠ -1, show ret2 ≠ -1, then compare toNat indices and lift to Int equality
    have hret1ne : ret1 ≠ (-1) := by
      exact hret1neg1

    have hoccurs : occurs arr target := by
      -- from (ret1=-1 ↔ ¬occurs) and ret1≠-1, derive occurs
      -- sketch: have ¬(¬occurs) then classical by_contra
      (try simp at *; expose_names); exact (uniqueness_0 arr target hpre ret1 ret2 hpost1 hpost2 hsorted hpost1_neg1 hpost2_neg1 hneg1_iff hret1neg1 hret1ne hpost1_imp hpost2_imp); done

    have hret2ne : ret2 ≠ (-1) := by
      -- if ret2 = -1 then ¬occurs, contradict hoccurs
      intro hret2neg1
      have hno : ¬ occurs arr target := by
        exact (hpost2_neg1.mp hret2neg1)
      exact hno hoccurs

    -- Step 8: apply the implication parts to obtain bounds/value/minimality (Nat-based!)
    have hspec1 : intIndexInBounds arr ret1 ∧ arr[ret1.toNat]! = target ∧ (∀ (j : Nat), j < ret1.toNat → arr[j]! ≠ target) := by
      exact hpost1_imp hret1ne
    have hspec2 : intIndexInBounds arr ret2 ∧ arr[ret2.toNat]! = target ∧ (∀ (j : Nat), j < ret2.toNat → arr[j]! ≠ target) := by
      exact hpost2_imp hret2ne

    have hb1 : intIndexInBounds arr ret1 := by
      exact hspec1.left
    have hb2 : intIndexInBounds arr ret2 := by
      exact hspec2.left

    have hat1 : arr[ret1.toNat]! = target := by
      exact hspec1.right.left
    have hat2 : arr[ret2.toNat]! = target := by
      exact hspec2.right.left

    have hmin1 : ∀ (j : Nat), j < ret1.toNat → arr[j]! ≠ target := by
      exact hspec1.right.right
    have hmin2 : ∀ (j : Nat), j < ret2.toNat → arr[j]! ≠ target := by
      exact hspec2.right.right

    -- Step 9: Nat trichotomy on ret1.toNat and ret2.toNat
    have htrich : ret1.toNat < ret2.toNat ∨ ret1.toNat = ret2.toNat ∨ ret2.toNat < ret1.toNat := by
      simpa using Nat.lt_trichotomy ret1.toNat ret2.toNat

    -- Step 10: show ret1.toNat < ret2.toNat is impossible
    have hnot_lt12 : ¬ ret1.toNat < ret2.toNat := by
      intro hlt
      have hne_target : arr[ret1.toNat]! ≠ target := by
        exact hmin2 ret1.toNat hlt
      exact hne_target hat1

    -- Step 11: show ret2.toNat < ret1.toNat is impossible
    have hnot_lt21 : ¬ ret2.toNat < ret1.toNat := by
      intro hlt
      have hne_target : arr[ret2.toNat]! ≠ target := by
        exact hmin1 ret2.toNat hlt
      exact hne_target hat2

    -- Step 12: conclude toNat equality
    have htoNat_eq : ret1.toNat = ret2.toNat := by
      rcases htrich with hlt12 | heq | hlt21
      · exact False.elim (hnot_lt12 hlt12)
      · exact heq
      · exact False.elim (hnot_lt21 hlt21)

    -- Step 13: lift toNat equality to Int equality using nonnegativity from intIndexInBounds
    have hret1_nonneg : (0 : Int) ≤ ret1 := by
      exact hb1.left
    have hret2_nonneg : (0 : Int) ≤ ret2 := by
      exact hb2.left

    have hofNat_toNat1 : (Int.ofNat ret1.toNat) = ret1 := by
      -- standard lemma: Int.ofNat_of_nonneg / Int.ofNat_eq_coe / Int.toNat_of_nonneg
      -- sketch: simpa using (Int.ofNat_of_nonneg hret1_nonneg).symm or similar
      (try simp at *; expose_names); exact hret1_nonneg; done
    have hofNat_toNat2 : (Int.ofNat ret2.toNat) = ret2 := by
      (try simp at *; expose_names); exact hret2_nonneg; done

    have hEq_ofNat : (Int.ofNat ret1.toNat) = (Int.ofNat ret2.toNat) := by
      simpa [htoNat_eq]
    calc
      ret1 = Int.ofNat ret1.toNat := by simpa [hofNat_toNat1] using (Eq.symm hofNat_toNat1)
      _ = Int.ofNat ret2.toNat := hEq_ofNat
      _ = ret2 := hofNat_toNat2
end Proof
