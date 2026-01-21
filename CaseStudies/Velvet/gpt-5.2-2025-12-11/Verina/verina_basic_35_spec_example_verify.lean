import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def nonzerosList (arr : Array Int) : List Int :=
  arr.toList.filter (fun x => x ≠ 0)

def allZeroFrom (arr : Array Int) (k : Nat) : Prop :=
  ∀ i : Nat, i < arr.size → k ≤ i → arr[i]! = 0



def precondition (arr : Array Int) : Prop :=
  True








def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  result.size = arr.size ∧
  (∃ k : Nat,
    k = (nonzerosList arr).length ∧
    k ≤ result.size ∧
    (∀ i : Nat, i < k → result[i]! = (nonzerosList arr)[i]!) ∧
    allZeroFrom result k)


def test1_arr : Array Int := #[0, 1, 0, 3, 12]

def test1_Expected : Array Int := #[1, 3, 12, 0, 0]

def test3_arr : Array Int := #[1, 2, 3]

def test3_Expected : Array Int := #[1, 2, 3]

def test7_arr : Array Int := #[0, -1, 0, -2, 3, 0]

def test7_Expected : Array Int := #[-1, -2, 3, 0, 0, 0]







section Proof
theorem test1_precondition :
  precondition test1_arr := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_arr test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_arr, test1_Expected]
  · refine ⟨3, ?_, ?_, ?_, ?_⟩
    · simp [nonzerosList, test1_arr]
    · simp [test1_Expected]
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
        omega
      rcases hi' with rfl | rfl | rfl
      · simp [test1_arr, test1_Expected, nonzerosList]
      · simp [test1_arr, test1_Expected, nonzerosList]
      · simp [test1_arr, test1_Expected, nonzerosList]
    · unfold allZeroFrom
      intro i hiSize hik
      have h3 : i = 3 ∨ i = 4 := by
        have : i < 5 := by
          simpa [test1_Expected] using hiSize
        omega
      rcases h3 with rfl | rfl
      · simp [test1_Expected]
      · simp [test1_Expected]

theorem test3_precondition :
  precondition test3_arr := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_arr test3_Expected := by
  unfold postcondition
  constructor
  · simp [test3_arr, test3_Expected]
  · refine ⟨3, ?_, ?_, ?_, ?_⟩
    · simp [nonzerosList, test3_arr]
    · simp [test3_Expected]
    · intro i hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
        omega
      rcases hcases with h0 | h1 | h2
      · subst h0
        simp [test3_Expected, nonzerosList, test3_arr]
      · subst h1
        simp [test3_Expected, nonzerosList, test3_arr]
      · subst h2
        simp [test3_Expected, nonzerosList, test3_arr]
    ·
      unfold allZeroFrom
      intro i hiSize hk
      -- size is 3, so i < 3 and 3 ≤ i is impossible
      have hsz : test3_Expected.size = 3 := by simp [test3_Expected]
      have hiLt3 : i < 3 := by simpa [hsz] using hiSize
      have : False := Nat.not_lt_of_ge hk hiLt3
      contradiction

theorem test7_precondition :
  precondition test7_arr := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition :
  postcondition test7_arr test7_Expected := by
  unfold postcondition
  constructor
  · simp [test7_arr, test7_Expected]
  · refine ⟨3, ?_, ?_, ?_, ?_⟩
    · simp [nonzerosList, test7_arr]
    · simp [test7_Expected]
    · intro i hi
      have hnz : nonzerosList test7_arr = [-1, -2, 3] := by
        simp [nonzerosList, test7_arr]
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
        omega
      rcases hi' with rfl | rfl | rfl
      · simp [test7_Expected, hnz]
      · simp [test7_Expected, hnz]
      · simp [test7_Expected, hnz]
    · unfold allZeroFrom
      intro i hiSize hiGe
      have hsize : test7_Expected.size = 6 := by
        simp [test7_Expected]
      have hiSize' : i < 6 := by
        simpa [hsize] using hiSize
      have hi' : i = 3 ∨ i = 4 ∨ i = 5 := by
        omega
      rcases hi' with rfl | rfl | rfl
      · simp [test7_Expected]
      · simp [test7_Expected]
      · simp [test7_Expected]

theorem uniqueness_0
    (arr : Array ℤ)
    (hpre : precondition arr)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hsize1 : ret1.size = arr.size)
    (k1 : ℕ)
    (hk1_len : k1 = (nonzerosList arr).length)
    (hk1_le : k1 ≤ ret1.size)
    (hk1_zero : allZeroFrom ret1 k1)
    (hsize2 : ret2.size = arr.size)
    (k2 : ℕ)
    (hk2_len : k2 = (nonzerosList arr).length)
    (hk2_le : k2 ≤ ret2.size)
    (hk2_zero : allZeroFrom ret2 k2)
    (hk1_prefix : ∀ i < k1, ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hk2_prefix : ∀ i < k2, ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    : k1 = k2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (arr : Array ℤ)
    (hpre : precondition arr)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hsize1 : ret1.size = arr.size)
    (k1 : ℕ)
    (hk1_len : k1 = (nonzerosList arr).length)
    (hk1_le : k1 ≤ ret1.size)
    (hk1_zero : allZeroFrom ret1 k1)
    (hsize2 : ret2.size = arr.size)
    (k2 : ℕ)
    (hk2_len : k2 = (nonzerosList arr).length)
    (hk2_le : k2 ≤ ret2.size)
    (hk2_zero : allZeroFrom ret2 k2)
    (hk12 : k1 = k2)
    (hk1_prefix : ∀ i < k1, ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hk2_prefix : ∀ i < k2, ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    : ret1.size = ret2.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (arr : Array ℤ)
    (hpre : precondition arr)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hsize1 : ret1.size = arr.size)
    (k1 : ℕ)
    (hk1_len : k1 = (nonzerosList arr).length)
    (hk1_le : k1 ≤ ret1.size)
    (hk1_zero : allZeroFrom ret1 k1)
    (hsize2 : ret2.size = arr.size)
    (k2 : ℕ)
    (hk2_len : k2 = (nonzerosList arr).length)
    (hk2_le : k2 ≤ ret2.size)
    (hk2_zero : allZeroFrom ret2 k2)
    (hk12 : k1 = k2)
    (hsize12 : ret1.size = ret2.size)
    (i : ℕ)
    (hi1 : i < ret1.size)
    (hi2 : i < ret2.size)
    (hk1_def : k1 = (nonzerosList arr).length)
    (hk2_def : k2 = (nonzerosList arr).length)
    (hik1 : i < k1)
    (hik2 : i < k2)
    (hk1_prefix : ∀ i < k1, ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hk2_prefix : ∀ i < k2, ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    (hret1_i : ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hret2_i : ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    : ret1[i]! = ret2[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_3
    (arr : Array ℤ)
    (hpre : precondition arr)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hsize1 : ret1.size = arr.size)
    (k1 : ℕ)
    (hk1_len : k1 = (nonzerosList arr).length)
    (hk1_le : k1 ≤ ret1.size)
    (hk1_zero : allZeroFrom ret1 k1)
    (hsize2 : ret2.size = arr.size)
    (k2 : ℕ)
    (hk2_len : k2 = (nonzerosList arr).length)
    (hk2_le : k2 ≤ ret2.size)
    (hk2_zero : allZeroFrom ret2 k2)
    (hk12 : k1 = k2)
    (hsize12 : ret1.size = ret2.size)
    (i : ℕ)
    (hi1 : i < ret1.size)
    (hi2 : i < ret2.size)
    (hk1_def : k1 = (nonzerosList arr).length)
    (hk2_def : k2 = (nonzerosList arr).length)
    (hik1 : i < k1)
    (hik2 : i < k2)
    (hpoint : ret1[i]! = ret2[i]!)
    (hk1_prefix : ∀ i < k1, ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hk2_prefix : ∀ i < k2, ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    (hret1_i : ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hret2_i : ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    : ret1[i] = ret2[i] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_4
    (arr : Array ℤ)
    (hpre : precondition arr)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hsize1 : ret1.size = arr.size)
    (k1 : ℕ)
    (hk1_len : k1 = (nonzerosList arr).length)
    (hk1_le : k1 ≤ ret1.size)
    (hk1_zero : allZeroFrom ret1 k1)
    (hsize2 : ret2.size = arr.size)
    (k2 : ℕ)
    (hk2_len : k2 = (nonzerosList arr).length)
    (hk2_le : k2 ≤ ret2.size)
    (hk2_zero : allZeroFrom ret2 k2)
    (hk12 : k1 = k2)
    (hsize12 : ret1.size = ret2.size)
    (i : ℕ)
    (hi1 : i < ret1.size)
    (hi2 : i < ret2.size)
    (hk1_def : k1 = (nonzerosList arr).length)
    (hk2_def : k2 = (nonzerosList arr).length)
    (hik1_ge : k1 ≤ i)
    (hret1_i0 : ret1[i]! = 0)
    (hik2_ge : k2 ≤ i)
    (hret2_i0 : ret2[i]! = 0)
    (hpoint : ret1[i]! = ret2[i]!)
    (hk1_prefix : ∀ i < k1, ret1[i]! = (nonzerosList arr)[i]?.getD 0)
    (hk2_prefix : ∀ i < k2, ret2[i]! = (nonzerosList arr)[i]?.getD 0)
    : ret1[i] = ret2[i] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (arr : Array Int):
  precondition arr →
  (∀ ret1 ret2,
    postcondition arr ret1 →
    postcondition arr ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2

  -- unfold precondition: it's `True`, so it provides no additional info
  have hpre_triv : True := by
    simpa [precondition] using hpre

  -- expand both postconditions and extract their components
  rcases hpost1 with ⟨hsize1, k1, hk1_len, hk1_le, hk1_prefix, hk1_zero⟩
  rcases hpost2 with ⟨hsize2, k2, hk2_len, hk2_le, hk2_prefix, hk2_zero⟩

  -- synchronize the existential witnesses: k1 = k2 because both equal (nonzerosList arr).length
  have hk12 : k1 = k2 := by
    -- hk1_len : k1 = L, hk2_len : k2 = L
    -- so k1 = k2 by transitivity
    (try simp at *; expose_names); exact (uniqueness_0 arr hpre ret1 ret2 hpre_triv hsize1 k1 hk1_len hk1_le hk1_zero hsize2 k2 hk2_len hk2_le hk2_zero hk1_prefix hk2_prefix); done

  -- sizes of ret1 and ret2 agree
  have hsize12 : ret1.size = ret2.size := by
    -- hsize1 : ret1.size = arr.size, hsize2 : ret2.size = arr.size
    -- hence ret1.size = ret2.size
    (try simp at *; expose_names); exact (uniqueness_1 arr hpre ret1 ret2 hpre_triv hsize1 k1 hk1_len hk1_le hk1_zero hsize2 k2 hk2_len hk2_le hk2_zero hk12 hk1_prefix hk2_prefix); done

  -- prove array equality by extensionality: same size + pointwise equality
  apply Array.ext hsize12
  intro i hi1 hi2

  -- Let k be the (common) split point
  have hk1_def : k1 = (nonzerosList arr).length := by
    exact hk1_len
  have hk2_def : k2 = (nonzerosList arr).length := by
    exact hk2_len

  -- case split on whether i < k1 or k1 ≤ i
  have hcases : i < k1 ∨ k1 ≤ i := by
    exact Nat.lt_or_ge i k1

  cases hcases with
  | inl hik1 =>
      -- Use prefix property for both arrays at index i < k
      have hret1_i : ret1[i]! = (nonzerosList arr)[i]! := by
        exact hk1_prefix i hik1
      have hik2 : i < k2 := by
        -- rewrite by hk12
        (try simp at *; expose_names); exact Nat.lt_of_lt_of_eq hik1 hk12; done
      have hret2_i : ret2[i]! = (nonzerosList arr)[i]! := by
        exact hk2_prefix i hik2
      -- conclude equality at index i
      have hpoint : ret1[i]! = ret2[i]! := by
        -- both equal the same (nonzerosList arr)[i]!
        (try simp at *; expose_names); exact (uniqueness_2 arr hpre ret1 ret2 hpre_triv hsize1 k1 hk1_len hk1_le hk1_zero hsize2 k2 hk2_len hk2_le hk2_zero hk12 hsize12 i hi1 hi2 hk1_def hk2_def hik1 hik2 hk1_prefix hk2_prefix hret1_i hret2_i); done
      -- convert getElem (with proof) to get! on each side, then use hpoint
      -- (goal is `ret1[i] = ret2[i]` with proofs hi1 hi2)
      (try simp at *; expose_names); exact (uniqueness_3 arr hpre ret1 ret2 hpre_triv hsize1 k1 hk1_len hk1_le hk1_zero hsize2 k2 hk2_len hk2_le hk2_zero hk12 hsize12 i hi1 hi2 hk1_def hk2_def hik1 hik2 hpoint hk1_prefix hk2_prefix hret1_i hret2_i); done
  | inr hik1_ge =>
      -- Use allZeroFrom for both arrays: indices i with k ≤ i are 0
      have hret1_i0 : ret1[i]! = 0 := by
        -- unfold allZeroFrom and apply with hi1 and hik1_ge
        -- note: hi1 : i < ret1.size
        -- hk1_zero : allZeroFrom ret1 k1
        (try simp at *; expose_names); exact hk1_zero i hi1 hik1_ge; done
      have hik2_ge : k2 ≤ i := by
        -- rewrite by hk12
        (try simp at *; expose_names); exact le_of_eq_of_le (id (Eq.symm hk12)) hik1_ge; done
      have hret2_i0 : ret2[i]! = 0 := by
        -- unfold allZeroFrom and apply with hi2 and hik2_ge
        (try simp at *; expose_names); exact hk2_zero i hi2 hik2_ge; done
      have hpoint : ret1[i]! = ret2[i]! := by
        -- both are 0
        (try simp at *; expose_names); exact (Nat.ToInt.of_eq (id (Eq.symm hret1_i0)) (id (Eq.symm hret2_i0)) rfl); done
      -- convert getElem (with proof) to get! on each side, then use hpoint
      (try simp at *; expose_names); exact (uniqueness_4 arr hpre ret1 ret2 hpre_triv hsize1 k1 hk1_len hk1_le hk1_zero hsize2 k2 hk2_len hk2_le hk2_zero hk12 hsize12 i hi1 hi2 hk1_def hk2_def hik1_ge hret1_i0 hik2_ge hret2_i0 hpoint hk1_prefix hk2_prefix); done
end Proof
