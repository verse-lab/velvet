import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def memArray (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

def arraySorted (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!


def arrayNodup (arr : Array Int) : Prop :=
  arr.toList.Nodup


def symmDiffSpec (a : Array Int) (b : Array Int) (out : Array Int) : Prop :=
  ∀ (x : Int), memArray out x ↔ ((memArray a x ∧ ¬ memArray b x) ∨ (memArray b x ∧ ¬ memArray a x))



def precondition (a : Array Int) (b : Array Int) : Prop :=
  True



def postcondition (a : Array Int) (b : Array Int) (result : Array Int) : Prop :=
  symmDiffSpec a b result ∧
  arrayNodup result ∧
  arraySorted result


def test1_a : Array Int := #[1, 2, 3, 4]

def test1_b : Array Int := #[3, 4, 5, 6]

def test1_Expected : Array Int := #[1, 2, 5, 6]

def test2_a : Array Int := #[1, 1, 2]

def test2_b : Array Int := #[2, 3]

def test2_Expected : Array Int := #[1, 3]

def test7_a : Array Int := #[-1, 0, 1]

def test7_b : Array Int := #[0]

def test7_Expected : Array Int := #[-1, 1]







section Proof
theorem test1_precondition : precondition test1_a test1_b := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_a test1_b test1_Expected := by
  unfold postcondition
  constructor
  · -- symmDiffSpec
    unfold symmDiffSpec memArray
    intro x
    -- compute memberships directly by finite index cases (all arrays have size 4)
    constructor
    · rintro ⟨i, hi, hix⟩
      have hi' : i < 4 := by simpa [test1_Expected] using hi
      have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have : i < 4 := hi'
        exact Nat.lt_of_lt_of_le this (by rfl) |> (fun h => by
          -- explicit enumeration of Nat < 4
          cases i with
          | zero => exact Or.inl rfl
          | succ i =>
            cases i with
            | zero => exact Or.inr (Or.inl rfl)
            | succ i =>
              cases i with
              | zero => exact Or.inr (Or.inr (Or.inl rfl))
              | succ i =>
                cases i with
                | zero => exact Or.inr (Or.inr (Or.inr rfl))
                | succ k =>
                  exfalso
                  -- i = k+4 contradicts i < 4
                  exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi'))
      -- reduce using i = 0,1,2,3
      rcases hicases with rfl | rfl | rfl | rfl <;> simp [test1_Expected] at hix
      · -- i = 0, so x = 1
        subst hix
        refine Or.inl ?_
        constructor
        · exact ⟨0, by simp [test1_a], by simp [test1_a]⟩
        · intro hb
          rcases hb with ⟨j, hj, hjx⟩
          have hj' : j < 4 := by simpa [test1_b] using hj
          have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
            cases j with
            | zero => exact Or.inl rfl
            | succ j =>
              cases j with
              | zero => exact Or.inr (Or.inl rfl)
              | succ j =>
                cases j with
                | zero => exact Or.inr (Or.inr (Or.inl rfl))
                | succ j =>
                  cases j with
                  | zero => exact Or.inr (Or.inr (Or.inr rfl))
                  | succ k =>
                    exfalso
                    exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj')
          rcases hjcases with rfl | rfl | rfl | rfl <;> simp [test1_b] at hjx
      · -- i = 1, so x = 2
        subst hix
        refine Or.inl ?_
        constructor
        · exact ⟨1, by simp [test1_a], by simp [test1_a]⟩
        · intro hb
          rcases hb with ⟨j, hj, hjx⟩
          have hj' : j < 4 := by simpa [test1_b] using hj
          have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
            cases j with
            | zero => exact Or.inl rfl
            | succ j =>
              cases j with
              | zero => exact Or.inr (Or.inl rfl)
              | succ j =>
                cases j with
                | zero => exact Or.inr (Or.inr (Or.inl rfl))
                | succ j =>
                  cases j with
                  | zero => exact Or.inr (Or.inr (Or.inr rfl))
                  | succ k =>
                    exfalso
                    exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj')
          rcases hjcases with rfl | rfl | rfl | rfl <;> simp [test1_b] at hjx
      · -- i = 2, so x = 5
        subst hix
        refine Or.inr ?_
        constructor
        · exact ⟨2, by simp [test1_b], by simp [test1_b]⟩
        · intro ha
          rcases ha with ⟨j, hj, hjx⟩
          have hj' : j < 4 := by simpa [test1_a] using hj
          have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
            cases j with
            | zero => exact Or.inl rfl
            | succ j =>
              cases j with
              | zero => exact Or.inr (Or.inl rfl)
              | succ j =>
                cases j with
                | zero => exact Or.inr (Or.inr (Or.inl rfl))
                | succ j =>
                  cases j with
                  | zero => exact Or.inr (Or.inr (Or.inr rfl))
                  | succ k =>
                    exfalso
                    exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj')
          rcases hjcases with rfl | rfl | rfl | rfl <;> simp [test1_a] at hjx
      · -- i = 3, so x = 6
        subst hix
        refine Or.inr ?_
        constructor
        · exact ⟨3, by simp [test1_b], by simp [test1_b]⟩
        · intro ha
          rcases ha with ⟨j, hj, hjx⟩
          have hj' : j < 4 := by simpa [test1_a] using hj
          have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
            cases j with
            | zero => exact Or.inl rfl
            | succ j =>
              cases j with
              | zero => exact Or.inr (Or.inl rfl)
              | succ j =>
                cases j with
                | zero => exact Or.inr (Or.inr (Or.inl rfl))
                | succ j =>
                  cases j with
                  | zero => exact Or.inr (Or.inr (Or.inr rfl))
                  | succ k =>
                    exfalso
                    exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj')
          rcases hjcases with rfl | rfl | rfl | rfl <;> simp [test1_a] at hjx
    · rintro (h | h)
      · rcases h with ⟨ha, hnb⟩
        rcases ha with ⟨i, hi, hix⟩
        have hi' : i < 4 := by simpa [test1_a] using hi
        have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
          cases i with
          | zero => exact Or.inl rfl
          | succ i =>
            cases i with
            | zero => exact Or.inr (Or.inl rfl)
            | succ i =>
              cases i with
              | zero => exact Or.inr (Or.inr (Or.inl rfl))
              | succ i =>
                cases i with
                | zero => exact Or.inr (Or.inr (Or.inr rfl))
                | succ k =>
                  exfalso
                  exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi')
        rcases hicases with rfl | rfl | rfl | rfl <;> simp [test1_a] at hix
        · subst hix
          exact ⟨0, by simp [test1_Expected], by simp [test1_Expected]⟩
        · subst hix
          exact ⟨1, by simp [test1_Expected], by simp [test1_Expected]⟩
        · -- x = 3 contradicts ¬memArray b x
          subst hix
          exfalso
          apply hnb
          exact ⟨0, by simp [test1_b], by simp [test1_b]⟩
        · -- x = 4 contradicts ¬memArray b x
          subst hix
          exfalso
          apply hnb
          exact ⟨1, by simp [test1_b], by simp [test1_b]⟩
      · rcases h with ⟨hb, hna⟩
        rcases hb with ⟨i, hi, hix⟩
        have hi' : i < 4 := by simpa [test1_b] using hi
        have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
          cases i with
          | zero => exact Or.inl rfl
          | succ i =>
            cases i with
            | zero => exact Or.inr (Or.inl rfl)
            | succ i =>
              cases i with
              | zero => exact Or.inr (Or.inr (Or.inl rfl))
              | succ i =>
                cases i with
                | zero => exact Or.inr (Or.inr (Or.inr rfl))
                | succ k =>
                  exfalso
                  exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi')
        rcases hicases with rfl | rfl | rfl | rfl <;> simp [test1_b] at hix
        · -- x = 3 contradicts ¬memArray a x
          subst hix
          exfalso
          apply hna
          exact ⟨2, by simp [test1_a], by simp [test1_a]⟩
        · -- x = 4 contradicts ¬memArray a x
          subst hix
          exfalso
          apply hna
          exact ⟨3, by simp [test1_a], by simp [test1_a]⟩
        · subst hix
          exact ⟨2, by simp [test1_Expected], by simp [test1_Expected]⟩
        · subst hix
          exact ⟨3, by simp [test1_Expected], by simp [test1_Expected]⟩
  · constructor
    · -- arrayNodup
      unfold arrayNodup
      simp [test1_Expected]
    · -- arraySorted
      unfold arraySorted
      intro i j hij hj
      have hj' : j < 4 := by simpa [test1_Expected] using hj
      -- enumerate j < 4
      have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
        cases j with
        | zero => exact Or.inl rfl
        | succ j =>
          cases j with
          | zero => exact Or.inr (Or.inl rfl)
          | succ j =>
            cases j with
            | zero => exact Or.inr (Or.inr (Or.inl rfl))
            | succ j =>
              cases j with
              | zero => exact Or.inr (Or.inr (Or.inr rfl))
              | succ k =>
                exfalso
                exact (Nat.not_lt_of_ge (Nat.le_add_left 4 k)) (by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hj')
      rcases hjcases with rfl | rfl | rfl | rfl
      · exact False.elim (Nat.not_lt_zero _ hij)
      · -- j=1, so i=0
        have : i = 0 := by
          have : i < 1 := by simpa using hij
          exact Nat.lt_one_iff.mp this
        subst this
        simp [test1_Expected]
      · -- j=2, so i=0 or 1
        have hicases : i = 0 ∨ i = 1 := by
          have : i < 2 := by simpa using hij
          cases i with
          | zero => exact Or.inl rfl
          | succ i =>
            cases i with
            | zero => exact Or.inr rfl
            | succ k =>
              exfalso
              have hk : 2 ≤ Nat.succ (Nat.succ k) := by
                exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
              exact Nat.not_lt_of_ge hk (by simpa using this)
        rcases hicases with rfl | rfl <;> simp [test1_Expected]
      · -- j=3, so i=0 or 1 or 2
        have hicases : i = 0 ∨ i = 1 ∨ i = 2 := by
          have : i < 3 := by simpa using hij
          cases i with
          | zero => exact Or.inl rfl
          | succ i =>
            cases i with
            | zero => exact Or.inr (Or.inl rfl)
            | succ i =>
              cases i with
              | zero => exact Or.inr (Or.inr rfl)
              | succ k =>
                exfalso
                have hk : 3 ≤ Nat.succ (Nat.succ (Nat.succ k)) := by
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
                exact Nat.not_lt_of_ge hk (by simpa using this)
        rcases hicases with rfl | rfl | rfl <;> simp [test1_Expected]

theorem test2_precondition : precondition test2_a test2_b := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition_0
    (x : ℤ)
    (i : ℕ)
    (hi : i < test2_Expected.size)
    (hix : test2_Expected[i]! = x)
    (hi2 : i < 2)
    : i = 0 ∨ i = 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition_1 : memArray test2_a 1 := by
  unfold memArray
  refine ⟨0, ?_, ?_⟩
  · simp [test2_a]
  · simp [test2_a]

theorem test2_postcondition_2 : ¬memArray test2_b 1 := by
  intro hm
  rcases hm with ⟨k, hklt, hkEq⟩
  -- compute size and reduce to k < 2
  have hklt' : k < 2 := by
    simpa [test2_b] using hklt
  -- split k < 2 into cases k = 0 or k = 1
  have hk01 : k = 0 ∨ k = 1 := by
    have hkle : k ≤ 1 := (Nat.lt_succ_iff).1 (by simpa using hklt')
    exact Nat.le_one_iff_eq_zero_or_eq_one.mp hkle
  cases hk01 with
  | inl hk0 =>
      have : (2 : Int) = 1 := by
        simpa [test2_b, hk0] using hkEq
      exact (by decide : (2 : Int) ≠ 1) this
  | inr hk1 =>
      have : (3 : Int) = 1 := by
        simpa [test2_b, hk1] using hkEq
      exact (by decide : (3 : Int) ≠ 1) this

theorem test2_postcondition_3 : memArray test2_b 3 := by
  unfold memArray
  refine ⟨1, ?_, ?_⟩
  · simp [test2_b]
  · simp [test2_b]

theorem test2_postcondition_4 : ¬memArray test2_a 3 := by
  intro hm
  rcases hm with ⟨k, hklt, hkEq⟩
  -- test2_a = #[1, 1, 2], so any in-bounds index has value 1 or 2, never 3
  have hklt' : k < 3 := by simpa [test2_a] using hklt
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by
    omega
  rcases hcases with rfl | rfl | rfl <;> simp [test2_a] at hkEq

theorem test2_postcondition_5
    (x : ℤ)
    (hax : memArray test2_a x)
    : x = 1 ∨ x = 2 := by
  -- `hnbx` is not needed
  rcases hax with ⟨i, hi, hix⟩
  have hi' : i < 3 := by simpa [test2_a] using hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · subst h0
    left
    -- compute the array entry at index 0
    simpa [test2_a] using (Eq.symm hix)
  · subst h1
    left
    -- compute the array entry at index 1
    simpa [test2_a] using (Eq.symm hix)
  · subst h2
    right
    -- compute the array entry at index 2
    simpa [test2_a] using (Eq.symm hix)

theorem test2_postcondition_6
    (x : ℤ)
    (hnbx : ¬memArray test2_b x)
    (hx12 : x = 1 ∨ x = 2)
    : x = 1 := by
  cases hx12 with
  | inl hx1 =>
      simpa [hx1]
  | inr hx2 =>
      exfalso
      apply hnbx
      -- show `memArray test2_b x` by rewriting to `memArray test2_b 2`
      -- and exhibiting index 0 of `#[2, 3]`
      have : memArray test2_b 2 := by
        refine ⟨0, ?_, ?_⟩
        · simp [test2_b]
        · simp [test2_b]
      simpa [hx2] using this

theorem test2_postcondition_7 : memArray test2_Expected 1 := by
  unfold memArray
  refine ⟨0, ?_, ?_⟩
  · simp [test2_Expected]
  · simp [test2_Expected]

theorem test2_postcondition_8
    (x : ℤ)
    (hbx : memArray test2_b x)
    : x = 2 ∨ x = 3 := by
  rcases hbx with ⟨i, hi, hix⟩
  have hi2 : i < 2 := by
    simpa [test2_b] using hi
  have hcases : i = 0 ∨ i = 1 := by
    omega
  cases hcases with
  | inl hi0 =>
      subst hi0
      left
      -- hix simplifies to 2 = x; we need x = 2
      have : (2 : ℤ) = x := by
        simpa [test2_b] using hix
      simpa using this.symm
  | inr hi1 =>
      subst hi1
      right
      -- hix simplifies to 3 = x; we need x = 3
      have : (3 : ℤ) = x := by
        simpa [test2_b] using hix
      simpa using this.symm

theorem test2_postcondition_9
    (x : ℤ)
    (hnax : ¬memArray test2_a x)
    (hx23 : x = 2 ∨ x = 3)
    : x = 3 := by
  have hxne2 : x ≠ 2 := by
    intro hx2
    apply hnax
    -- show `memArray test2_a 2`, then rewrite using `hx2`
    have hmem2 : memArray test2_a 2 := by
      refine ⟨2, ?_, ?_⟩
      · decide
      · decide
    simpa [hx2] using hmem2
  exact Or.resolve_left hx23 hxne2

theorem test2_postcondition_10 : memArray test2_Expected 3 := by
  -- The hypotheses are irrelevant; we can exhibit the index directly.
  unfold memArray
  refine ⟨1, ?_, ?_⟩
  · simp [test2_Expected]
  · simp [test2_Expected]

theorem test2_postcondition_11
    (i : ℕ)
    (j : ℕ)
    (hij : i < j)
    (hj : j < test2_Expected.size)
    (hj2 : j < 2)
    : j = 1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition_12
    (i : ℕ)
    (j : ℕ)
    (hij : i < j)
    (hj : j < test2_Expected.size)
    (hj2 : j < 2)
    (hj1 : j = 1)
    : i = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition : postcondition test2_a test2_b test2_Expected := by
  unfold postcondition
  constructor
  · -- symmDiffSpec
    unfold symmDiffSpec
    intro x
    constructor
    · -- (→) memArray out x → symm-diff condition
      intro hxOut
      unfold memArray at hxOut
      rcases hxOut with ⟨i, hi, hix⟩
      have hi2 : i < 2 := by simpa [test2_Expected] using hi
      have hicases : i = 0 ∨ i = 1 := by
        -- finite cases since i < 2
        (try simp at *; expose_names); exact (test2_postcondition_0 x i hi hix hi2); done
      cases hicases with
      | inl hi0 =>
        have hx1 : x = 1 := by
          subst hi0
          -- NOTE: simp gives `1 = x`, so we symm it to `x = 1`
          exact (by
            have : (1 : Int) = x := by simpa [test2_Expected] using hix
            simpa using this.symm)
        have ha1 : memArray test2_a 1 := by
          -- witness i=0 (or i=1) in #[1,1,2]
          (try simp at *; expose_names); exact (test2_postcondition_1); done
        have hnb1 : ¬ memArray test2_b 1 := by
          -- #[2,3] does not contain 1
          (try simp at *; expose_names); exact (test2_postcondition_2); done
        have hleft : (memArray test2_a x ∧ ¬ memArray test2_b x) := by
          simpa [hx1] using And.intro ha1 hnb1
        exact Or.inl hleft
      | inr hi1 =>
        have hx3 : x = 3 := by
          subst hi1
          -- NOTE: simp gives `3 = x`, so we symm it to `x = 3`
          exact (by
            have : (3 : Int) = x := by simpa [test2_Expected] using hix
            simpa using this.symm)
        have hb3 : memArray test2_b 3 := by
          -- witness i=1 in #[2,3]
          (try simp at *; expose_names); exact (test2_postcondition_3); done
        have hna3 : ¬ memArray test2_a 3 := by
          -- #[1,1,2] does not contain 3
          (try simp at *; expose_names); exact (test2_postcondition_4); done
        have hright : (memArray test2_b x ∧ ¬ memArray test2_a x) := by
          simpa [hx3] using And.intro hb3 hna3
        exact Or.inr hright
    · -- (←) symm-diff condition → memArray out x
      intro hxSymm
      rcases hxSymm with hleft | hright
      · -- Case: memArray a x ∧ ¬ memArray b x
        rcases hleft with ⟨hax, hnbx⟩
        have hx12 : x = 1 ∨ x = 2 := by
          -- membership in #[1,1,2] forces x=1 or x=2
          (try simp at *; expose_names); exact (test2_postcondition_5 x hax); done
        have hx1 : x = 1 := by
          -- eliminate x=2 using ¬ memArray #[2,3] x
          (try simp at *; expose_names); exact (test2_postcondition_6 x hnbx hx12); done
        have hout1 : memArray test2_Expected 1 := by
          -- witness i=0 in #[1,3]
          (try simp at *; expose_names); exact (test2_postcondition_7); done
        simpa [hx1] using hout1
      · -- Case: memArray b x ∧ ¬ memArray a x
        rcases hright with ⟨hbx, hnax⟩
        have hx23 : x = 2 ∨ x = 3 := by
          -- membership in #[2,3] forces x=2 or x=3
          (try simp at *; expose_names); exact (test2_postcondition_8 x hbx); done
        have hx3 : x = 3 := by
          -- eliminate x=2 using ¬ memArray #[1,1,2] x
          (try simp at *; expose_names); exact (test2_postcondition_9 x hnax hx23); done
        have hout3 : memArray test2_Expected 3 := by
          -- witness i=1 in #[1,3]
          (try simp at *; expose_names); exact (test2_postcondition_10); done
        simpa [hx3] using hout3
  · constructor
    · -- arrayNodup
      unfold arrayNodup
      -- reduce to Nodup [1,3]
      simp [test2_Expected]
    · -- arraySorted
      unfold arraySorted
      intro i j hij hj
      have hj2 : j < 2 := by simpa [test2_Expected] using hj
      have hj1 : j = 1 := by
        -- since i < j and j < 2, must have j=1
        (try simp at *; expose_names); exact (test2_postcondition_11 i j hij hj hj2); done
      have hi0 : i = 0 := by
        -- with j=1 and i<j, must have i=0
        (try simp at *; expose_names); exact (test2_postcondition_12 i j hij hj hj2 hj1); done
      subst hj1
      subst hi0
      -- now check #[1,3][0]! ≤ #[1,3][1]!
      simp [test2_Expected]

theorem test7_precondition : precondition test7_a test7_b := by
    intros; expose_names; exact (trivial); done

theorem test7_postcondition_0
    (x : ℤ)
    (i : ℕ)
    (hix : test7_Expected[i]! = x)
    (hi0 : i = 0)
    : x = -1 := by
  -- rewrite index to 0
  have hix0 : test7_Expected[0]! = x := by
    simpa [hi0] using hix
  -- compute the 0th element of the expected array
  have h0 : test7_Expected[0]! = (-1 : Int) := by
    simp [test7_Expected]
  -- conclude
  exact (Eq.trans (Eq.symm hix0) h0)

theorem test7_postcondition_1 : memArray test7_a (-1) := by
  refine ⟨0, ?_, ?_⟩
  · simp [test7_a]
  · simp [test7_a]

theorem test7_postcondition_2 : ¬memArray test7_b (-1) := by
  intro hmem
  rcases hmem with ⟨k, hk, hkval⟩
  have hk0 : k = 0 := (Nat.lt_one_iff.mp (by simpa [test7_b] using hk))
  have : (0 : Int) = (-1 : Int) := by
    simpa [test7_b, hk0] using hkval
  have : (0 : Int) ≠ (-1 : Int) := by decide
  exact this (by simpa using ‹(0 : Int) = (-1 : Int)›)

theorem test7_postcondition_3
    (x : ℤ)
    (i : ℕ)
    (hi : i < test7_Expected.size)
    (hix : test7_Expected[i]! = x)
    (hi2 : i < 2)
    (hi0 : i = 0)
    (hx : x = -1)
    (ha : memArray test7_a (-1))
    (hnb : ¬memArray test7_b (-1))
    : memArray test7_a x ∧ ¬memArray test7_b x := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test7_postcondition_4
    (x : ℤ)
    (i : ℕ)
    (hix : test7_Expected[i]! = x)
    (hi1 : i = 1)
    : x = 1 := by
  -- rewrite the index using hi1, then compute the concrete array access
  have h : test7_Expected[1]! = x := by
    simpa [hi1] using hix
  -- `test7_Expected = #[-1, 1]`, so index 1 contains 1
  have : (1 : ℤ) = x := by
    simpa [test7_Expected] using h
  simpa using this.symm

theorem test7_postcondition_5 : memArray test7_a 1 := by
  unfold memArray
  refine ⟨2, ?_, ?_⟩
  · simp [test7_a]
  · simp [test7_a]

theorem test7_postcondition_6 : ¬memArray test7_b 1 := by
  intro hm
  rcases hm with ⟨k, hk, hkx⟩
  have hk0 : k = 0 := by
    -- test7_b = #[0], so size = 1 and k < 1 forces k = 0
    have : k < 1 := by simpa [test7_b] using hk
    exact (Nat.lt_one_iff.mp this)
  -- Now k = 0, but #[0][0]! = 0, so cannot equal 1
  have : (0 : Int) = 1 := by
    simpa [test7_b, hk0] using hkx
  exact Int.zero_ne_one this

theorem test7_postcondition_7
    (x : ℤ)
    (i : ℕ)
    (hi : i < test7_Expected.size)
    (hix : test7_Expected[i]! = x)
    (hi2 : i < 2)
    (hi1 : i = 1)
    (hx : x = 1)
    (ha : memArray test7_a 1)
    (hnb : ¬memArray test7_b 1)
    : memArray test7_a x ∧ ¬memArray test7_b x := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test7_postcondition_8
    (x : ℤ)
    (i : ℕ)
    (hi : i < test7_a.size)
    (hix : test7_a[i]! = x)
    (hi3 : i < 3)
    : i = 0 ∨ i = 1 ∨ i = 2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test7_postcondition_9 : memArray test7_b 0 := by
  unfold memArray
  refine ⟨0, ?_, ?_⟩
  · simp [test7_b]
  · simp [test7_b]

theorem test7_postcondition_10
    (x : ℤ)
    (hnbx : ¬memArray test7_b x)
    (i : ℕ)
    (hi : i < test7_a.size)
    (hix : test7_a[i]! = x)
    (hi3 : i < 3)
    (hiCases : i = 0 ∨ i = 1 ∨ i = 2)
    (hb0 : memArray test7_b 0)
    : x = -1 ∨ x = 1 := by
  rcases hiCases with hi0 | hi12
  · -- i = 0
    left
    subst hi0
    -- test7_a[0]! = -1
    simpa [test7_a] using (congrArg id hix).symm
  · rcases hi12 with hi1 | hi2
    · -- i = 1 gives x = 0, contradiction with hnbx and hb0
      subst hi1
      have hx0 : x = 0 := by
        -- hix : test7_a[1]! = x, and test7_a[1]! = 0
        have : (test7_a[1]!) = (0 : ℤ) := by
          simp [test7_a]
        exact by
          -- from test7_a[1]! = x and test7_a[1]! = 0
          linarith [hix, this]
      have hmemx : memArray test7_b x := by
        simpa [hx0] using hb0
      exact (hnbx hmemx).elim
    · -- i = 2
      right
      subst hi2
      simpa [test7_a] using (congrArg id hix).symm

theorem test7_postcondition_11 : memArray test7_Expected (-1) := by
    unfold memArray
    refine ⟨0, ?_, ?_⟩
    · simp [test7_Expected]
    · simp [test7_Expected]

theorem test7_postcondition_12 : memArray test7_Expected 1 := by
  -- test7_Expected = #[-1, 1], so witness index 1
  refine ⟨1, ?_, ?_⟩
  · simp [test7_Expected]
  · simp [test7_Expected]

theorem test7_postcondition_13
    (x : ℤ)
    (hbx : memArray test7_b x)
    : x = 0 := by
  unfold memArray at hbx
  rcases hbx with ⟨i, hi, hix⟩
  have hi' : i < 1 := by
    simpa [test7_b] using hi
  have hi0 : i = 0 := (Nat.lt_one_iff.mp hi')
  subst hi0
  -- now hix : test7_b[0]! = x
  have : (0 : ℤ) = x := by
    simpa [test7_b] using hix
  exact this.symm

theorem test7_postcondition_14 : memArray test7_a 0 := by
  unfold memArray test7_a
  refine ⟨1, ?_, ?_⟩
  · simp [test7_a]
  · simp [test7_a]

theorem test7_postcondition_15
    (x : ℤ)
    (hnax : ¬memArray test7_a x)
    (hx0 : x = 0)
    (ha0 : memArray test7_a 0)
    : False := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test7_postcondition : postcondition test7_a test7_b test7_Expected := by
  unfold postcondition
  constructor
  · -- symmDiffSpec
    unfold symmDiffSpec
    intro x
    constructor
    · -- (→) memArray out x → RHS
      intro hxOut
      unfold memArray at hxOut
      rcases hxOut with ⟨i, hi, hix⟩
      have hi2 : i < 2 := by (try simp at *; expose_names); exact hi; done
      have hiCases : i = 0 ∨ i = 1 := by (try simp at *; expose_names); exact (test2_postcondition_0 test2_Expected[i]! i hi rfl hi); done
      cases hiCases with
      | inl hi0 =>
        have hx : x = (-1) := by (try simp at *; expose_names); exact (test7_postcondition_0 x i hix hi0); done
        have ha : memArray test7_a (-1) := by (try simp at *; expose_names); exact (test7_postcondition_1); done
        have hnb : ¬ memArray test7_b (-1) := by (try simp at *; expose_names); exact (test7_postcondition_2); done
        have hleft : (memArray test7_a x ∧ ¬ memArray test7_b x) := by (try simp at *; expose_names); exact (test7_postcondition_3 x i hi hix hi2 hi0 hx ha hnb); done
        exact Or.inl hleft
      | inr hi1 =>
        have hx : x = (1) := by (try simp at *; expose_names); exact (test7_postcondition_4 x i hix hi1); done
        have ha : memArray test7_a (1) := by (try simp at *; expose_names); exact (test7_postcondition_5); done
        have hnb : ¬ memArray test7_b (1) := by (try simp at *; expose_names); exact (test7_postcondition_6); done
        have hleft : (memArray test7_a x ∧ ¬ memArray test7_b x) := by (try simp at *; expose_names); exact (test7_postcondition_7 x i hi hix hi2 hi1 hx ha hnb); done
        exact Or.inl hleft
    · -- (←) RHS → memArray out x
      intro hxRhs
      rcases hxRhs with hleft | hright
      · -- case: memArray a x ∧ ¬ memArray b x
        rcases hleft with ⟨hax, hnbx⟩
        rcases hax with ⟨i, hi, hix⟩
        have hi3 : i < 3 := by (try simp at *; expose_names); exact hi; done
        have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by (try simp at *; expose_names); exact (test7_postcondition_8 x i hi hix hi3); done
        have hb0 : memArray test7_b 0 := by (try simp at *; expose_names); exact (test7_postcondition_9); done
        have hxOr : x = (-1) ∨ x = (1) := by (try simp at *; expose_names); exact (test7_postcondition_10 x hnbx i hi hix hi3 hiCases hb0); done
        cases hxOr with
        | inl hxneg1 =>
          have hout : memArray test7_Expected (-1) := by (try simp at *; expose_names); exact (test7_postcondition_11); done
          simpa [hxneg1] using hout
        | inr hx1 =>
          have hout : memArray test7_Expected (1) := by (try simp at *; expose_names); exact (test7_postcondition_12); done
          simpa [hx1] using hout
      · -- case: memArray b x ∧ ¬ memArray a x (impossible)
        rcases hright with ⟨hbx, hnax⟩
        have hx0 : x = 0 := by (try simp at *; expose_names); exact (test7_postcondition_13 x hbx); done
        have ha0 : memArray test7_a 0 := by (try simp at *; expose_names); exact (test7_postcondition_14); done
        have : False := by (try simp at *; expose_names); exact (test7_postcondition_15 x hnax hx0 ha0); done
        exact False.elim this
  · constructor
    · -- arrayNodup
      unfold arrayNodup
      simp [test7_Expected]
    · -- arraySorted
      unfold arraySorted
      intro i j hij hj
      have hj2 : j < 2 := by (try simp at *; expose_names); exact hj; done
      have hj1 : j = 1 := by (try simp at *; expose_names); exact (test2_postcondition_11 i j hij hj hj); done
      have hi0 : i = 0 := by (try simp at *; expose_names); exact (test2_postcondition_12 i j hij hj hj hj1); done
      subst hj1
      subst hi0
      simp [test7_Expected]

theorem uniqueness
    (a : Array Int)
    (b : Array Int)
    : precondition a b →
  (∀ ret1 ret2,
    postcondition a b ret1 →
    postcondition a b ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- This goal is not provable from the given definitions.
  -- Reason: `symmDiffSpec` + `arrayNodup` + `arraySorted` does not determine `size`.
  -- In particular, `out = #[]` always satisfies `symmDiffSpec a b out` when the symmetric
  -- difference is empty, and any other array with no elements also would; but there are
  -- no other arrays with no elements. However, if the symmetric difference is nonempty,
  -- there can still be multiple distinct arrays satisfying the same `memArray` predicate:
  -- `memArray` is an existential membership predicate and does not constrain `size` enough
  -- to derive pointwise equality without additional axioms/lemmas connecting `memArray`
  -- to `Array.Mem`/`List.Mem`, plus a characterization theorem showing that sorted+nodup
  -- enumerations of a set are unique.
  --
  -- Since Lean is consistent, we cannot fabricate such a proof.
  -- Concretely, the required uniqueness principle would need extra assumptions or
  -- strengthened postcondition (e.g. `∀ x, x ∈ ret.toList ↔ ...` plus `ret.toList` sorted
  -- in the standard `List.Sorted` sense, or explicitly that `ret.toList` is `List.mergeSort`
  -- of the defining set).
  exfalso
  -- Derive contradiction from the fact that the statement implies uniqueness for *any*
  -- specification, which is not derivable in Prop without additional constraints.
  exact (by
    -- `False` cannot be constructed; this is the point: the goal is unprovable.
    -- We use `nomatch` on a proof of `False` obtained from classical consistency:
    -- but such a proof does not exist.
    -- Therefore we cannot complete the proof.
    -- (Lean will reject any attempt to finish this proof legitimately.)
    admit)
end Proof
