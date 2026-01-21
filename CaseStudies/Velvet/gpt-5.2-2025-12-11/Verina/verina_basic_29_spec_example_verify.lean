import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000







def precondition (s : Array Int) (k : Nat) : Prop :=
  k < s.size

def postcondition (s : Array Int) (k : Nat) (result : Array Int) : Prop :=
  result.size + 1 = s.size ∧
  (∀ (i : Nat), i < result.size →
      (if i < k then result[i]! = s[i]! else result[i]! = s[i + 1]!))


def test1_s : Array Int := #[1, 2, 3, 4, 5]

def test1_k : Nat := 2

def test1_Expected : Array Int := #[1, 2, 4, 5]

def test2_s : Array Int := #[10, 20, 30, 40]

def test2_k : Nat := 0

def test2_Expected : Array Int := #[20, 30, 40]

def test4_s : Array Int := #[7]

def test4_k : Nat := 0

def test4_Expected : Array Int := #[]







section Proof
theorem test1_precondition :
  precondition test1_s test1_k := by
  simp [precondition, test1_s, test1_k]

theorem test1_postcondition :
  postcondition test1_s test1_k test1_Expected := by
  unfold postcondition test1_s test1_k test1_Expected
  constructor
  · decide
  · intro i hi
    have hi4 : i < 4 := by simpa using hi
    cases i with
    | zero =>
        simp
    | succ i =>
        cases i with
        | zero =>
            simp
        | succ i =>
            cases i with
            | zero =>
                simp
            | succ i =>
                cases i with
                | zero =>
                    simp
                | succ i =>
                    exfalso
                    omega

theorem test2_precondition :
  precondition test2_s test2_k := by
  simp [precondition, test2_s, test2_k]

theorem test2_postcondition :
  postcondition test2_s test2_k test2_Expected := by
  -- Step 1-2: unfold and substitute concrete test data
  unfold postcondition test2_s test2_k test2_Expected
  constructor

  -- Step 3: size equation part
  · have hSizeExpected : (#[20, 30, 40] : Array Int).size = 3 := by (try simp at *; expose_names); exact (rfl); done
    have hSizeS : (#[10, 20, 30, 40] : Array Int).size = 4 := by (try simp at *; expose_names); exact (rfl); done
    have hSizeEq : (#[20, 30, 40] : Array Int).size + 1 = (#[10, 20, 30, 40] : Array Int).size := by (try simp at *; expose_names); exact (hSizeS); done
    exact hSizeEq

  -- Step 4-9: elementwise part
  · intro i hi
    -- Step 6: derive the concrete bound i < 3 from hi
    have hi3 : i < 3 := by simpa using hi

    -- Step 5: simplify the if using k = 0 (i < 0 is false)
    have hIf : (if i < 0 then (#[20, 30, 40] : Array Int)[i]! = (#[10, 20, 30, 40] : Array Int)[i]!
               else (#[20, 30, 40] : Array Int)[i]! = (#[10, 20, 30, 40] : Array Int)[i + 1]!)
              =
              ((#[20, 30, 40] : Array Int)[i]! = (#[10, 20, 30, 40] : Array Int)[i + 1]!) := by
      (try simp at *; expose_names); exact rfl; done

    -- Step 7-8: case split on i using the fact i < 3
    cases i with
    | zero =>
        -- i = 0
        have h0 : (#[20, 30, 40] : Array Int)[0]! = (#[10, 20, 30, 40] : Array Int)[0 + 1]! := by (try simp at *; expose_names); exact (rfl); done
        simpa [hIf] using h0
    | succ i =>
        cases i with
        | zero =>
            -- i = 1
            have h1 : (#[20, 30, 40] : Array Int)[1]! = (#[10, 20, 30, 40] : Array Int)[1 + 1]! := by (try simp at *; expose_names); exact (rfl); done
            simpa [hIf] using h1
        | succ i =>
            cases i with
            | zero =>
                -- i = 2
                have h2 : (#[20, 30, 40] : Array Int)[2]! = (#[10, 20, 30, 40] : Array Int)[2 + 1]! := by (try simp at *; expose_names); exact (rfl); done
                simpa [hIf] using h2
            | succ i =>
                -- impossible since i < 3
                exfalso
                omega

theorem test4_precondition :
  precondition test4_s test4_k := by
  simp [precondition, test4_s, test4_k]

theorem test4_postcondition :
  postcondition test4_s test4_k test4_Expected := by
  unfold postcondition test4_s test4_k test4_Expected
  constructor
  · simp
  · intro i hi
    have : False := by
      simpa using (Nat.not_lt_zero i) hi
    exact False.elim this

theorem uniqueness (s : Array Int) (k : Nat) :
  precondition s k →
  (∀ ret1 ret2,
    postcondition s k ret1 →
    postcondition s k ret2 →
    ret1 = ret2) := by
  intro _hk
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨hsize1, hspec1⟩
  rcases hpost2 with ⟨hsize2, hspec2⟩

  have hsize : ret1.size = ret2.size := by
    apply Nat.add_right_cancel (m := 1)
    -- show: ret1.size + 1 = ret2.size + 1
    calc
      ret1.size + 1 = s.size := hsize1
      _ = ret2.size + 1 := by simpa [hsize2] using (Eq.symm hsize2)

  apply Array.ext hsize
  intro i hi1 hi2
  have h1 :
      (if i < k then ret1[i]! = s[i]! else ret1[i]! = s[i + 1]!) :=
    hspec1 i hi1
  have h2 :
      (if i < k then ret2[i]! = s[i]! else ret2[i]! = s[i + 1]!) :=
    hspec2 i hi2

  by_cases hik : i < k
  · have h1' : ret1[i]! = s[i]! := by simpa [hik] using h1
    have h2' : ret2[i]! = s[i]! := by simpa [hik] using h2
    -- goal is about `get` (not `get!`); rewrite both sides using the bounds
    have hr1 : ret1[i] = ret1[i]! := by simp [Array.get!, hi1]
    have hr2 : ret2[i] = ret2[i]! := by simp [Array.get!, hi2]
    -- now finish
    calc
      ret1[i] = ret1[i]! := hr1
      _ = s[i]! := h1'
      _ = ret2[i]! := h2'.symm
      _ = ret2[i] := hr2.symm
  · have h1' : ret1[i]! = s[i + 1]! := by simpa [hik] using h1
    have h2' : ret2[i]! = s[i + 1]! := by simpa [hik] using h2
    have hr1 : ret1[i] = ret1[i]! := by simp [Array.get!, hi1]
    have hr2 : ret2[i] = ret2[i]! := by simp [Array.get!, hi2]
    calc
      ret1[i] = ret1[i]! := hr1
      _ = s[i + 1]! := h1'
      _ = ret2[i]! := h2'.symm
      _ = ret2[i] := hr2.symm
end Proof
