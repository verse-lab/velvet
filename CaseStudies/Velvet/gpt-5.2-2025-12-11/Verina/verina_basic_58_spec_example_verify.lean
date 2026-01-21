import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def DoubledArray (s : Array Int) (result : Array Int) : Prop :=
  result.size = s.size ∧
  ∀ (i : Nat), i < s.size → result[i]! = (2 : Int) * s[i]!

def precondition (s : Array Int) : Prop :=
  True

def postcondition (s : Array Int) (result : Array Int) : Prop :=
  DoubledArray s result


def test1_s : Array Int := #[]

def test1_Expected : Array Int := #[]

def test2_s : Array Int := #[1, 2, 3, 4, 5]

def test2_Expected : Array Int := #[2, 4, 6, 8, 10]

def test3_s : Array Int := #[0, -1, 5]

def test3_Expected : Array Int := #[0, -2, 10]







section Proof
theorem test1_precondition : precondition test1_s := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_s test1_Expected := by
  unfold postcondition DoubledArray
  constructor
  · simp [test1_s, test1_Expected]
  · intro i hi
    have : False := (Nat.not_lt_zero i) hi
    exact False.elim this

theorem test2_precondition : precondition test2_s := by
    intros; expose_names; exact (trivial); done

theorem test2_postcondition_0
    (i : ℕ)
    (hi : i < test2_s.size)
    (hsz : test2_s.size = 5)
    (hi5 : i < 5)
    : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition : postcondition test2_s test2_Expected := by
  unfold postcondition DoubledArray
  constructor
  · have hsize : test2_Expected.size = test2_s.size := by
      simp [test2_s, test2_Expected]
    exact hsize
  · intro i hi
    have hsz : test2_s.size = 5 := by
      simp [test2_s]
    have hi5 : i < 5 := by
      simpa [hsz] using hi
    have hcases : test2_Expected[i]! = (2 : Int) * test2_s[i]! := by
      -- reduce to the five possible indices using i < 5
      have hlt : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        -- one can prove this by Nat-case analysis / omega / intervalCases
        (try simp at *; expose_names); exact (test2_postcondition_0 i hi hsz hi5); done
      -- solve each concrete index by simp on array literals
      rcases hlt with h0 | h1 | h2 | h3 | h4
      · simp [h0, test2_s, test2_Expected]
      · simp [h1, test2_s, test2_Expected]
      · simp [h2, test2_s, test2_Expected]
      · simp [h3, test2_s, test2_Expected]
      · simp [h4, test2_s, test2_Expected]
    exact hcases

theorem test3_precondition : precondition test3_s := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_s test3_Expected := by
  unfold postcondition
  unfold DoubledArray
  constructor
  · simp [test3_s, test3_Expected]
  · intro i hi
    have hi' : i < 3 := by
      simpa [test3_s] using hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases this with rfl | rfl | rfl
    · simp [test3_s, test3_Expected]
    · simp [test3_s, test3_Expected]
    · simp [test3_s, test3_Expected]

theorem uniqueness_0
    (s : Array ℤ)
    (ret1 : Array ℤ)
    (hD1 : DoubledArray s ret1)
    : ret1.size = s.size := by
    exact hD1.1

theorem uniqueness_1
    (s : Array ℤ)
    (ret1 : Array ℤ)
    (hD1 : DoubledArray s ret1)
    : ∀ i < s.size, ret1[i]! = 2 * s[i]! := by
    intro i hi
    exact hD1.2 i hi

theorem uniqueness_2
    (s : Array ℤ)
    (ret2 : Array ℤ)
    (hpost2 : postcondition s ret2)
    : ret2.size = s.size := by
    intros; expose_names; exact (uniqueness_0 s ret2 hpost2); done

theorem uniqueness_3
    (s : Array ℤ)
    (ret2 : Array ℤ)
    (hpost2 : postcondition s ret2)
    : ∀ i < s.size, ret2[i]! = 2 * s[i]! := by
    intros; expose_names; exact (uniqueness_1 s ret2 hpost2 i h); done

theorem uniqueness_4
    (s : Array ℤ)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hD1 : DoubledArray s ret1)
    (hD2 : DoubledArray s ret2)
    (hD1_size : ret1.size = s.size)
    (hD1_val : ∀ i < s.size, ret1[i]! = 2 * s[i]!)
    (hD2_size : ret2.size = s.size)
    (hD2_val : ∀ i < s.size, ret2[i]! = 2 * s[i]!)
    : ret1.size = ret2.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_5
    (s : Array ℤ)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hD1 : DoubledArray s ret1)
    (hD2 : DoubledArray s ret2)
    (hD1_size : ret1.size = s.size)
    (hD1_val : ∀ i < s.size, ret1[i]! = 2 * s[i]!)
    (hD2_size : ret2.size = s.size)
    (hD2_val : ∀ i < s.size, ret2[i]! = 2 * s[i]!)
    (hsize : ret1.size = ret2.size)
    (hlt_s : ∀ i < ret1.size, i < s.size)
    (hlt_2 : ∀ i < ret1.size, i < ret2.size → i < s.size)
    : ∀ i < ret1.size, i < ret2.size → ret1[i]! = ret2[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_6
    (s : Array ℤ)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpre_triv : True)
    (hD1 : DoubledArray s ret1)
    (hD2 : DoubledArray s ret2)
    (hD1_size : ret1.size = s.size)
    (hD1_val : ∀ i < s.size, ret1[i]! = 2 * s[i]!)
    (hD2_size : ret2.size = s.size)
    (hD2_val : ∀ i < s.size, ret2[i]! = 2 * s[i]!)
    (hsize : ret1.size = ret2.size)
    (hlt_s : ∀ i < ret1.size, i < s.size)
    (hlt_2 : ∀ i < ret1.size, i < ret2.size → i < s.size)
    (hpoint_getBang : ∀ i < ret1.size, i < ret2.size → ret1[i]! = ret2[i]!)
    : ∀ (i : ℕ) (hi1 : i < ret1.size) (hi2 : i < ret2.size), ret1[i] = ret2[i] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness
    (s : Array Int)
    : precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2
  have hpre_triv : True := by (try simp at *; expose_names); exact hpre; done
  have hD1 : DoubledArray s ret1 := by simpa [postcondition] using hpost1
  have hD2 : DoubledArray s ret2 := by simpa [postcondition] using hpost2
  have hD1_size : ret1.size = s.size := by (try simp at *; expose_names); exact (uniqueness_0 s ret1 hD1); done
  have hD1_val : ∀ i : Nat, i < s.size → ret1[i]! = (2 : Int) * s[i]! := by (try simp at *; expose_names); exact (uniqueness_1 s ret1 hD1); done
  have hD2_size : ret2.size = s.size := by (try simp at *; expose_names); exact (uniqueness_2 s ret2 hpost2); done
  have hD2_val : ∀ i : Nat, i < s.size → ret2[i]! = (2 : Int) * s[i]! := by (try simp at *; expose_names); exact (uniqueness_3 s ret2 hpost2); done
  have hsize : ret1.size = ret2.size := by (try simp at *; expose_names); exact (uniqueness_4 s ret1 ret2 hpre_triv hD1 hD2 hD1_size hD1_val hD2_size hD2_val); done
  have hlt_s : (i : Nat) → (hi1 : i < ret1.size) → i < s.size := by (try simp at *; expose_names); exact (fun i hi1 ↦ Nat.lt_of_lt_of_eq hi1 hD1_size); done
  have hlt_2 : (i : Nat) → (hi1 : i < ret1.size) → (hi2 : i < ret2.size) → i < s.size := by (try simp at *; expose_names); exact (fun i hi1 hi2 ↦ hlt_s i hi1); done
  have hpoint_getBang : (i : Nat) → (hi1 : i < ret1.size) → (hi2 : i < ret2.size) → ret1[i]! = ret2[i]! := by (try simp at *; expose_names); exact (uniqueness_5 s ret1 ret2 hpre_triv hD1 hD2 hD1_size hD1_val hD2_size hD2_val hsize hlt_s hlt_2); done
  have hpoint_getElem : (i : Nat) → (hi1 : i < ret1.size) → (hi2 : i < ret2.size) → ret1[i] = ret2[i] := by (try simp at *; expose_names); exact (uniqueness_6 s ret1 ret2 hpre_triv hD1 hD2 hD1_size hD1_val hD2_size hD2_val hsize hlt_s hlt_2 hpoint_getBang); done
  have hext : ret1 = ret2 := by
    apply Array.ext hsize
    intro i hi1 hi2
    exact hpoint_getElem i hi1 hi2
  exact hext
end Proof
