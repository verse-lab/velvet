import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000








def atMostOneDistinct (a : Array Int) : Prop :=
  a.size = 0 ∨ (∀ (i : Nat), i < a.size → a[i]! = a[0]!)



def precondition (a : Array Int) : Prop :=
  True



def postcondition (a : Array Int) (result : Bool) : Prop :=
  result ↔ atMostOneDistinct a


def test1_a : Array Int := #[1, 1, 1]

def test1_Expected : Bool := true

def test2_a : Array Int := #[1, 2, 1]

def test2_Expected : Bool := false

def test7_a : Array Int := #[]

def test7_Expected : Bool := true







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  simp [postcondition, atMostOneDistinct, test1_a, test1_Expected]
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases this with rfl | rfl | rfl <;> simp [test1_a]

theorem test2_precondition :
  precondition test2_a := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_Expected := by
  unfold postcondition test2_a test2_Expected
  -- goal: False ↔ atMostOneDistinct #[1,2,1]
  constructor
  · intro hFalse
    cases hFalse
  · intro hAtMost
    -- show False, by contradicting the "all equal to a[0]" branch using i = 1
    rcases hAtMost with hsz0 | hall
    · -- but size is 3
      simp [atMostOneDistinct] at hsz0
    · have hlt : (1 : Nat) < (#[ (1 : Int), 2, 1 ] : Array Int).size := by
        simp
      have hEq := hall 1 hlt
      -- compute both sides: a[1]! = 2, a[0]! = 1
      -- contradiction
      simpa using (show (2 : Int) = 1 from by simpa using hEq)

theorem test7_precondition :
  precondition test7_a := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition :
  postcondition test7_a test7_Expected := by
  simp [postcondition, atMostOneDistinct, test7_a, test7_Expected]

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  unfold postcondition at hpost1 hpost2
  apply (Bool.eq_iff_iff).2
  -- prove ret1 ↔ ret2
  constructor
  · intro hret1
    exact hpost2.2 (hpost1.1 hret1)
  · intro hret2
    exact hpost1.2 (hpost2.1 hret2)
end Proof
