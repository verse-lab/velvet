import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def IntIsEven (n : Int) : Prop := n % 2 = 0

def precondition (n : Int) : Prop :=
  True

def postcondition (n : Int) (result : Bool) : Prop :=
  (result = true ↔ IntIsEven n) ∧
  (result = false ↔ ¬ IntIsEven n)


def test1_n : Int := 4

def test1_Expected : Bool := true

def test4_n : Int := -2

def test4_Expected : Bool := true

def test2_n : Int := 7

def test2_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_n := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_n test1_Expected := by
  simp [postcondition, test1_n, test1_Expected, IntIsEven]

theorem test4_precondition :
  precondition test4_n := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_n test4_Expected := by
  -- unfold the definitions
  simp [postcondition, IntIsEven, test4_n, test4_Expected]

theorem test2_precondition :
  precondition test2_n := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_n test2_Expected := by
  unfold postcondition
  simp [test2_n, test2_Expected, IntIsEven]

theorem uniqueness_0
    (n : ℤ)
    (hpre : precondition n)
    (ret1 : Bool)
    (ret2 : Bool)
    (hpost1 : postcondition n ret1)
    (hpost2 : postcondition n ret2)
    : ret1 = true ↔ IntIsEven n := by
    simpa [postcondition] using hpost1.1

theorem uniqueness_1
    (n : ℤ)
    (hpre : precondition n)
    (ret1 : Bool)
    (ret2 : Bool)
    (hpost1 : postcondition n ret1)
    (hpost2 : postcondition n ret2)
    (h1_true : ret1 = true ↔ IntIsEven n)
    : ret1 = false ↔ ¬IntIsEven n := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2
    (n : ℤ)
    (hpre : precondition n)
    (ret1 : Bool)
    (ret2 : Bool)
    (hpost1 : postcondition n ret1)
    (hpost2 : postcondition n ret2)
    (h1_true : ret1 = true ↔ IntIsEven n)
    (h1_false : ret1 = false ↔ ¬IntIsEven n)
    : ret2 = true ↔ IntIsEven n := by
    intros; expose_names; exact (uniqueness_0 n hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_3
    (n : ℤ)
    (hpre : precondition n)
    (ret1 : Bool)
    (ret2 : Bool)
    (hpost1 : postcondition n ret1)
    (hpost2 : postcondition n ret2)
    (h1_true : ret1 = true ↔ IntIsEven n)
    (h1_false : ret1 = false ↔ ¬IntIsEven n)
    (h2_true : ret2 = true ↔ IntIsEven n)
    : ret2 = false ↔ ¬IntIsEven n := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_4
    (n : ℤ)
    (hpre : precondition n)
    (ret2 : Bool)
    (hpost2 : postcondition n ret2)
    (h2_true : ret2 = true ↔ IntIsEven n)
    (h2_false : ret2 = false ↔ ¬IntIsEven n)
    (hpost1 : postcondition n false)
    (hnotEven : ¬IntIsEven n)
    (h1_true : ¬IntIsEven n)
    (h1_false : ¬IntIsEven n)
    : ret2 = false := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_5
    (n : ℤ)
    (hpre : precondition n)
    (ret2 : Bool)
    (hpost2 : postcondition n ret2)
    (h2_true : ret2 = true ↔ IntIsEven n)
    (h2_false : ret2 = false ↔ ¬IntIsEven n)
    (hpost1 : postcondition n true)
    (heven : IntIsEven n)
    (h1_true : IntIsEven n)
    (h1_false : IntIsEven n)
    : ret2 = true := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (n : Int):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2
  have h1_true : (ret1 = true ↔ IntIsEven n) := by (try simp at *; expose_names); exact (uniqueness_0 n hpre ret1 ret2 hpost1 hpost2); done
  have h1_false : (ret1 = false ↔ ¬ IntIsEven n) := by (try simp at *; expose_names); exact (uniqueness_1 n hpre ret1 ret2 hpost1 hpost2 h1_true); done
  have h2_true : (ret2 = true ↔ IntIsEven n) := by (try simp at *; expose_names); exact (uniqueness_2 n hpre ret1 ret2 hpost1 hpost2 h1_true h1_false); done
  have h2_false : (ret2 = false ↔ ¬ IntIsEven n) := by (try simp at *; expose_names); exact (uniqueness_3 n hpre ret1 ret2 hpost1 hpost2 h1_true h1_false h2_true); done
  cases ret1 with
  | false =>
    have hnotEven : ¬ IntIsEven n := by (try simp at *; expose_names); exact h1_true; done
    have hret2false : ret2 = false := by (try simp at *; expose_names); exact (uniqueness_4 n hpre ret2 hpost2 h2_true h2_false hpost1 hnotEven h1_true h1_false); done
    simpa [hret2false]
  | true =>
    have heven : IntIsEven n := by (try simp at *; expose_names); exact h1_true; done
    have hret2true : ret2 = true := by (try simp at *; expose_names); exact (uniqueness_5 n hpre ret2 hpost2 h2_true h2_false hpost1 heven h1_true h1_false); done
    simpa [hret2true]
end Proof
