import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def precondition (n : Int) (a : Array Int) : Prop :=
  a.size > 0




def postcondition (n : Int) (a : Array Int) (result : Bool) : Prop :=
  (result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n))


def test1_n : Int := 6

def test1_a : Array Int := #[1, 2, 3, 4, 5]

def test1_Expected : Bool := true

def test2_n : Int := 3

def test2_a : Array Int := #[1, 2, 3, 4, 5]

def test2_Expected : Bool := false

def test3_n : Int := 5

def test3_a : Array Int := #[5, 5, 5]

def test3_Expected : Bool := false







section Proof
theorem test1_precondition :
  precondition test1_n test1_a := by
  unfold precondition
  simp [test1_a]

theorem test1_postcondition :
  postcondition test1_n test1_a test1_Expected := by
  -- unfold and reduce `result = true` with `result = true` where `result` is `true`
  simp [postcondition, test1_n, test1_a, test1_Expected]
  intro i hi
  -- `simp` has reduced the goal to a concrete inequality about the `i`th element of #[1,2,3,4,5]
  -- and the hypothesis is `i < 5`; we do a finite split on `i` by cases on `i`.
  interval_cases i <;> simp at hi <;> simp [test1_a]

theorem test2_precondition :
  precondition test2_n test2_a := by
  unfold precondition
  simp [test2_a]

theorem test2_postcondition :
  postcondition test2_n test2_a test2_Expected := by
  -- After unfolding, `simp` turns the postcondition into an existential counterexample
  simp [postcondition, test2_n, test2_a, test2_Expected]
  -- Provide the failing index i = 2
  refine ⟨2, by decide, ?_⟩
  -- At i = 2 the array value is 3, so we need to show 3 ≤ 3
  simp

theorem test3_precondition :
  precondition test3_n test3_a := by
  simp [precondition, test3_a]

theorem test3_postcondition :
  postcondition test3_n test3_a test3_Expected := by
  -- Unfold to a concrete proposition; `simp` turns the iff with `false = true`
  -- into an existence of a counterexample index.
  simp [postcondition, test3_n, test3_a, test3_Expected]
  -- Provide a witness index where the inequality fails.
  refine ⟨0, ?_, ?_⟩
  · decide
  · simp

theorem uniqueness (n : Int) (a : Array Int):
  precondition n a →
  (∀ ret1 ret2,
    postcondition n a ret1 →
    postcondition n a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  -- Reduce to showing ret1 and ret2 have the same truth value w.r.t. `= true`
  apply (Bool.eq_iff_iff).2
  -- Both `ret1 = true` and `ret2 = true` are equivalent to the same proposition
  have h1' : ret1 = true ↔ (∀ i : Nat, i < a.size → a[i]! < n) := by
    simpa [postcondition] using h1
  have h2' : ret2 = true ↔ (∀ i : Nat, i < a.size → a[i]! < n) := by
    simpa [postcondition] using h2
  exact Iff.trans h1' (Iff.symm h2')
end Proof
