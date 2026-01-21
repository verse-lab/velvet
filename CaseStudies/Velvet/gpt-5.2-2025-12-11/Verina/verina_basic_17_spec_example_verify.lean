import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def charsLoweredPointwise (s : String) (t : String) : Prop :=
  let sl := s.toList
  let tl := t.toList
  tl.length = sl.length ∧
    ∀ (i : Nat), i < sl.length → tl[i]! = Char.toLower (sl[i]!)

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  charsLoweredPointwise s result


def test1_s : String := "Hello, World!"

def test1_Expected : String := "hello, world!"

def test4_s : String := ""

def test4_Expected : String := ""

def test6_s : String := "MixedCASE123"

def test6_Expected : String := "mixedcase123"







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition
  unfold charsLoweredPointwise
  -- Reduce everything to computation on concrete lists of characters.
  -- The remaining goal is decidable and can be discharged by native computation.
  native_decide

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  simp [postcondition, charsLoweredPointwise, test4_s, test4_Expected]

theorem test6_precondition :
  precondition test6_s := by
  intros; expose_names; exact (trivial); done

theorem test6_postcondition :
  postcondition test6_s test6_Expected := by
  unfold postcondition charsLoweredPointwise
  decide

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hsPre
  intro ret1 ret2 hpost1 hpost2
  dsimp [precondition] at _hsPre
  dsimp [postcondition, charsLoweredPointwise] at hpost1 hpost2
  set sl : List Char := s.toList
  set tl1 : List Char := ret1.toList
  set tl2 : List Char := ret2.toList
  rcases hpost1 with ⟨hlen1, hpt1⟩
  rcases hpost2 with ⟨hlen2, hpt2⟩
  have hlen12 : tl1.length = tl2.length := by
    exact Eq.trans hlen1 (Eq.symm hlen2)
  have hlist : tl1 = tl2 := by
    apply List.ext_getElem hlen12
    intro i hi1 hi2
    have hisl : i < sl.length := by
      exact Nat.lt_of_lt_of_eq hi1 hlen1
    have ht1 : tl1[i]! = Char.toLower (sl[i]!) := hpt1 i hisl
    have ht2 : tl2[i]! = Char.toLower (sl[i]!) := hpt2 i hisl
    have ht : tl1[i]! = tl2[i]! := by
      exact Eq.trans ht1 ht2.symm
    -- getElem! is definitional for lists, so we can rewrite both sides
    simpa [List.get!_eq_getElem!, hi1, hi2] using ht
  exact String.ext hlist
end Proof
