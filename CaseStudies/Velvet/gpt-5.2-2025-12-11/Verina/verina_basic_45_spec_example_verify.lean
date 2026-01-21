import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def isEven (z : Int) : Bool := (z % 2) == 0

def isOdd (z : Int) : Bool := (z % 2) != 0




def precondition (lst : List Int) : Prop :=
  (lst.find? isEven).isSome ∧ (lst.find? isOdd).isSome



def postcondition (lst : List Int) (result : Int) : Prop :=
  ∃ (e : Int) (o : Int),
    lst.find? isEven = some e ∧
    lst.find? isOdd = some o ∧
    result = e * o


def test1_lst : List Int := [2, 3, 4, 5]

def test1_Expected : Int := 6

def test3_lst : List Int := [1, 2, 5, 4]

def test3_Expected : Int := 2

def test6_lst : List Int := [4, -5, 8, 3]

def test6_Expected : Int := -20







section Proof
theorem test1_precondition :
  precondition test1_lst := by
  unfold precondition test1_lst
  constructor
  · -- even exists (2 is even)
    simp [List.find?_cons, isEven]
  · -- odd exists (3 is odd)
    simp [List.find?_cons, isOdd, isEven]

theorem test1_postcondition :
  postcondition test1_lst test1_Expected := by
  unfold postcondition
  -- pick the first even and first odd elements in the list
  refine ⟨2, 3, ?_, ?_, ?_⟩
  · -- find? isEven [2,3,4,5] = some 2
    simp [test1_lst, List.find?_cons, isEven]
  · -- find? isOdd [2,3,4,5] = some 3
    simp [test1_lst, List.find?_cons, isOdd]
  · -- 6 = 2 * 3
    simp [test1_Expected]

theorem test3_precondition :
  precondition test3_lst := by
  unfold precondition test3_lst
  constructor
  · -- even exists
    simp [List.find?_cons, isEven]
  · -- odd exists
    simp [List.find?_cons, isOdd]

theorem test3_postcondition :
  postcondition test3_lst test3_Expected := by
  unfold postcondition
  refine ⟨2, 1, ?_, ?_, ?_⟩
  · -- find first even
    simp [test3_lst, isEven]
  · -- find first odd
    simp [test3_lst, isOdd]
  · -- result = e * o
    simp [test3_Expected]

theorem test6_precondition :
  precondition test6_lst := by
  unfold precondition test6_lst
  constructor
  · -- even exists: 4 is even, so find? returns some 4
    -- Use the existence characterization of `find?` being `isSome`.
    refine (List.find?_isSome).2 ?_
    refine ⟨4, ?_, ?_⟩
    · simp [test6_lst]
    · simp [isEven]
  · -- odd exists: -5 is odd, so find? returns some (-5)
    refine (List.find?_isSome).2 ?_
    refine ⟨-5, ?_, ?_⟩
    · simp [test6_lst]
    · simp [isOdd]

theorem test6_postcondition :
  postcondition test6_lst test6_Expected := by
  unfold postcondition
  refine ⟨4, -5, ?_, ?_, ?_⟩
  · -- find? isEven
    decide
  · -- find? isOdd
    decide
  · -- expected value
    decide

theorem uniqueness (lst : List Int):
  precondition lst →
  (∀ ret1 ret2,
    postcondition lst ret1 →
    postcondition lst ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨e1, o1, he1, ho1, hr1⟩
  rcases hpost2 with ⟨e2, o2, he2, ho2, hr2⟩
  have he : e1 = e2 := by
    have : (some e1 : Option Int) = some e2 := by
      exact (Eq.trans (Eq.symm he1) he2)
    exact (Option.some_inj.mp this)
  have ho : o1 = o2 := by
    have : (some o1 : Option Int) = some o2 := by
      exact (Eq.trans (Eq.symm ho1) ho2)
    exact (Option.some_inj.mp this)
  calc
    ret1 = e1 * o1 := hr1
    _ = e2 * o2 := by simp [he, ho]
    _ = ret2 := by simpa [hr2]
end Proof
