import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def rightShift (l : List Int) (k : Nat) : List Int :=
  if l.length = 0 then l
  else
    let effectiveK := k % l.length
    if effectiveK = 0 then l
    else l.rotate (l.length - effectiveK)

def isStrictlySorted (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l[i]! < l[i + 1]!

def allDistinct (l : List Int) : Prop :=
  l.Nodup

def allPositive (l : List Int) : Prop :=
  ∀ i : Nat, i < l.length → l[i]! > 0



def require1 (nums : List Int) := nums.length > 0
def require2 (nums : List Int) := allDistinct nums
def require3 (nums : List Int) := allPositive nums

def precondition (nums : List Int) :=
  require1 nums ∧ require2 nums ∧ require3 nums



def ensures1 (nums : List Int) (result : Int) :=
  result ≥ 0 → isStrictlySorted (rightShift nums result.toNat)


def ensures2 (nums : List Int) (result : Int) :=
  result ≥ 0 → ∀ k : Nat, k < result.toNat → ¬isStrictlySorted (rightShift nums k)



def ensures3 (nums : List Int) (result : Int) :=
  result = -1 → ∀ k : Nat, ¬isStrictlySorted (rightShift nums k)


def ensures4 (nums : List Int) (result : Int) :=
  result = -1 ∨ (result ≥ 0 ∧ result < nums.length)

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧
  ensures2 nums result ∧
  ensures3 nums result ∧
  ensures4 nums result


def test1_nums : List Int := [3, 4, 5, 1, 2]

def test1_Expected : Int := 2

def test3_nums : List Int := [2, 1, 4]

def test3_Expected : Int := -1

def test5_nums : List Int := [2, 1]

def test5_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  constructor
  · -- require1
    unfold require1 test1_nums
    native_decide
  constructor
  · -- require2
    unfold require2 allDistinct test1_nums
    native_decide
  · -- require3
    unfold require3 allPositive test1_nums
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> native_decide
end Proof
