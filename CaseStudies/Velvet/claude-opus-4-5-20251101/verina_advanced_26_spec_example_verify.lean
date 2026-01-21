import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def digitToLetters (c : Char) : List Char :=
  match c with
  | '2' => ['a', 'b', 'c']
  | '3' => ['d', 'e', 'f']
  | '4' => ['g', 'h', 'i']
  | '5' => ['j', 'k', 'l']
  | '6' => ['m', 'n', 'o']
  | '7' => ['p', 'q', 'r', 's']
  | '8' => ['t', 'u', 'v']
  | '9' => ['w', 'x', 'y', 'z']
  | _ => []


def isValidDigit (c : Char) : Bool :=
  (digitToLetters c).length > 0


def allValidDigits (s : String) : Bool :=
  s.data.all isValidDigit



def precondition (digits : String) :=
  True



def postcondition (digits : String) (result : List String) :=

  (digits.isEmpty → result = []) ∧

  (¬digits.isEmpty → ¬allValidDigits digits → result = []) ∧

  (¬digits.isEmpty → allValidDigits digits →

    result.length = (digits.data.map (fun c => (digitToLetters c).length)).foldl (· * ·) 1 ∧

    (∀ i : Nat, i < result.length → (result[i]!).length = digits.length) ∧

    (∀ i : Nat, i < result.length →
      ∀ j : Nat, j < digits.length →
        (result[i]!).data[j]! ∈ digitToLetters (digits.data[j]!)) ∧

    result.Nodup ∧

    (∀ combo : List Char, combo.length = digits.length →
      (∀ j : Nat, j < digits.length → combo[j]! ∈ digitToLetters (digits.data[j]!)) →
      combo.asString ∈ result))


def test1_digits : String := ""

def test1_Expected : List String := []

def test2_digits : String := "2"

def test2_Expected : List String := ["a", "b", "c"]

def test4_digits : String := "23"

def test4_Expected : List String := ["ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"]







section Proof
theorem test1_precondition :
  precondition test1_digits := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_digits test1_Expected := by
  unfold postcondition test1_digits test1_Expected
  constructor
  · -- First conjunct: digits.isEmpty → result = []
    intro _
    rfl
  constructor
  · -- Second conjunct: ¬digits.isEmpty → ¬allValidDigits digits → result = []
    intro h
    -- h : ¬"".isEmpty, but "".isEmpty = true, so this is a contradiction
    simp [String.isEmpty] at h
    -- Now h : ¬"".endPos = 0, but "".endPos = 0 by native_decide/rfl
    have : "".endPos = 0 := rfl
    exact absurd this h
  · -- Third conjunct: ¬digits.isEmpty → allValidDigits digits → ...
    intro h
    -- Same contradiction
    simp [String.isEmpty] at h
    have : "".endPos = 0 := rfl
    exact absurd this h

theorem test2_precondition :
  precondition test2_digits := by
  intros; expose_names; exact (trivial); done
end Proof
