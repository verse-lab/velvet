import Lean
import Mathlib.Tactic
import Std.Data.HashSet

namespace VerinaSpec

def findFirstRepeatedChar_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    -- Exists repeated char
    cs.count c ≥ 2 ∧
    -- There is no other repeated char before the found one
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    -- There is no repeated char
    List.Pairwise (· ≠ ·) cs
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: Check if character c appears in the list before position i
def appearsBeforePos (chars : List Char) (c : Char) (i : Nat) : Prop :=
  ∃ j : Nat, j < i ∧ j < chars.length ∧ chars[j]! = c

-- Helper: Position i is where we first see a repeated character
-- (chars[i] appeared somewhere before position i, and no earlier position has this property)
def isFirstRepeatPos (chars : List Char) (i : Nat) : Prop :=
  i < chars.length ∧
  appearsBeforePos chars chars[i]! i ∧
  ∀ k : Nat, k < i → ¬appearsBeforePos chars chars[k]! k

-- Helper: Check if any character in the string is repeated
def hasRepeatedChar (chars : List Char) : Prop :=
  ∃ i : Nat, i < chars.length ∧ appearsBeforePos chars chars[i]! i

-- Postcondition clause 1: If result is some c, then c is a repeated character found at the first repeat position
def ensures1 (s : String) (result : Option Char) :=
  ∀ c : Char, result = some c →
    ∃ i : Nat, isFirstRepeatPos s.toList i ∧ s.toList[i]! = c

-- Postcondition clause 2: If result is none, then no character repeats in the string
def ensures2 (s : String) (result : Option Char) :=
  result = none → ¬hasRepeatedChar s.toList

-- Postcondition clause 3: If there is a repeated character, result must be some
def ensures3 (s : String) (result : Option Char) :=
  hasRepeatedChar s.toList → result.isSome

def precondition (s : String) :=
  True  -- no preconditions

def postcondition (s : String) (result : Option Char) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.findFirstRepeatedChar_precond s ↔ LeetProofSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result : Option Char) (h_precond : VerinaSpec.findFirstRepeatedChar_precond s):
  VerinaSpec.findFirstRepeatedChar_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  sorry
