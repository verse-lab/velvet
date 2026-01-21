import Lean
import Mathlib.Tactic

namespace VerinaSpec

def only_once_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0

def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  -- !benchmark @start postcond
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: no restrictions on input
def precondition (a : Array Int) (key : Int) :=
  True

-- Postcondition: result is true iff key appears exactly once in array
def postcondition (a : Array Int) (key : Int) (result : Bool) :=
  result = (a.count key == 1)

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (key : Int):
  VerinaSpec.only_once_precond a key ↔ LeetProofSpec.precondition a key := by
  sorry

theorem postcondition_equiv (a : Array Int) (key : Int) (result : Bool) (h_precond : VerinaSpec.only_once_precond a key):
  VerinaSpec.only_once_postcond a key result h_precond ↔ LeetProofSpec.postcondition a key result := by
  sorry
