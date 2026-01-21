import Lean
import Mathlib.Tactic

namespace VerinaSpec

def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  -- !benchmark @start precond
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l
  -- !benchmark @end precond

def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  -- !benchmark @start postcond
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Precondition: valid bounds for all parameters
def precondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) :=
  atPos ≤ l ∧ l ≤ oline.size ∧ p ≤ nl.size

-- Postcondition clauses:
-- 1. The result has the correct length
def ensures1 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  result.size = l + p

-- 2. Characters before atPos come from oline unchanged
def ensures2 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, i < atPos → result[i]! = oline[i]!

-- 3. Characters at positions atPos to atPos + p - 1 come from nl
def ensures3 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, i < p → result[atPos + i]! = nl[i]!

-- 4. Characters from atPos onwards in oline are shifted right by p positions
def ensures4 (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ∀ i : Nat, atPos ≤ i → i < l → result[i + p]! = oline[i]!

def postcondition (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) :=
  ensures1 oline l nl p atPos result ∧
  ensures2 oline l nl p atPos result ∧
  ensures3 oline l nl p atPos result ∧
  ensures4 oline l nl p atPos result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat):
  VerinaSpec.insert_precond oline l nl p atPos ↔ LeetProofSpec.precondition oline l nl p atPos := by
  sorry

theorem postcondition_equiv (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result : Array Char) (h_precond : VerinaSpec.insert_precond oline l nl p atPos):
  VerinaSpec.insert_postcond oline l nl p atPos result h_precond ↔ LeetProofSpec.postcondition oline l nl p atPos result := by
  sorry
