import Lean
import Mathlib.Tactic

namespace VerinaSpec

def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ x > 0 ∧ x < a.size  -- x must be at least 1 (as stated in description)
  -- !benchmark @end precond

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  -- !benchmark @start postcond
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper: check if m is the maximum of the first x elements
def isMaxOfFirstX (a : Array Int) (x : Nat) (m : Int) : Prop :=
  (∃ i : Nat, i < x ∧ a[i]! = m) ∧
  (∀ i : Nat, i < x → a[i]! ≤ m)

-- Helper: check if there exists an element from index x onward that exceeds m
def existsExceedingM (a : Array Int) (x : Nat) (m : Int) : Prop :=
  ∃ i : Nat, x ≤ i ∧ i < a.size ∧ a[i]! > m

-- Helper: p is the first index >= x where a[p] > m
def isFirstExceedingIndex (a : Array Int) (x : Nat) (m : Int) (p : Nat) : Prop :=
  x ≤ p ∧ p < a.size ∧ a[p]! > m ∧ (∀ j : Nat, x ≤ j → j < p → a[j]! ≤ m)

-- Precondition: array is nonempty and x is valid (1 ≤ x < a.size)
def precondition (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ 1 ≤ x ∧ x < a.size

-- Postcondition: m is max of first x elements, p is determined by the ordering condition
def postcondition (a : Array Int) (x : Nat) (result : Int × Nat) : Prop :=
  let m := result.1
  let p := result.2
  -- m is the maximum of the first x elements
  isMaxOfFirstX a x m ∧
  -- p is in valid range [x, a.size)
  x ≤ p ∧ p < a.size ∧
  -- Either p is the first index >= x where a[p] > m, or no such index exists and p = a.size - 1
  ((existsExceedingM a x m ∧ isFirstExceedingIndex a x m p) ∨
   (¬existsExceedingM a x m ∧ p = a.size - 1))

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (a : Array Int) (x : Nat):
  VerinaSpec.onlineMax_precond a x ↔ LeetProofSpec.precondition a x := by
  sorry

theorem postcondition_equiv (a : Array Int) (x : Nat) (result : Int × Nat) (h_precond : VerinaSpec.onlineMax_precond a x):
  VerinaSpec.onlineMax_postcond a x result h_precond ↔ LeetProofSpec.postcondition a x result := by
  sorry
