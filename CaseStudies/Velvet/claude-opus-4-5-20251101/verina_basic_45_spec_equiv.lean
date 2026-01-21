import Lean
import Mathlib.Tactic

namespace VerinaSpec

def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none

def findProduct_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
  -- !benchmark @end precond

def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  -- !benchmark @start postcond
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions

-- Check if an integer is even
def isEven (n : Int) : Prop := n % 2 = 0

-- Check if an integer is odd
def isOdd (n : Int) : Prop := n % 2 ≠ 0

-- Predicate: element at index i is the first even number in the list
def isFirstEvenAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isEven lst[i]! ∧
  ∀ j : Nat, j < i → ¬isEven lst[j]!

-- Predicate: element at index i is the first odd number in the list
def isFirstOddAt (lst : List Int) (i : Nat) : Prop :=
  i < lst.length ∧
  isOdd lst[i]! ∧
  ∀ j : Nat, j < i → ¬isOdd lst[j]!

-- Precondition: list contains at least one even and at least one odd number
def require1 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isEven x

def require2 (lst : List Int) : Prop :=
  ∃ x ∈ lst, isOdd x

-- Postcondition: result is product of first even and first odd
def ensures1 (lst : List Int) (result : Int) : Prop :=
  ∃ i j : Nat,
    isFirstEvenAt lst i ∧
    isFirstOddAt lst j ∧
    result = lst[i]! * lst[j]!

def precondition (lst : List Int) : Prop :=
  require1 lst ∧ require2 lst

def postcondition (lst : List Int) (result : Int) : Prop :=
  ensures1 lst result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (lst : List Int):
  VerinaSpec.findProduct_precond lst ↔ LeetProofSpec.precondition lst := by
  sorry

theorem postcondition_equiv (lst : List Int) (result : Int) (h_precond : VerinaSpec.findProduct_precond lst):
  VerinaSpec.findProduct_postcond lst result h_precond ↔ LeetProofSpec.postcondition lst result := by
  sorry
