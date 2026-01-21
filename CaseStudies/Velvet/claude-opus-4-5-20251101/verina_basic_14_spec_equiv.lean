import Lean
import Mathlib.Tactic

namespace VerinaSpec

def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result
  -- !benchmark @end postcond

end VerinaSpec

namespace LeetProofSpec

-- Helper Functions
-- Using String.contains from Mathlib/Lean stdlib

-- Postcondition clauses
def ensures1 (s : String) (result : Bool) :=
  result = true ↔ (s.contains 'z' ∨ s.contains 'Z')

def ensures2 (s : String) (result : Bool) :=
  result = false ↔ (¬s.contains 'z' ∧ ¬s.contains 'Z')

def precondition (s : String) :=
  True  -- no preconditions as stated in the problem

def postcondition (s : String) (result : Bool) :=
  ensures1 s result ∧ ensures2 s result

end LeetProofSpec

-- Equivalence theorems

theorem precondition_equiv (s : String):
  VerinaSpec.containsZ_precond s ↔ LeetProofSpec.precondition s := by
  sorry

theorem postcondition_equiv (s : String) (result : Bool) (h_precond : VerinaSpec.containsZ_precond s):
  VerinaSpec.containsZ_postcond s result h_precond ↔ LeetProofSpec.postcondition s result := by
  sorry
