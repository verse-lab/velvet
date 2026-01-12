import CaseStudies.Velvet.SpecDSL

section Specs

register_specdef_allow_recursion

def factorial (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => (n' + 1) * factorial n'

def precondition (n: Nat) := n % 2 = 1

def postcondition (n: Nat) (result: Nat) := result > factorial n ∧ result % 10 = 1

end Specs
