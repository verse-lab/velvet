import CaseStudies.Velvet.SpecDSL

-- Comprehensive test of specdef functionality

-- Test 1: Basic pre/post conditions with simple function

namespace Test1
section Specs

def precondition (n : Nat) := n > 0
def postcondition (n : Nat) (result : Nat) := result >= n

end Specs

end Test1

namespace Test2

section Specs

def precondition (n : Nat) := n < 100
def postcondition (n : Nat) (result : Nat) := result > n ∧ result < n + 10

end Specs

end Test2

#check Test1.precondition
#check Test1.postcondition
#check Test2.precondition
#check Test2.postcondition
