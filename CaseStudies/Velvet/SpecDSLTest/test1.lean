import CaseStudies.Velvet.Std
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Comprehensive test of specdef functionality

namespace Test1
section Specs

register_specdef_allow_recursion

def fib (n: Nat) : Nat :=
  if n < 2 then 1 else
  fib (n - 1) + fib (n - 2)
  termination_by n

def precondition (n: Nat) := True
def postcondition (n: Nat) (result : Nat) :=
  result = fib n

end Specs

section Impl
method fib_iterative' (n: Nat) return (res: Nat)
    ensures res = fib n
    do
    if n = 0 then
        return 0
    else if n = 1 then
        return 1
    else
        let mut a := 0
        let mut b := 1
        let mut i := 2
        while i <= n
            invariant i ≤ n + 1
            invariant a = fib (i - 2)
            invariant b = fib (i - 1)
            done_with i = n + 1
        do
            let next_fib := a + b
            a := b
            b := next_fib
            i := i + 1
        return b

#eval (fib_iterative' 2).run


/--
error: Forbidden names (Test1.fib) used in body, this is not allowed
-/
#guard_msgs in
method fib_trivial (n: Nat) return (res: Nat)
  ensures res = fib n
  do
    if n < 2 then
      return n
    else
      return fib n

end Impl

end Test1

namespace Test2

section Specs

def precondition (n : Nat) := n < 100
def postcondition (n : Nat) (result : Nat) := result > n ∧ result < n + 10

end Specs

end Test2

#print Test1.precondition
#check Test1.postcondition
#check Test2.precondition
#check Test2.postcondition
