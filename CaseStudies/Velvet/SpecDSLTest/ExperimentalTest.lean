import CaseStudies.Velvet.Std
import CaseStudies.Velvet.Attributes
import CaseStudies.Velvet.SpecDSLExperimental

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

namespace TestCases

attribute [allowedSymbol] List.take List.map List.filter

-- Test cases
spec foo1 : Int := 5


spec fib (n: Nat) : Nat :=
  if n < 2 then 1 else
  fib (n - 1) + fib (n - 2)
  termination_by n

-- With type parameters
spec foo3 {α : Type} (x : α) : α := x

-- With pattern matching
/--
error: Unsupported syntax, only allowed syntax is with ':=' 
-/
#guard_msgs in 
spec foo4 : Nat → Nat
  | 0 => 0
  | n + 1 => n



@[velvetSpecHelper] def foo := 1
@[velvetSpecHelper] def bar := 2

/--
info: Velvet Helpers: [TestCases.foo1, TestCases.fib, TestCases.foo3, TestCases.foo, TestCases.bar]
-/
#guard_msgs in
#printVelvetHelpers 

namespace Impl


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
error: Forbidden names (TestCases.fib) used in body, this is not allowed
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

end TestCases
