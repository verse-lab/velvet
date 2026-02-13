import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    isEven: determine whether a given integer is even
    Natural language breakdown:
    1. The input is an integer n.
    2. The output is a Boolean.
    3. The output is true exactly when n is even.
    4. The output is false exactly when n is odd.
    5. Evenness for integers can be characterized by remainder modulo 2 being 0.
    6. There are no preconditions: the function is defined for all integers.
-/

@[grind]
def IntIsEven (n : Int) : Prop := n % 2 = 0

section Impl
method isEven (n : Int)
  return (result : Bool)
  ensures result = true ↔ IntIsEven n
  do
  if n % 2 = 0 then
    return true
  else
    return false
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct isEven by
  loom_solve
end Proof
