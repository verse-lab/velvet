import CaseStudies.Velvet.Std
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Test 4: Check if non-recursive functions from Specs can be used in method bodies

namespace Test4

section Specs

-- Non-recursive functions that should get velvetSpecHelper attribute
def add (x y : Nat) : Nat := x + y
def multiply (x y : Nat) : Nat := x * y
def isEven (n : Nat) : Bool := n % 2 = 0
def increment (x : Nat) : Nat := x + 1

def precondition (x y : Nat) := True
def postcondition (x y : Nat) (result : Nat) := True

end Specs

namespace Impl

/--
error: Forbidden names (Test4.add) used in body, this is not allowed
-/
#guard_msgs in
method testAdd (x : Nat) (y : Nat) return (res: Nat)
    ensures res = x + y
    do
    -- This should be forbidden if add has velvetSpecHelper attribute
    return add x y

/--
error: Forbidden names (Test4.multiply) used in body, this is not allowed
-/
#guard_msgs in
method testMultiply (x : Nat) (y : Nat) return (res: Nat)
    ensures res = x * y
    do
    return multiply x y

/--
error: Forbidden names (Test4.isEven) used in body, this is not allowed
-/
#guard_msgs in
method testIsEven (n : Nat) return (res: Bool)
    ensures res = (n % 2 = 0)
    do
    return isEven n

/--
error: Forbidden names (Test4.increment) used in body, this is not allowed
-/
#guard_msgs in
method testIncrement (x : Nat) return (res: Nat)
    ensures res = x + 1
    do
    return increment x

-- Test 5: This should work - not using any Specs functions
method testValid (x : Nat) (y : Nat) return (res: Nat)
    ensures res = x + y + 1
    do
    let sum := x + y
    return sum + 1

end Impl

end Test4

-- Print function definitions to check attributes
#print Test4.add
#print Test4.multiply
#print Test4.isEven
#print Test4.increment
