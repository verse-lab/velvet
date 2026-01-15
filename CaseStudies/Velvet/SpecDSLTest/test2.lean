import CaseStudies.Velvet.SpecDSL

-- Register forbidden function
register_specdef_forbidden List.filter

section Specs

/--
error: axiom is not allowed in Specs sections
-/
#guard_msgs in
axiom myAxiom : Nat

/--
error: sorry is not allowed in Specs sections
-/
#guard_msgs in
def mylemma (x : Nat) : x ≤ 1 := sorry

/--
error: recursive function 'factorial' is not allowed in Specs sections
-/
#guard_msgs in
def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)

/--
error: 'let rec' (recursive let binding) is not allowed in Specs sections
-/
#guard_msgs in
def testLetRec : Nat :=
  let rec f (x : Nat) := if x = 0 then 0 else f (x - 1)
  f 10

/--
error: recursive function 'fib' is not allowed in Specs sections
-/
#guard_msgs in
def fib (n: Nat) : Nat :=
  if n < 2 then 1 else
  fib (n - 1) + fib (n - 2)
  termination_by n

/--
error: 'List.filter' is not allowed in Specs sections
-/
#guard_msgs in
def invalidFunction (xs : List Nat) : List Nat :=
  List.filter (· > 0) xs

def precondition := True

/--
error: Specs section must contain def postcondition
-/
#guard_msgs in
end Specs
