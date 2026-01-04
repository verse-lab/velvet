import CaseStudies.Velvet.SpecDSL

-- Enable recursion checking
register_specdef_forbid_recursion

-- Register forbidden function
register_specdef_forbidden List.filter

specdef TestSection

-- This should error: "axiom is not allowed in specdef sections"
axiom myAxiom : Nat

-- This should error: "sorry is not allowed in specdef sections"
def mylemma (x : Nat) : x ≤ 1 := sorry

-- This should error: recursive function is not allowed
def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)

-- This should error: let rec is not allowed
def testLetRec : Nat :=
  let rec f (x : Nat) := if x = 0 then 0 else f (x - 1)
  f 10

-- This should error: "'List.filter' is not allowed in specdef sections"
def invalidFunction (xs : List Nat) : List Nat :=
  List.filter (· > 0) xs

def_pre := True

-- This should error: specdef section must contain def_post
specend TestSection
