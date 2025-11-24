import CaseStudies.Velvet.Std

section

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/--
warning: Invariant annotations are not specified, so the loop invariant is assumed to be just `True`.
To turn off this warning, use `set_option loom.linter.warnings false`.
-/
#guard_msgs in
method zero_invariant (mut n : Nat) return (res : Nat) do
  while n > 0 do
    n := n - 1
  return n

end

section
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/--
warning: Decreasing annotations are not checked in partial correctness semantics
To turn off this warning, use `set_option loom.linter.warnings false`.
-/
#guard_msgs in
method redundant_decreasing (mut n : Nat) return (res : Nat) do
  while n > 0
    invariant n >= 0
    decreasing n
  do
    n := n - 1
  return n

end

section
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

/--
error: Decreasing annotations are required in total correctness semantics
To turn off this error, use `set_option loom.linter.errors false`.
-/
#guard_msgs in
method missing_decreasing (mut n : Nat) return (res : Nat) do
  while n > 0
    invariant n >= 0
    done_with n = 0
  do
    n := n - 1
  return n

end

section
set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

set_option loom.linter.errors false
set_option loom.linter.warnings false

#guard_msgs in
method no_msg (mut n : Nat) return (res : Nat) do
  while n > 0 do
    n := n - 1
  return n
end
