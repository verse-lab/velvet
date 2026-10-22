import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

namespace Velvet.Examples.IO.Policy

inductive Console where
  | stdin (e : IOEvent String String IOErr)
  | stdout (e : IOEvent String String IOErr)

instance : Embeds Stdin Console where
  inj _ e := .stdin e
  proj
    | .stdin e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Embeds Stdout Console where
  inj _ e := .stdout e
  proj
    | .stdout e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Distinct Stdin Stdout Console := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

@[simp, grind =]
theorem inj_stdin (e : IOEvent String String IOErr) : (Embeds.inj Stdin.mk e : Console) = .stdin e := rfl

@[simp, grind =]
theorem inj_stdout (e : IOEvent String String IOErr) : (Embeds.inj Stdout.mk e : Console) = .stdout e := rfl

instance : Model stdinP Stdin Console where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model stdoutP Stdout Console where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

def inputClosed (h : Trace Console) : Prop := Console.stdin (.read (.error .eof)) ∈ h.events

def noOutputAfterClose (h : Trace Console) : Prop :=
  match h.events.getLast? with
  | some (.stdout (.write _ _)) => ¬ inputClosed h
  | _ => True

instance : Policy Console := ⟨noOutputAfterClose⟩

@[simp, grind =]
theorem allow_eq (h : Trace Console) : Policy.allow h = noOutputAfterClose h := rfl

@[simp, grind =]
theorem noOutputAfterClose_stdout (h : Trace Console) (o : String) (r : WriteOutcome IOErr) :
    noOutputAfterClose (h.recordFor Stdout.mk (.write o r)) = ¬ inputClosed (h.recordFor Stdout.mk (.write o r)) := by
  simp [noOutputAfterClose]

@[simp, grind =]
theorem inputClosed_recordFor_stdin_ok (h : Trace Console) (s : String) :
    inputClosed (h.recordFor Stdin.mk (.read (.ok s))) = inputClosed h := by
  simp [inputClosed]

@[simp, grind =]
theorem inputClosed_recordFor_stdout (h : Trace Console) (e : IOEvent String String IOErr) :
    inputClosed (h.recordFor Stdout.mk e) = inputClosed h := by
  simp [inputClosed]

abbrev Prog := IOProg Console IOErr

method echo returns (r : Unit) in Prog
  requires (h : Trace Console) => ¬ inputClosed h
  signals (e : IOErr) (h : Trace Console) => e = .eof
  signals False
  ensures (h : Trace Console) => ¬ inputClosed h
do
  let s ← read Stdin.mk
  write Stdout.mk s

prove_correct echo by
  velvet_vcgen [echo] with finish

method greet returns (r : Unit) in Prog
  requires (h : Trace Console) => ¬ inputClosed h
  signals (e : IOErr) (h : Trace Console) => e = .eof
  signals False
  ensures (h : Trace Console) => ¬ inputClosed h
do
  write Stdout.mk "name?"
  let s ← read Stdin.mk
  write Stdout.mk s!"hello {s}"

prove_correct greet by
  velvet_vcgen [greet] with finish

end Velvet.Examples.IO.Policy
