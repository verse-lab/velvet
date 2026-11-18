import Velvet.Examples.IO.Setup

open Std.WP Lean.Order IOProg

/-! A rule spanning two channels, no output after stdin hits EOF, stated in the specs. -/

namespace Velvet.Examples.IO.CrossChannel

inductive Console where
  | stdin (e : IOEvent String String IOErr)
  | stdout (e : IOEvent String String IOErr)

instance : Provide Console Stdin where
  inj _ e := .stdin e
  proj
    | .stdin e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Provide Console Stdout where
  inj _ e := .stdout e
  proj
    | .stdout e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Distinguish Console Stdin Stdout := ⟨fun _ _ => rfl⟩
instance : Distinguish Console Stdout Stdin := ⟨fun _ _ => rfl⟩

@[simp, grind =]
theorem inj_stdin (e : IOEvent String String IOErr) : (Provide.inj Stdin.mk e : Console) = .stdin e := rfl

@[simp, grind =]
theorem inj_stdout (e : IOEvent String String IOErr) : (Provide.inj Stdout.mk e : Console) = .stdout e := rfl

instance [Clients] : PureModel Stdin stdinP Console where
  call t ch o := stdinModel (t.traceOf ch) o
  call_ok _ ch o := stdinModel_ok ch _ o

instance : PureModel Stdout stdoutP Console where
  call _ _ o := stdoutModel o
  call_ok _ ch o := stdoutModel_ok ch _ o

def inputClosed (h : Trace Console) : Prop := Console.stdin (.read (.error .eof)) ∈ h.events

@[simp, grind =]
theorem inputClosed_recordFor_stdin_ok (h : Trace Console) (s : String) :
    inputClosed (h.recordFor Stdin.mk (.read (.ok s))) = inputClosed h := by
  simp [inputClosed]

@[simp, grind =]
theorem inputClosed_recordFor_stdin_eof (h : Trace Console) :
    inputClosed (h.recordFor Stdin.mk (.read (.error .eof))) = True := by
  simp [inputClosed, Trace.recordFor]

@[simp, grind =]
theorem inputClosed_recordFor_stdout (h : Trace Console) (e : IOEvent String String IOErr) :
    inputClosed (h.recordFor Stdout.mk e) = inputClosed h := by
  simp [inputClosed]

abbrev Prog := IOProg Console IOErr

method echo [Clients] returns (line : String) in Prog
  given (h₀ : Trace Console)
  requires (h : Trace Console) => h = h₀ ∧ ¬ inputClosed h
  signals (e : IOErr) (h : Trace Console) =>
    e = .eof ∧ (inputClosed h → h.traceOf Stdout.mk = h₀.traceOf Stdout.mk)
  signals True
  ensures (h : Trace Console) =>
    ¬ inputClosed h ∧
    h.traceOf Stdin.mk = h₀.traceOf Stdin.mk ++ [.read (.ok line)] ∧
      h.traceOf Stdout.mk = h₀.traceOf Stdout.mk ++ [.write line (.ok ())]
do
  let s ← read Stdin.mk
  write Stdout.mk s
  return s

prove_correct echo by
  velvet_vcgen [echo] with finish

method greet [Clients] returns (name : String) in Prog
  given (h₀ : Trace Console)
  requires (h : Trace Console) => h = h₀ ∧ ¬ inputClosed h
  signals (e : IOErr) (h : Trace Console) =>
    e = .eof ∧ (inputClosed h → h.traceOf Stdout.mk = h₀.traceOf Stdout.mk ++ [.write "name?" (.ok ())])
  signals True
  ensures (h : Trace Console) =>
    ¬ inputClosed h ∧
    h.traceOf Stdin.mk = h₀.traceOf Stdin.mk ++ [.read (.ok name)] ∧
      h.traceOf Stdout.mk = h₀.traceOf Stdout.mk ++ [.write "name?" (.ok ()), .write s!"hello {name}" (.ok ())]
do
  write Stdout.mk "name?"
  let s ← read Stdin.mk
  write Stdout.mk s!"hello {s}"
  return s

prove_correct greet by
  velvet_vcgen [greet] with finish

end Velvet.Examples.IO.CrossChannel
