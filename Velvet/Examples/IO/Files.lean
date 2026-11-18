import Velvet
import Velvet.Core.FreerMonad.IO

open Std.WP Lean.Order IOProg

/-! Requests carry their reply type: `check p : FsOp Bool` and `open p : FsOp File`, where a `File`
is a channel of its own. The contracts refer to an arbitrary `FsWorld`, so what is proved about a
program holds for every disk. Reading an open file whose path is on the disk, or closing an open file,
cannot fail, so `readFile` never fails and cannot leave a file open. -/

namespace Velvet.Examples.IO.Files

inductive FsErr where
  | eof
  | notFound
deriving DecidableEq

structure Fs
deriving DecidableEq

structure File where
  fd : Nat
  path : String
deriving DecidableEq

/-- What is stored at each path. -/
class FsWorld where
  contents : String → Option String

inductive FsOp : Type → Type where
  | check (p : String) : FsOp Bool
  | open (p : String) : FsOp File

inductive FsEv where
  | checked (p : String) (r : Except FsErr Bool)
  | opened (p : String) (r : Except FsErr File)

instance : Channel Fs FsOp FsEv FsErr where
  log o r := match o, r with
    | .check p, r => .checked p r
    | .open p, r => .opened p r

inductive FileOp : Type → Type where
  | read : FileOp String
  | close : FileOp Unit

inductive FileEv where
  | read (r : Except FsErr String)
  | closed (r : Except FsErr Unit)

instance : Channel File FileOp FileEv FsErr where
  log o r := match o, r with
    | .read, r => .read r
    | .close, r => .closed r

@[simp, grind =] theorem log_check (p : String) (r) : Channel.log Fs (.check p) r = FsEv.checked p r := rfl
@[simp, grind =] theorem log_open (p : String) (r) : Channel.log Fs (.open p) r = FsEv.opened p r := rfl
@[simp, grind =] theorem log_read (r) : Channel.log File .read r = FileEv.read r := rfl
@[simp, grind =] theorem log_close (r) : Channel.log File .close r = FileEv.closed r := rfl

/-- The files `fs` has handed out. -/
def opened (h : List FsEv) : List File :=
  h.filterMap fun
    | .opened _ (.ok f) => some f
    | _ => none

/-- Whether the file has been closed. -/
def closed (h : List FileEv) : Bool :=
  h.any fun
    | .closed (.ok _) => true
    | _ => false

def fsP [FsWorld] : Protocol Fs FsOp FsEv FsErr where
  allow _ _ _ := True
  onReply _ h o r := match o, r with
    | .check p, .ok b => (b = true ↔ FsWorld.contents p ≠ none)
    | .open p, .ok f => f.path = p ∧ f ∉ opened h ∧ FsWorld.contents p ≠ none
    | .check _, .error _ => False
    | .open p, .error e => e = .notFound ∧ FsWorld.contents p = none

def fileP [FsWorld] : Protocol File FileOp FileEv FsErr where
  allow _ h _ := closed h = false
  onReply f h o r := match o, r with
    | .read, .ok s => FsWorld.contents f.path = some s
    | .read, .error e => e = .eof ∧ (closed h = true ∨ FsWorld.contents f.path = none)
    | .close, .ok _ => True
    | .close, .error e => e = .eof ∧ closed h = true

section Lemmas
variable [FsWorld]

@[simp, grind =] theorem fsP_allow (ch h) (o : FsOp α) : fsP.allow ch h o = True := rfl
@[simp, grind =] theorem fsP_onReply_check (ch h) (p : String) (b : Bool) :
    fsP.onReply ch h (.check p) (.ok b) = (b = true ↔ FsWorld.contents p ≠ none) := rfl
@[simp, grind =] theorem fsP_onReply_open (ch h) (p : String) (f : File) :
    fsP.onReply ch h (.open p) (.ok f) = (f.path = p ∧ f ∉ opened h ∧ FsWorld.contents p ≠ none) := rfl
@[simp, grind =] theorem fsP_onReply_check_error (ch h) (p : String) (e : FsErr) :
    fsP.onReply ch h (.check p) (.error e) = False := rfl
@[simp, grind =] theorem fsP_onReply_open_error (ch h) (p : String) (e : FsErr) :
    fsP.onReply ch h (.open p) (.error e) = (e = .notFound ∧ FsWorld.contents p = none) := rfl

@[simp, grind =] theorem fileP_allow (f h) (o : FileOp α) : fileP.allow f h o = (closed h = false) := rfl
@[simp, grind =] theorem fileP_onReply_read (f : File) (h) (s : String) :
    fileP.onReply f h .read (.ok s) = (FsWorld.contents f.path = some s) := rfl
@[simp, grind =] theorem fileP_onReply_close (f h) (u : Unit) : fileP.onReply f h .close (.ok u) = True := rfl
@[simp, grind =] theorem fileP_onReply_read_error (f : File) (h) (e : FsErr) :
    fileP.onReply f h .read (.error e) = (e = .eof ∧ (closed h = true ∨ FsWorld.contents f.path = none)) := rfl
@[simp, grind =] theorem fileP_onReply_close_error (f h) (e : FsErr) :
    fileP.onReply f h .close (.error e) = (e = .eof ∧ closed h = true) := rfl

end Lemmas

@[simp, grind =] theorem opened_checked (h) (p : String) (r : Except FsErr Bool) :
    opened (h ++ [.checked p r]) = opened h := by
  cases r <;> simp [opened]
@[simp, grind =] theorem opened_opened (h) (p : String) (f : File) :
    opened (h ++ [.opened p (.ok f)]) = opened h ++ [f] := by
  simp [opened]
@[simp, grind =] theorem closed_nil : closed [] = false := rfl
@[simp, grind =] theorem closed_read (h) (r : Except FsErr String) : closed (h ++ [.read r]) = closed h := by
  simp [closed]
@[simp, grind =] theorem closed_closed (h) (u : Unit) : closed (h ++ [.closed (.ok u)]) = true := by
  simp [closed]

abbrev Ev := (Fs × FsEv) ⊕ (File × FileEv)

@[simp, grind =] theorem inj_fs (fs : Fs) (e : FsEv) : (Provide.inj fs e : Ev) = .inl (fs, e) := rfl
@[simp, grind =] theorem inj_file (f : File) (e : FileEv) : (Provide.inj f e : Ev) = .inr (f, e) := rfl

/-! ## A model, answering from the world -/

/-- A file at `p` whose fd is one past every fd handed out so far. -/
def nextFile (h : List FsEv) (p : String) : File := ⟨((opened h).map (·.fd)).sum + 1, p⟩

theorem le_sum_of_mem {l : List Nat} {x : Nat} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have := ih hx; simp; omega

theorem nextFile_fresh (h : List FsEv) (p : String) : nextFile h p ∉ opened h := fun hm => by
  have := le_sum_of_mem (List.mem_map_of_mem (f := (·.fd)) hm)
  simp only [nextFile] at this
  omega

instance [FsWorld] : PureModel Fs fsP Ev where
  call t ch o := match o with
    | .check p => .ok (FsWorld.contents p).isSome
    | .open p => if (FsWorld.contents p).isSome then .ok (nextFile (t.traceOf ch) p) else .error .notFound
  call_ok t ch o := by
    cases o with
    | check p =>
      show fsP.onReply ch _ (.check p) (.ok _)
      cases h : FsWorld.contents p <;> simp [h]
    | «open» p =>
      show fsP.onReply ch _ (.open p) (if _ then _ else _)
      split
      · rename_i hc
        exact ⟨rfl, nextFile_fresh _ _, by cases h : FsWorld.contents p <;> simp_all⟩
      · rename_i hc
        exact ⟨rfl, by cases h : FsWorld.contents p <;> simp_all⟩

instance [FsWorld] : PureModel File fileP Ev where
  call t f o := match o with
    | .read =>
      match FsWorld.contents f.path with
      | some s => if closed (t.traceOf f) then .error .eof else .ok s
      | none => .error .eof
    | .close => .ok ()
  call_ok t f o := by
    cases o with
    | read =>
      show fileP.onReply f _ .read (match FsWorld.contents f.path with | some s => _ | none => _)
      split
      · rename_i s hs
        split
        · exact ⟨rfl, .inl ‹_›⟩
        · exact hs
      · exact ⟨rfl, .inr ‹_›⟩
    | close => trivial

/-! ## Reading a file -/

/-- Returns what is stored at `p`, or `none` when nothing is. It never fails, and the trace it leaves
is exactly a check, and when the file exists, opening a fresh file, reading it, and closing it. -/
method readFile [FsWorld] (fs : Fs) (p : String) returns (r : Option String) in IOProg Ev FsErr
  given (h₀ : Trace Ev)
  requires (h : Trace Ev) => h = h₀ ∧ ∀ f : File, h.traceOf f ≠ [] → f ∈ opened (h.traceOf fs)
  signals (e : FsErr) (h : Trace Ev) => False
  signals False
  ensures (h : Trace Ev) => r = FsWorld.contents p
  ensures (h : Trace Ev) => ∀ f : File, h.traceOf f ≠ [] → f ∈ opened (h.traceOf fs)
  ensures (h : Trace Ev) => r = none → h.events = h₀.events ++ [.inl (fs, .checked p (.ok false))]
  ensures (h : Trace Ev) => ∀ s, r = some s → ∃ f : File, f ∉ opened (h₀.traceOf fs) ∧
    h.events = h₀.events ++
      [.inl (fs, .checked p (.ok true)), .inl (fs, .opened p (.ok f)),
        .inr (f, .read (.ok s)), .inr (f, .closed (.ok ()))]
do
  let ok ← call fs (.check p)
  if ok then
    let f ← call fs (.open p)
    let s ← call f .read
    call f .close
    return some s
  else
    return none

prove_correct readFile by
  velvet_vcgen [readFile]
  all_goals grind (ematch := 10)

end Velvet.Examples.IO.Files
