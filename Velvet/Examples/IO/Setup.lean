import Velvet
import Velvet.Core.FreerMonad.IO

namespace Velvet.Examples.IO

inductive IOErr where
  | eof
  | reset
  | full
deriving DecidableEq

structure Stdin
deriving DecidableEq

structure Stdout
deriving DecidableEq

structure Log
deriving DecidableEq

structure Request where
  id : Nat
deriving DecidableEq

structure Response where
  id : Nat

structure Socket where
  fd : Nat
deriving DecidableEq

inductive Cmd where
  | login
  | fetch
deriving DecidableEq

inductive Reply where
  | ok
  | denied
deriving DecidableEq

structure Auth where
  fd : Nat
deriving DecidableEq

instance : Channel Stdin String String IOErr := ⟨⟩
instance : Channel Stdout String String IOErr := ⟨⟩
instance : Channel Log Unit String IOErr := ⟨⟩
instance : Channel Socket Request Response IOErr := ⟨⟩
instance : Channel Auth Cmd Reply IOErr := ⟨⟩

def stdinP : Protocol String String IOErr where
  guarantee _ _ := False
  readAssumption _
    | .ok s => ¬ s.contains '\n'
    | .error e => e = .eof
  writeAssumption _ _ _ := True

def stdoutP : Protocol String String IOErr where
  guarantee _ _ := True
  readAssumption _
    | .ok _ => False
    | .error e => e = .eof
  writeAssumption _ _
    | .ok => True
    | .error e => e = .eof

def logP : Protocol Unit String IOErr where
  guarantee _ o := o ≠ ""
  readAssumption _
    | .ok _ => False
    | .error e => e = .eof
  writeAssumption _ _
    | .ok => True
    | .error e => e = .full

def pending (h : List (IOEvent Request Response IOErr)) : Option Request :=
  h.foldl (fun _ e => match e with | .read (.ok q) => some q | _ => none) none

def reqResp : Protocol Request Response IOErr where
  guarantee h r := ∃ q, pending h = some q ∧ r.id = q.id
  readAssumption h
    | .ok _ => pending h = none
    | .error e => e = .eof ∨ e = .reset
  writeAssumption _ _
    | .ok => True
    | .error e => e = .eof ∨ e = .reset

def loggedIn (h : List (IOEvent Cmd Reply IOErr)) : Bool :=
  h.foldl (fun b e => match e with | .read (.ok .login) => true | _ => b) false

def authP : Protocol Cmd Reply IOErr where
  guarantee h r := r = .ok → loggedIn h = true
  readAssumption _
    | .ok _ => True
    | .error e => e = .eof
  writeAssumption _ _
    | .ok => True
    | .error e => e = .eof

@[simp, grind =] theorem stdinP_guarantee (h) (o : String) : stdinP.guarantee h o = False := rfl
@[simp, grind =] theorem stdinP_read_ok (h) (s : String) : stdinP.readAssumption h (.ok s) = ¬ s.contains '\n' := rfl
@[simp, grind =] theorem stdinP_read_error (h) (e : IOErr) : stdinP.readAssumption h (.error e) = (e = .eof) := rfl

@[simp, grind =] theorem stdoutP_guarantee (h) (o : String) : stdoutP.guarantee h o = True := rfl
@[simp, grind =] theorem stdoutP_write_ok (h) (o : String) : stdoutP.writeAssumption h o .ok = True := rfl
@[simp, grind =] theorem stdoutP_write_error (h) (o : String) (e : IOErr) :
    stdoutP.writeAssumption h o (.error e) = (e = .eof) := rfl

@[simp, grind =] theorem logP_guarantee (h) (o : String) : logP.guarantee h o = (o ≠ "") := rfl
@[simp, grind =] theorem logP_write_ok (h) (o : String) : logP.writeAssumption h o .ok = True := rfl
@[simp, grind =] theorem logP_write_error (h) (o : String) (e : IOErr) :
    logP.writeAssumption h o (.error e) = (e = .full) := rfl

@[simp, grind =] theorem pending_read_ok (h) (q : Request) : pending (h ++ [.read (.ok q)]) = some q := by
  simp [pending, List.foldl_append]
@[simp, grind =] theorem pending_read_error (h) (e : IOErr) : pending (h ++ [.read (.error e)]) = none := by
  simp [pending, List.foldl_append]
@[simp, grind =] theorem pending_write (h) (o : Response) (r : WriteOutcome IOErr) :
    pending (h ++ [.write o r]) = none := by
  simp [pending, List.foldl_append]

@[simp, grind =] theorem reqResp_guarantee (h) (r : Response) :
    reqResp.guarantee h r = ∃ q, pending h = some q ∧ r.id = q.id := rfl
@[simp, grind =] theorem reqResp_read_ok (h) (q : Request) : reqResp.readAssumption h (.ok q) = (pending h = none) := rfl
@[simp, grind =] theorem reqResp_read_error (h) (e : IOErr) :
    reqResp.readAssumption h (.error e) = (e = .eof ∨ e = .reset) := rfl
@[simp, grind =] theorem reqResp_write_ok (h) (o : Response) : reqResp.writeAssumption h o .ok = True := rfl
@[simp, grind =] theorem reqResp_write_error (h) (o : Response) (e : IOErr) :
    reqResp.writeAssumption h o (.error e) = (e = .eof ∨ e = .reset) := rfl

@[simp, grind =] theorem loggedIn_read_login (h) : loggedIn (h ++ [.read (.ok .login)]) = true := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_read_fetch (h) : loggedIn (h ++ [.read (.ok .fetch)]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_read_error (h) (e : IOErr) : loggedIn (h ++ [.read (.error e)]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_write (h) (o : Reply) (r : WriteOutcome IOErr) :
    loggedIn (h ++ [.write o r]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]

@[simp, grind =] theorem authP_guarantee (h) (r : Reply) : authP.guarantee h r = (r = .ok → loggedIn h = true) := rfl
@[simp, grind =] theorem authP_read_ok (h) (c : Cmd) : authP.readAssumption h (.ok c) = True := rfl
@[simp, grind =] theorem authP_read_error (h) (e : IOErr) : authP.readAssumption h (.error e) = (e = .eof) := rfl
@[simp, grind =] theorem authP_write_ok (h) (o : Reply) : authP.writeAssumption h o .ok = True := rfl
@[simp, grind =] theorem authP_write_error (h) (o : Reply) (e : IOErr) :
    authP.writeAssumption h o (.error e) = (e = .eof) := rfl

inductive Event where
  | stdin (e : IOEvent String String IOErr)
  | stdout (e : IOEvent String String IOErr)
  | log (e : IOEvent Unit String IOErr)
  | sock (s : Socket) (e : IOEvent Request Response IOErr)
  | auth (a : Auth) (e : IOEvent Cmd Reply IOErr)

instance : Embeds Stdin Event where
  inj _ e := .stdin e
  proj
    | .stdin e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Embeds Stdout Event where
  inj _ e := .stdout e
  proj
    | .stdout e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Embeds Log Event where
  inj _ e := .log e
  proj
    | .log e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Embeds Socket Event where
  inj s e := .sock s e
  proj
    | .sock s e => some (s, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Embeds Auth Event where
  inj a e := .auth a e
  proj
    | .auth a e => some (a, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Distinct Stdin Stdout Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdin Log Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdin Socket Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdin Auth Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdout Log Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdout Socket Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Stdout Auth Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Log Socket Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Log Auth Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
instance : Distinct Socket Auth Event := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

instance : Model stdinP Stdin Event where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model stdoutP Stdout Event where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model logP Log Event where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model reqResp Socket Event where
  read _ _ := .error .eof
  read_ok _ _ := Or.inl rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

instance : Model authP Auth Event where
  read _ _ := .error .eof
  read_ok _ _ := rfl
  write _ _ _ := .ok
  write_ok _ _ _ := trivial

abbrev Prog := IOProg Event IOErr

end Velvet.Examples.IO
