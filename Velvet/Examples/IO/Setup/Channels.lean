import Velvet
import Velvet.Core.FreerMonad.IO

/-! The channel kinds the IO examples use, and their protocols. -/

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

instance : StreamChannel Stdin String String IOErr := ⟨⟩
instance : StreamChannel Stdout String String IOErr := ⟨⟩
instance : StreamChannel Log Unit String IOErr := ⟨⟩
instance : StreamChannel Socket Request Response IOErr := ⟨⟩
instance : StreamChannel Auth Cmd Reply IOErr := ⟨⟩

def stdinP : StreamProtocol Stdin String String IOErr where
  allow _ _ o := match o with
    | .read => True
    | .write _ => False
  onReply _ _ o r := match o, r with
    | .read, .ok s => ¬ s.contains '\n'
    | .read, .error e => e = .eof
    | .write _, _ => True

def stdoutP : StreamProtocol Stdout String String IOErr where
  allow _ _ _ := True
  onReply _ _ o r := match o, r with
    | .read, .ok _ => False
    | _, .error e => e = .eof
    | .write _, .ok _ => True

def logP : StreamProtocol Log Unit String IOErr where
  allow _ _ o := match o with
    | .read => True
    | .write o => o ≠ ""
  onReply _ _ o r := match o, r with
    | .read, .ok _ => False
    | .read, .error e => e = .eof
    | .write _, .ok _ => True
    | .write _, .error e => e = .full

def pending (h : List (IOEvent Request Response IOErr)) : Option Request :=
  h.foldl (fun _ e => match e with | .read (.ok q) => some q | _ => none) none

def reqResp : StreamProtocol Socket Request Response IOErr where
  allow _ h o := match o with
    | .read => True
    | .write r => ∃ q, pending h = some q ∧ r.id = q.id
  onReply _ h o r := match o, r with
    | .read, .ok _ => pending h = none
    | _, .error e => e = .eof ∨ e = .reset
    | .write _, .ok _ => True

def loggedIn (h : List (IOEvent Cmd Reply IOErr)) : Bool :=
  h.foldl (fun b e => match e with | .read (.ok .login) => true | _ => b) false

def authP : StreamProtocol Auth Cmd Reply IOErr where
  allow _ h o := match o with
    | .read => True
    | .write r => r = .ok → loggedIn h = true
  onReply _ _ o r := match o, r with
    | _, .ok _ => True
    | _, .error e => e = .eof

@[simp, grind =] theorem stdinP_allow_read (ch h) : stdinP.allow ch h .read = True := rfl
@[simp, grind =] theorem stdinP_allow_write (ch h) (o : String) : stdinP.allow ch h (.write o) = False := rfl
@[simp, grind =] theorem stdinP_onReply_read_ok (ch h) (s : String) :
    stdinP.onReply ch h .read (.ok s) = ¬ s.contains '\n' := rfl
@[simp, grind =] theorem stdinP_onReply_read_error (ch h) (e : IOErr) :
    stdinP.onReply ch h .read (.error e) = (e = .eof) := rfl

@[simp, grind =] theorem stdoutP_allow (ch h) (o : StreamOp String String α) : stdoutP.allow ch h o = True := rfl
@[simp, grind =] theorem stdoutP_onReply_write_ok (ch h) (o : String) (u : Unit) :
    stdoutP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem stdoutP_onReply_error (ch h) (o : StreamOp String String α) (e : IOErr) :
    stdoutP.onReply ch h o (.error e) = (e = .eof) := by cases o <;> rfl

@[simp, grind =] theorem logP_allow_write (ch h) (o : String) : logP.allow ch h (.write o) = (o ≠ "") := rfl
@[simp, grind =] theorem logP_onReply_write_ok (ch h) (o : String) (u : Unit) :
    logP.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem logP_onReply_write_error (ch h) (o : String) (e : IOErr) :
    logP.onReply ch h (.write o) (.error e) = (e = .full) := rfl

@[simp, grind =] theorem pending_onRead_ok (h) (q : Request) : pending (h ++ [.read (.ok q)]) = some q := by
  simp [pending, List.foldl_append]
@[simp, grind =] theorem pending_onRead_error (h) (e : IOErr) : pending (h ++ [.read (.error e)]) = none := by
  simp [pending, List.foldl_append]
@[simp, grind =] theorem pending_write (h) (o : Response) (r : Except IOErr Unit) :
    pending (h ++ [.write o r]) = none := by
  simp [pending, List.foldl_append]

@[simp, grind =] theorem reqResp_allow_read (ch h) : reqResp.allow ch h .read = True := rfl
@[simp, grind =] theorem reqResp_allow_write (ch h) (r : Response) :
    reqResp.allow ch h (.write r) = ∃ q, pending h = some q ∧ r.id = q.id := rfl
@[simp, grind =] theorem reqResp_onReply_read_ok (ch h) (q : Request) :
    reqResp.onReply ch h .read (.ok q) = (pending h = none) := rfl
@[simp, grind =] theorem reqResp_onReply_write_ok (ch h) (o : Response) (u : Unit) :
    reqResp.onReply ch h (.write o) (.ok u) = True := rfl
@[simp, grind =] theorem reqResp_onReply_error (ch h) (o : StreamOp Request Response α) (e : IOErr) :
    reqResp.onReply ch h o (.error e) = (e = .eof ∨ e = .reset) := by cases o <;> rfl

@[simp, grind =] theorem loggedIn_read_login (h) : loggedIn (h ++ [.read (.ok .login)]) = true := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_read_fetch (h) : loggedIn (h ++ [.read (.ok .fetch)]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_onRead_error (h) (e : IOErr) : loggedIn (h ++ [.read (.error e)]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]
@[simp, grind =] theorem loggedIn_write (h) (o : Reply) (r : Except IOErr Unit) :
    loggedIn (h ++ [.write o r]) = loggedIn h := by
  simp [loggedIn, List.foldl_append]

@[simp, grind =] theorem authP_allow_read (ch h) : authP.allow ch h .read = True := rfl
@[simp, grind =] theorem authP_allow_write (ch h) (r : Reply) :
    authP.allow ch h (.write r) = (r = .ok → loggedIn h = true) := rfl
@[simp, grind =] theorem authP_onReply_ok (ch h) (o : StreamOp Cmd Reply α) (v : α) :
    authP.onReply ch h o (.ok v) = True := by cases o <;> rfl
@[simp, grind =] theorem authP_onReply_error (ch h) (o : StreamOp Cmd Reply α) (e : IOErr) :
    authP.onReply ch h o (.error e) = (e = .eof) := by cases o <;> rfl

end Velvet.Examples.IO
