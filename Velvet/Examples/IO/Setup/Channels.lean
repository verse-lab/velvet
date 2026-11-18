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

structure Request where
  id : Nat
deriving DecidableEq

structure Response where
  id : Nat

structure Socket where
  fd : Nat
deriving DecidableEq

instance : StreamChannel Stdin String String IOErr := ⟨⟩
instance : StreamChannel Stdout String String IOErr := ⟨⟩
instance : StreamChannel Socket Request Response IOErr := ⟨⟩

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

end Velvet.Examples.IO
