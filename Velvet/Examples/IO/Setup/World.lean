import Velvet.Examples.IO.Setup.Channels

/-! What the outside world sends, and how each channel kind answers, keeping its protocol's promises. -/

namespace Velvet.Examples.IO

/-- The world a program runs against: what arrives on each channel. -/
class Clients where
  stdin : List String
  stdin_ok : ∀ s ∈ stdin, ¬ s.contains '\n'
  requests : Socket → List Request

/-- How many successful reads the history holds. -/
def readCount (h : List (IOEvent In Out IOErr)) : Nat :=
  h.countP fun
    | .read (.ok _) => true
    | _ => false

/-- The next of `inputs` after the reads in `h`, or the end of input. -/
def nextInput (inputs : List In) (h : List (IOEvent In Out IOErr)) : Except IOErr In :=
  match inputs[readCount h]? with
  | some i => .ok i
  | none => .error .eof

/-- Stdout takes every line. -/
def stdoutModel : StreamOp String String α → Except IOErr α
  | .read => .error .eof
  | .write _ => .ok ()

theorem stdoutModel_ok (ch : Stdout) (h) (o : StreamOp String String α) :
    stdoutP.onReply ch h o (stdoutModel o) := by
  cases o <;> first | rfl | trivial

section Models
variable [Clients]

/-- Stdin hands out the world's lines in order, then the end of input. -/
def stdinModel (h : List (IOEvent String String IOErr)) : StreamOp String String α → Except IOErr α
  | .read => nextInput Clients.stdin h
  | .write _ => .ok ()

theorem stdinModel_ok (ch : Stdin) (h) (o : StreamOp String String α) :
    stdinP.onReply ch h o (stdinModel h o) := by
  cases o with
  | read =>
    simp only [stdinModel, nextInput]
    split
    · rename_i s hs
      exact Clients.stdin_ok s (List.mem_of_getElem? hs)
    · rfl
  | write _ => trivial

/-- A socket delivers its client's requests in order, each once the previous one is answered, then
the end of input. -/
def socketModel (s : Socket) (h : List (IOEvent Request Response IOErr)) :
    StreamOp Request Response α → Except IOErr α
  | .read => if pending h = none then nextInput (Clients.requests s) h else .error .reset
  | .write _ => .ok ()

theorem socketModel_ok (s : Socket) (h) (o : StreamOp Request Response α) :
    reqResp.onReply s h o (socketModel s h o) := by
  cases o with
  | read =>
    simp only [socketModel, nextInput]
    split
    · rename_i hp
      split
      · exact hp
      · exact .inl rfl
    · exact .inr rfl
  | write _ => trivial

end Models

end Velvet.Examples.IO
