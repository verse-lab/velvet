import Velvet.Examples.IO.Setup.World

/-! One event type holding every channel kind, and IO programs over it. -/

namespace Velvet.Examples.IO

inductive Event where
  | stdin (e : IOEvent String String IOErr)
  | stdout (e : IOEvent String String IOErr)
  | log (e : IOEvent Unit String IOErr)
  | sock (s : Socket) (e : IOEvent Request Response IOErr)
  | auth (a : Auth) (e : IOEvent Cmd Reply IOErr)

instance : Provide Event Stdin where
  inj _ e := .stdin e
  proj
    | .stdin e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Provide Event Stdout where
  inj _ e := .stdout e
  proj
    | .stdout e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Provide Event Log where
  inj _ e := .log e
  proj
    | .log e => some (⟨⟩, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Provide Event Socket where
  inj s e := .sock s e
  proj
    | .sock s e => some (s, e)
    | _ => none
  proj_inj _ _ := rfl

instance : Provide Event Auth where
  inj a e := .auth a e
  proj
    | .auth a e => some (a, e)
    | _ => none
  proj_inj _ _ := rfl

@[simp, grind =] theorem inj_stdin (ch : Stdin) (e) : (Provide.inj ch e : Event) = .stdin e := rfl
@[simp, grind =] theorem inj_stdout (ch : Stdout) (e) : (Provide.inj ch e : Event) = .stdout e := rfl
@[simp, grind =] theorem inj_log (ch : Log) (e) : (Provide.inj ch e : Event) = .log e := rfl
@[simp, grind =] theorem inj_sock (s : Socket) (e) : (Provide.inj s e : Event) = .sock s e := rfl
@[simp, grind =] theorem inj_auth (a : Auth) (e) : (Provide.inj a e : Event) = .auth a e := rfl

instance : Distinguish Event Stdin Stdout := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdout Stdin := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdin Log := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Log Stdin := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdin Socket := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Socket Stdin := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdin Auth := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Auth Stdin := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdout Log := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Log Stdout := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdout Socket := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Socket Stdout := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Stdout Auth := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Auth Stdout := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Log Socket := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Socket Log := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Log Auth := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Auth Log := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Socket Auth := ⟨fun _ _ => rfl⟩
instance : Distinguish Event Auth Socket := ⟨fun _ _ => rfl⟩

section Models
variable [Clients]

instance : PureModel Stdin stdinP Event where
  call t ch o := stdinModel (t.traceOf ch) o
  call_ok _ ch o := stdinModel_ok ch _ o

instance : PureModel Stdout stdoutP Event where
  call _ _ o := stdoutModel o
  call_ok _ ch o := stdoutModel_ok ch _ o

instance : PureModel Log logP Event where
  call t ch o := logModel (t.traceOf ch) o
  call_ok _ ch o := logModel_ok ch _ o

instance : PureModel Socket reqResp Event where
  call t s o := socketModel s (t.traceOf s) o
  call_ok _ s o := socketModel_ok s _ o

instance : PureModel Auth authP Event where
  call t a o := authModel a (t.traceOf a) o
  call_ok _ a o := authModel_ok a _ o

end Models

abbrev Prog := IOProg Event IOErr

end Velvet.Examples.IO
