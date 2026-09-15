module

public import Velvet.Core.Named
public import Lean.Parser
public import Lean.Elab.Command
public import Std.Internal.Do

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Internal.Do Named

declare_syntax_cat velvBinder
syntax "(" Lean.Parser.Term.binderIdent (" : " term)? ")" : velvBinder

declare_syntax_cat velvSpecTerm
syntax (atomic(velvBinder+ " => " termBeforeDo) <|> termBeforeDo) : velvSpecTerm

/-- Convert a `velvSpecTerm` into a Lean `term` (e.g. `(s : Nat) => body` becomes `fun (s : Nat) => body`, and bare `term` stays as-is). -/
public def specTermToTerm (stx : TSyntax `velvSpecTerm) : MacroM (TSyntax `term) := do
  let inner := stx.raw[0]
  if inner.getArgs.size == 3 && inner[1].isToken "=>" then
    let binders : Array Syntax := inner[0].getArgs
    let mut funBinders : Array (TSyntax `term) := #[]
    for b in binders do
      match b with
      | `(velvBinder| ($id:ident : $ty:term)) => funBinders := funBinders.push (← `(term| ($id : $ty)))
      | `(velvBinder| ($id:ident)) => funBinders := funBinders.push (← `(term| $id))
      | `(velvBinder| (_ : $ty:term)) => funBinders := funBinders.push (← `(term| (_ : $ty)))
      | `(velvBinder| (_)) => funBinders := funBinders.push (← `(term| _))
      | _ => Macro.throwErrorAt (⟨b⟩ : TSyntax `velvBinder) "expected an explicit binder of the form `(x : T)` or `(x)`"
    `(term| fun $funBinders* => $(⟨inner[2]⟩))
  else
    pure ⟨inner⟩

variable {m : Type u → Type v} {Pred EPred : Type u}

/-- A runtime no-op that introduces an assertion into verification conditions. -/
public def assertGadget [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (_assertion : Pred) : m PUnit := pure ⟨⟩

syntax "assert" (atomic(ident " : ")) term : term

macro_rules
  | `(term| assert $nm:ident : $t:term) => do
    let nameStr := Lean.Syntax.mkStrLit nm.getId.toString
    let name : TSyntax `term ← `(Lean.Name.mkSimple $nameStr)
    let stx ← Named.sourceRefTerm t.raw
    `(_root_.assertGadget (Named.mk $name $stx $t))

namespace Specs

open Lean.Order

/-- Specification for `assertGadget`: the precondition requires both `assertion` and the
Heyting implication `assertion ⇨ post ⟨⟩`, so the assertion is available when proving the
continuation. -/
@[spec]
public theorem assertGadgetSpec {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (assertion : Pred) [∀ a : Pred, PreservesSup (meet a)]
    {post : PUnit → Pred} {epost : EPred} :
    Triple (_root_.assertGadget (m := m) assertion)
      (assertion ⊓ (assertion ⇨ post ⟨⟩)) post epost := by
  simpa [_root_.assertGadget] using
    (Triple.pure (m := m)
      (pre := assertion ⊓ (assertion ⇨ post ⟨⟩))
      (post := post) (epost := epost) (a := ⟨⟩)
      (h := meet_himp_le))

end Specs
