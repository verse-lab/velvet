import Lean.Data.Options
import Lean.Data.KVMap

/-!
Velvet attributes and options.

Registered in their own file (rather than at the use site) so the `register_option`
`initialize` block runs when the module is imported, before any other module reads the option.
-/

open Lean

/-- Termination semantics for `method` elaboration. -/
inductive VelvetSemanticsTermination : Type where
  | totalCorrectness
  | partialCorrectness

instance : Inhabited VelvetSemanticsTermination := ⟨.totalCorrectness⟩

instance : KVMap.Value VelvetSemanticsTermination where
  toDataValue
    | .totalCorrectness => "total"
    | .partialCorrectness => "partial"
  ofDataValue?
    | .ofString "total" => some .totalCorrectness
    | .ofString "partial" => some .partialCorrectness
    | _ => none

/-- `total` (default): the generated `def` must prove termination.
`partial`: the `def` is elaborated with `partial_fixpoint`, skipping the termination proof. -/
register_option velvet.semantics.termination : VelvetSemanticsTermination := {
  defValue := .totalCorrectness
  descr := "Termination semantics for `method`: `total` (default) or `partial`."
}

/-- Whether `method` should automatically verify itself during elaboration by running `prove_correct <name> by velvet_vcgen [<name>] with finish`. -/
register_option velvet.verifyDuringElab : Bool := {
  defValue := false
  descr := "Automatically verify method specifications during elaboration using `velvet_vcgen with finish`."
}

/-- Show status and diagnostics for verification goals during `velvet_vcgen`. -/
register_option velvet.showProgress : Bool := {
  defValue := true
  descr := "Show status and diagnostics for verification goals."
}
