module

public import Lean.Data.Options
public import Lean.Data.KVMap

open Lean

/-- Termination semantics for `method` elaboration. -/
public inductive VelvetSemanticsTermination : Type where
  | totalCorrectness
  | partialCorrectness

public instance : Inhabited VelvetSemanticsTermination := ⟨.totalCorrectness⟩

public instance : KVMap.Value VelvetSemanticsTermination where
  toDataValue
    | .totalCorrectness => "total"
    | .partialCorrectness => "partial"
  ofDataValue?
    | .ofString "total" => some .totalCorrectness
    | .ofString "partial" => some .partialCorrectness
    | _ => none

/-- `total` (default): the generated `def` must prove termination.
`partial`: the `def` is elaborated with `partial_fixpoint`, skipping the termination proof. -/
public register_option velvet.semantics.termination : VelvetSemanticsTermination := {
  defValue := .totalCorrectness
  descr := "Termination semantics for `method`: `total` (default) or `partial`."
}

/-- Whether `method` should automatically verify itself during elaboration by running `prove_correct <name> by velvet_vcgen [<name>] with finish`. -/
public register_option velvet.verifyDuringElab : Bool := {
  defValue := false
  descr := "Automatically verify method specifications during elaboration using `velvet_vcgen with finish`."
}
