/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Init.Prelude
public import Init.Data.String.Basic
public import Init.Data.ToString.Name
public import Lean.Data.Options
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Basic

open Lean Meta Elab Term

namespace Velvet.VCGen

/-- Clean up a specification theorem name (such as `Foo.bar.spec` -> `bar` or `Foo.bar`). -/
public meta def cleanFunctionName (declName : Name) : String :=
  let baseName := match declName with
    | .str p "spec" => p
    | other => other
  match baseName with
  | .str _ s => s
  | other => other.toString

/-- Result of attempting to discharge an individual VC. -/
public meta structure VCResult where
  idx : Nat
  tag : String
  isSolved : Bool

/-- State tracker for VC solving progress. -/
public meta structure ProgressTracker where
  funcName? : Option String := none
  total : Nat := 0
  solvedCount : Nat := 0
  results : Array VCResult := #[]
  enabled : Bool := false

namespace ProgressTracker

public meta def init (declName? : Option Name) (total : Nat) (enabled : Bool) : ProgressTracker :=
  let funcName? := declName?.map cleanFunctionName
  { funcName?, total, solvedCount := 0, results := #[], enabled }

private meta def formatPrefix (tracker : ProgressTracker) : String :=
  match tracker.funcName? with
  | some fn => s!"[velvet:{fn}]"
  | none    => "[velvet]"

public meta def onSolved (tracker : ProgressTracker) (idx : Nat) (tag : String) : ProgressTracker :=
  { tracker with
    solvedCount := tracker.solvedCount + 1
    results := tracker.results.push { idx, tag, isSolved := true } }

public meta def onUnsolved (tracker : ProgressTracker) (idx : Nat) (tag : String) : ProgressTracker :=
  { tracker with
    results := tracker.results.push { idx, tag, isSolved := false } }

public meta def onFinish (tracker : ProgressTracker) : MetaM Unit := do
  unless tracker.enabled && tracker.total > 0 do return
  let prefixStr := tracker.formatPrefix
  let summaryHeader :=
    if tracker.solvedCount == tracker.total then
      s!"{prefixStr} ✔ Finished: {tracker.solvedCount}/{tracker.total} solved"
    else
      let remaining := tracker.total - tracker.solvedCount
      s!"{prefixStr} ⚠ Finished: {tracker.solvedCount}/{tracker.total} solved ({remaining} remaining)"
  let lines := tracker.results.map fun r =>
    let icon := if r.isSolved then "✔" else "✖"
    let statusNote := if r.isSolved then "" else " (unsolved)"
    s!"  {icon} [{r.idx}/{tracker.total}] '{r.tag}'{statusNote}"
  let fullMsg := String.intercalate "\n" (summaryHeader :: lines.toList)
  logInfo m!"{fullMsg}"

public meta def onGenerated (tracker : ProgressTracker) (tags : List String) : MetaM Unit := do
  unless tracker.enabled do return
  let prefixStr := tracker.formatPrefix
  let count := tracker.total
  if count == 0 then
    logInfo m!"{prefixStr} ✔ All goals solved during generation."
  else
    let vcWord := if count == 1 then "VC" else "VCs"
    let header := s!"{prefixStr} ℹ Generated {count} {vcWord}:"
    let mut lines := []
    let mut i := 0
    for tag in tags do
      i := i + 1
      lines := lines ++ [s!"  • [{i}/{count}] '{tag}'"]
    let fullMsg := String.intercalate "\n" (header :: lines)
    logInfo m!"{fullMsg}"

end ProgressTracker

end Velvet.VCGen
