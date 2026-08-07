# Vendored VCGen frontend

These files are vendored from Lean's internal VCGen implementation in
`leanprover/lean4-nightly-2026-07-15`:

- `Solve.lean`
- `Driver.lean`
- `Frontend.lean`

The implementation lives in the sibling namespace
`Lean.Elab.Tactic.Do.Internal.VCGen'` and exposes the `vcgen''` tactic, avoiding
name collisions with Lean's built-in `vcgen`.

The remaining VCGen infrastructure (`Context`, `Entails`, `RuleCache`, spec
database, symbolic simplifier, etc.) is still imported from Lean. This keeps the
vendored surface small while allowing local changes to solving, worklist
driving, and frontend behavior.

The local tracing, invariant handling, lattice normalization, named-goal
processing, and transactional frontend behavior are maintained as overlays on
the upstream implementation. The 2026-07-15 rebase includes upstream's
extensible `@[frameproc]` frame inference and the revised eager program-pattern
elaboration used by `until` and explicit `frames` clauses.
