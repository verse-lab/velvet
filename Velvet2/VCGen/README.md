# Vendored VCGen frontend

These files are vendored from the Lean toolchain pinned by this repository
(`leanprover/lean4:nightly-2026-08-11`):

- `Solve.lean`
- `Driver.lean`
- `Frontend.lean`

Their upstream location is
`Lean/Elab/Tactic/Do/Internal/VCGen/` in the Lean source tree. The files are
unchanged except for the internal module edges: `Driver.lean` imports
`Velvet2.VCGen.Solve`, and `Frontend.lean` imports `Velvet2.VCGen.Driver`.

Unlike `Velvet2/VCGen'`, this copy keeps the upstream
`Lean.Elab.Tactic.Do.Internal.VCGen` namespace and the upstream `vcgen` tactic
name. Import `Velvet2.VCGen.Frontend` in place of Lean's internal frontend; do
not import both frontend modules into the same module.
