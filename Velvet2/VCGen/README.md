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

This copy keeps the upstream `Lean.Elab.Tactic.Do.Internal.VCGen` namespace and
exposes the bundled frontend as `vcgen_`. Import `Velvet2.VCGen.Frontend` to use it.
