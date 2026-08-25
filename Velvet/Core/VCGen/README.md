# Vendored VCGen frontend

These files are vendored from the Lean toolchain pinned by this repository
(`leanprover/lean4:nightly-2026-08-22`):

- `Solve.lean`
- `Driver.lean`
- `Frontend.lean`
- `Util.lean`

Their upstream location is
`Lean/Elab/Tactic/VCGen/` in the Lean source tree. The files include Velvet's
customizations for named goal tags, simplifying assumptions, and enhanced reporting.

This copy keeps the upstream `Lean.Elab.Tactic.VCGen` namespace and
exposes the bundled frontend as `velvet_vcgen`. Import `Velvet.VCGen.Frontend` to use it.
