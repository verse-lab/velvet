# Vendored VCGen frontend

Based on `leanprover/lean4:v4.34.0`, whose upstream files live in
`Lean/Elab/Tactic/Do/Internal/VCGen/`:

- `Solve.lean`
- `Driver.lean`
- `Frontend.lean`
- `Util.lean` (imports upstream helpers and overrides the customized ones)

Velvet adds named hypotheses and goal tags, extra simplification, source-aware
errors, and progress reporting. `BinderName.lean`, product-binder splitting, and
state-argument simplification retain behavior from the previous nightly.

The implementation uses the root `VCGen` namespace and exposes `velvet_vcgen`.
Import `Velvet.Core.VCGen.Frontend` to use the tactic.

See [EXTENSIONS.md](EXTENSIONS.md) for the exact code snippets in dependency order,
including the retained newer helpers and v4.34 API adaptations.
Run `bash generate_vcgen_diff` from the repository root to refresh the per-file diffs.
