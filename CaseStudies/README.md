# Case studies

Larger, self-contained verification case studies built on Velvet.

This directory is a **separate Lake package** (`caseStudies`), not a library of
the root `velvet` package. That is deliberate:

* the root package must stay **Mathlib-free**, and case studies here may depend
  on Mathlib freely;
* `lake build` at the repository root never descends into this directory, so
  case studies are not part of the main build; CI builds them in a separate
  job using this directory's Lake package;
* Mathlib and its transitive dependencies never appear in the root
  `lake-manifest.json` — they are resolved only by this package's own manifest.

The root package is consumed through a path dependency (`require velvet from ".."`),
so case studies always build against the working tree, not a pinned copy.

## Layout

The `CaseStudies` library uses `srcDir = ".."`, which makes the module root
`CaseStudies` resolve to this very directory:

```
CaseStudies/Chrono/SegmentTree/Defs.lean   <->   CaseStudies.Chrono.SegmentTree.Defs
```

Every `.lean` file under `CaseStudies/` is picked up automatically by the
`CaseStudies.+` glob; there is no root module to keep in sync.

## Building

```sh
cd CaseStudies
lake exe cache get   # download Mathlib's prebuilt oleans -- do not skip this
lake build
```

`lake build CaseStudies.Smoke` builds just the smoke test, which checks that
Velvet and Mathlib coexist. Use it to verify the setup itself.

## Writing a case study

Case-study files are **not** written in the Lean module system. Mathlib is still
a legacy (non-`module`) library, and a `module` file cannot import a
non-`module` one. So start files with plain imports:

```lean
import Velvet
import Mathlib.Algebra.Group.Defs
```

A legacy file importing Velvet still gets the full frontend — `method`,
`prove_correct`, `velvet_vcgen` and friends all work. Note that a `/-! ... -/`
module docstring is a command, so in a legacy file it has to come *after* the
imports, not before them.

## Status

| Case study | State |
| --- | --- |
| `CaseStudies.Smoke` | builds |
| `CaseStudies.LeetProof` | builds |
| `CaseStudies.Chrono.SegmentTree` | **work in progress, does not build yet** |

The segment-tree study is a partial port from the Chrono development:
`Defs.lean` still has one failing `grind`, and `SegmentTree.lean` imports
`CaseStudies.Chrono.Syntax_Chrono_CT` and `CaseStudies.Chrono.Chrono_Theory`,
which have not been ported into this repository yet. So a plain `lake build`
here currently fails — that failure is the remaining porting work, not a
problem with the package setup.
