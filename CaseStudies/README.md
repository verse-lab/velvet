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

## Overview

### Lazy Segment Tree

Segment Tree is a data structure which supports two operations: 
1. Query for a fold of a binary operation on segment [l, r] of some array `arr`
2. Apply a unary operation to all elements of array `arr` on segment [l, r]

Both operations yield O(logn) time. The folder `SegmentTree` is structured as follows:
- `Defs.lean` contains definitions and theory-level lemmas for the Segment Tree data structure
- `SegmentTree.lean` contains the implementation of data structure operations (proved in Velvet)
- `Asymptotics.lean` contains additional facts about running time for the data structure (these are not used in the correctness proofs)
- `Example.lean` contains an instance for Segment Tree data structure with binary operation of `+` and unary operation of `set to x`

Notably, only one goal in correctness proofs is not discharged by `grind` tactic automatically.