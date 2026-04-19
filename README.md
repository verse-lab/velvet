# Velvet: A Foundational Multi-Modal Verifier for Imperative Programs in Lean

Velvet is a Dafny-style verifier for imperative programs embedded in the Lean proof assistant. Built on top of the [Loom](https://github.com/verse-lab/loom) framework, Velvet seamlessly combines SMT-based automated proofs with Lean's interactive proof mode, enabling *multi-modal verification*: programs can be compiled, executed, validated using property-based testing, and formally verified within one unified environment.

Main features:

* **Auto-active verification via SMT** -- Dafny-style specification and verification with automated proof discharge using `cvc5` and `z3`

* **Multi-modal proofs** -- when SMT automation fails, complete proofs interactively using Lean tactics or any available automation (e.g., `aesop`, `grind`)

* **Property-based testing** -- extract executable code from Velvet programs and test them against their specifications using randomised testing

* **Partial and total correctness** -- separately verify functional correctness and termination, then combine them for total correctness

* **Non-determinism** -- reason about programs with non-deterministic choice using angelic or demonic semantics

* **Access to mathlib** -- use Lean's rich ecosystem of formalised mathematics in program specifications and proofs

For a detailed description of Velvet, see the [paper](paper.pdf).

## Building the Artefact (CAV 26)

This branch (`cav26-ae`) is the artefact accompanying the CAV 26 submission.
Running it reproduces the experimental claims in Sec. 4 of the [paper](paper.pdf):

* **RQ1 (automation parity with Dafny).** 21 medium-complexity VERINA
  programs that Velvet discharges fully automatically, verified in the same
  style as Dafny. Shipped under [Bench/both_easy/](Bench/both_easy/).
* **RQ2 (interactive proofs when automation fails).** 6 programs that require
  manual lemmas in both Velvet and Dafny, where Velvet benefits from access
  to `mathlib`. Shipped under [Bench/needs_proofs/](Bench/needs_proofs/).
* **RQ3 (expressivity beyond auto-active verifiers).** 3 programs
  (`memAlloc`, `isNonPrime`, `oneThird`) whose specifications either rely on
  complex mathematical objects or on custom theory libraries, and cannot be
  stated or proven in Dafny at all. Shipped under [Bench/hard/](Bench/hard/)
  — Lean files only, as there is no Dafny counterpart.

The artefact driver ([Bench/generate_artefact.py](Bench/generate_artefact.py))
benchmarks every matching `(.dfy, .lean)` pair from `both_easy/` and
`needs_proofs/` using [hyperfine](https://github.com/sharkdp/hyperfine),
aggregates the results, and produces **`Bench/results/chart_all.pdf`** — the
Dafny-vs-Velvet verification-time comparison shown in Fig. 6 of the paper —
alongside `chart_all.png` and a `benchmark_results.csv`.

### Prerequisites and reproduction

Tested on macOS (arm64, Apple M1) and Ubuntu (x86_64) with `cvc5` 1.3.1, `z3`
4.15.4, Lean 4.24.0.

1. **Install Lean** (via [`elan`](https://github.com/leanprover/elan)):

   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
   ```

   `elan` reads [`lean-toolchain`](lean-toolchain) and pulls the exact Lean
   version (4.24.0) used to prepare the artefact.

2. **Build Velvet** from the repository root:

   ```bash
   lake exe cache get; lake build
   ```

   <details close>
   <summary><strong>What this does</strong></summary>

   `lake exe cache get` downloads pre-built `mathlib` `.olean` files
   (≈ 7 k files, ~1 GB); `lake build` then compiles Loom, Velvet, and the
   examples used in RQ3. The first build also downloads the SMT solvers
   (`z3` 4.15.4 and `cvc5` 1.3.1) into
   `.lake/packages/Loom/.lake/build/`, driven by the
   `downloadDependencies` target in [`lakefile.lean`](lakefile.lean).
   Expected wall time: ≈ 5–10 min on a fresh machine (dominated by the
   mathlib download and Velvet example compilation).

   </details>

3. **Install Dafny** (≥ 4.x) — see <https://dafny.org/dafny/Installation>, or
   on macOS `brew install dafny` (pulls in `z3` automatically).

4. **Install the benchmark tooling**:

   ```bash
   # hyperfine
   brew install hyperfine                # macOS
   # sudo apt install hyperfine          # Ubuntu

   # Python deps — use a venv to avoid PEP 668 ("externally managed")
   python3 -m venv .venv
   . .venv/bin/activate
   pip install matplotlib numpy
   ```

5. **Run the driver**:

   ```bash
   python3 Bench/generate_artefact.py
   ```

   <details close>
   <summary><strong>What this does</strong></summary>

   By default, each program is timed 10 times with one warm-up run,
   matching the paper. Total wall time is roughly 25–40 min on an M1
   MacBook Pro.

   Useful flags:
   - `--runs N --warmup W` — tune the hyperfine settings (use `--runs 2`
     for a ~5 min smoke test).
   - `--skip-bench` — do not re-run hyperfine; only re-aggregate and
     re-plot from the existing `Bench/results/*/*.json` files.

   On completion the script prints a grand summary (aggregate ratio,
   geo-mean ratio and speedup, Velvet-faster-than-Dafny count) and
   writes:

   - `Bench/results/chart_all.pdf` — the Fig. 6 chart;
   - `Bench/results/chart_all.png` — PNG version;
   - `Bench/results/benchmark_results.csv` — per-program means / stddevs
     / ratios for machine-readable consumption.

   </details>

## Documentation

For detailed documentation of Velvet's features and usage, see [velvet_documentation.md](Velvet/velvet_documentation.md).

## Navigation Guide

### Core Library (`Velvet/`)

- `Syntax.lean` -- Velvet's DSL: macros for `method`, `ensures`, `requires`, `invariant`, `decreasing`, and the choice operator `:|`
- `Std.lean` -- standard tactics and utilities, including `loom_solve`, `loom_solve!`, `loom_solve?`, and `loom_smt`
- `VelvetTheory.lean` -- theoretical foundations for separated proofs of termination and correctness

### Examples (`Velvet/Examples/`)

- `Examples.lean` -- basic Dafny-like examples (`insertionSort`, `squareRoot`) with partial correctness
- `Examples_Total.lean` -- examples with total correctness semantics
- `Total_Partial_example.lean` -- combining termination and partial correctness proofs for total correctness
- `SpMSpV_Example.lean` -- sparse matrix-vector multiplication mixing automated and interactive proofs
- `SubstringSearch.lean` -- longest digit-only substring search
- `Recursion.lean` -- examples with recursive programs

### Benchmarks (`Bench/`)

Inputs and driver for reproducing the evaluation in Sec. 4 of the paper:

- [`both_easy/`](Bench/both_easy/) — 21 VERINA programs solved automatically
  by both Dafny and Velvet (RQ1). Each program appears as a `.dfy` / `.lean`
  pair; the `.lean` file imports `Velvet.Std` and ends with
  `prove_correct <name> by loom_solve`.
- [`needs_proofs/`](Bench/needs_proofs/) — 6 VERINA programs where SMT
  automation is insufficient in both systems and manual lemmas are supplied
  (RQ2). Same `.dfy` / `.lean` layout.
- [`hard/`](Bench/hard/) — the three RQ3 case studies (`IsNonPrime.lean`,
  `MemAlloc.lean`, `OneThird.lean`). These demonstrate Velvet's expressivity
  beyond auto-active verifiers (custom path theories, `mathlib` primality
  lemmas, Riemann sums) and therefore have no Dafny counterpart.
- [`generate_artefact.py`](Bench/generate_artefact.py) — single Python driver
  that runs hyperfine on every `(.dfy, .lean)` pair, aggregates per-program
  means/stddevs, and renders `chart_all.{pdf,png}` plus
  `benchmark_results.csv` into `Bench/results/`.
