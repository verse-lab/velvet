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

## Using Velvet

To use Velvet in your project, add the following to your `lakefile.lean`:

```lean
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"
```

## Build

Velvet requires [Lean 4](https://github.com/leanprover/lean4). We have tested Velvet on macOS (arm64) and Ubuntu (x86_64).

To build Velvet, run:

```bash
lake build
```

<details close>
<summary><strong>How to install Lean?</strong></summary>

If you don't have Lean installed, we recommend installing it via
[`elan`](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
```

</details>

<details close>
<summary><strong>Dependencies</strong></summary>

Velvet depends on [Loom](https://github.com/verse-lab/loom), which in turn depends on [`z3`](https://github.com/Z3Prover/z3) and [`cvc5`](https://github.com/cvc5/cvc5). These are downloaded automatically when you build Loom for the first time.

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