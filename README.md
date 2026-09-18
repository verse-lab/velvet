# Velvet

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

## What is Velvet?

Velvet is a Dafny-style verifier for imperative programs embedded in the Lean proof
assistant. Velvet seamlessly combines SMT-based automated proofs with Lean's
interactive proof mode, enabling multi-modal verification: programs can be compiled,
executed, validated using property-based testing, and formally verified within one
unified environment.

## Features

- **Shallow embedding in monads.** Programs are shallowly embedded in a monad. `Id`,
  `Option`, `StateT`, `ExceptT` and stacks thereof are supported.
- **Ghost state.** Variables that exist only for the sake of the specification, and are
  erased from the compiled program.
- **Nondeterminism.** Reason about programs with nondeterministic choice using angelic
  or demonic semantics.
- **Partial and total correctness.** Separately verify functional correctness and
  termination, then combine them for total correctness.
- **Multi-modal proofs.** When SMT automation fails, complete proofs interactively using
  Lean tactics or any available automation (e.g. `aesop`, `grind`).
- **Testing before proving.** `#derive_tester_for` turns a contract into an executable
  checker that runs on concrete or randomly generated inputs.
- **Foundational verification.** A proved method yields `<name>.spec`, a plain Lean
  theorem that Velvet reuses at call sites and that you can use in handwritten proofs.

## Building

### Requirements

Velvet requires [Lean 4](https://github.com/leanprover/lean4), installed through
[`elan`](https://github.com/leanprover/elan). The exact toolchain is pinned in
`lean-toolchain` and `elan` picks it up automatically, so there is nothing else to
install:

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
```

### Clone and build

```bash
git clone https://github.com/verse-lab/velvet.git
cd velvet
lake build
```

The root package deliberately does not depend on Mathlib, so this builds from source in
a few minutes. Use `lake build Examples` to check the example suite as well.

### Case studies

The case studies may use Mathlib and live in their own Lake package:

```bash
cd CaseStudies
lake exe cache get
lake build
```

`lake exe cache get` downloads a pre-built version of
[Mathlib](https://github.com/leanprover-community/mathlib4), which otherwise would take a
very long time to build. See [CaseStudies/README.md](CaseStudies/README.md) for details.

## Documentation

For detailed documentation of Velvet's features and usage, see [docs/doc.md](docs/doc.md).

## Navigation guide

| Path | Contents |
| :--- | :--- |
| [Velvet/Core/](Velvet/Core) | Weakest-precondition semantics, loop and nondeterminism combinators, the `velvet_vcgen` tactic |
| [Velvet/Frontend/](Velvet/Frontend) | `method` elaboration, `prove_correct`, options, tester derivation, VC reports |
| [Velvet/Examples/](Velvet/Examples) | Worked examples — the fastest way to learn the syntax |
| [CaseStudies/](CaseStudies) | Larger developments, in a separate Lake package so that Mathlib stays out of the root build |
| [docs/doc.md](docs/doc.md) | The language reference |

New to Velvet? Read [`Sqrt.lean`](Velvet/Examples/Sqrt.lean) for the basics,
[`Loops.lean`](Velvet/Examples/Loops.lean) for invariant patterns, and
[`StateT.lean`](Velvet/Examples/StateT.lean) for stateful contracts.
