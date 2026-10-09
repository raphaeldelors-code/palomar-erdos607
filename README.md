# Erdos607 — machine-checked upper bound on Erdős problem 607

[![CI](https://github.com/raphaeldelors-code/palomar-erdos607/actions/workflows/ci.yml/badge.svg)](https://github.com/raphaeldelors-code/palomar-erdos607/actions/workflows/ci.yml)

A [Palomar](https://palomar-registry.org/) submission. For `n ≥ 2`, let
`F(n)` be the number of distinct **multiplicity sets** `A(P)` arising from a
collection `P` of `n` points of the plane, where `A(P)` is the set of block
sizes (point counts) of the lines determined by `P`. This repository proves a
machine-checked upper bound for Erdős problem 607
(https://erdosproblems.com/607):

> If the number of profile sets of pairwise-balanced designs on an
> `n`-element universe is at most `exp(c·√n)` — the bound of
> Colbourn–Phelps–Rödl, *Block Sizes in Pairwise Balanced Designs*,
> Canadian Mathematical Bulletin 27(3), 375–380 (1984), Theorem 2.4 — then
> `F(n) ≤ exp(c·√n)` for every `n`.

The key combinatorial step: the lines determined by `P` form a
pairwise-balanced design on the `n` points (every pair of points lies on
exactly one line; every line contains at least two points), so `A(P)` is
exactly the set of block sizes of such a design, and `F(n)` is bounded by the
number of PBD profile sets on `n` points. The CPR-1984 PBD profile bound is a
published, independently verified theorem; it is cited here and taken as the
hypothesis `hCPR`, not re-proved in this repository.

## Repository map

- `Challenge.lean` is the small statement surface a reader audits
  (one `sorry` for the advertised declaration, by design).
- `Solution.lean` connects the same declaration to the completed proof.
- `Erdos607/Proof.lean` contains the full proof development (zero axioms,
  zero `sorry` in the library).
- `comparator.json` tells `lake comparator` which declarations must match.
- `formalization.yaml` records the public result description, provenance,
  authorship, automation, fidelity, and review information.
- `LICENSE` contains the Apache License 2.0 terms declared by
  `project.license`.
- `docbuild/` is the nested doc-gen4 project.
- `scripts/verify-comparator.sh` runs the `lake comparator` that ships in
  this project's own toolchain over the checked-in `comparator.json`,
  registering the toolchain's bundled independent kernels (NanoDa and con-ron)
  exactly as Palomar does.

The root uses `lakefile.toml`, the Lean toolchain
`leanprover/lean4:v4.35.0-rc2` (Palomar requires v4.35.0-rc2 or later), and
committed Lake manifests. Everything that judges a submission comes from
`lean-toolchain`. GitHub Actions builds the Lean project with `lean-action`,
generates API documentation with doc-gen4, and independently checks the
advertised statement with `lake comparator`. Actions are pinned to immutable
commits.

## Building

```text
lake update
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The full check set requires Linux, Git, Ruby, Python 3, and `bwrap`
(bubblewrap), which `lake comparator` uses to sandbox the build it judges.
The only `sorry` in the repository is the deliberate statement surface in
`Challenge.lean`; the proof library has none.

## Provenance and AI use

The mathematical reduction (lines of a point set form a pairwise-balanced
design, so multiplicity sets are exactly PBD profiles) was identified and
audited by a human. The Lean formalization and tactic search were developed
with an LLM agent (qwen3.8-27b served locally through llama-swap); Lean's
kernel re-checks every proof step. See `formalization.yaml` for the full
account.

## Submitting to Palomar

Read the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
commit the final snapshot, and
[open the submission form](https://submit.palomar-registry.org/)
with the full 40-character commit SHA.

Questions are welcome in the
[Palomar channel on the Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/621638-Palomar).
