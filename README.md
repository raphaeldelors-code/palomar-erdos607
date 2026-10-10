# Erdos607 — machine-checked upper bound on Erdős problem 607

[![CI](https://github.com/raphaeldelors-code/palomar-erdos607/actions/workflows/ci.yml/badge.svg)](https://github.com/raphaeldelors-code/palomar-erdos607/actions/workflows/ci.yml)

A [Palomar](https://palomar-registry.org/) submission. For `n ≥ 2`, let
`F(n)` be the number of distinct **multiplicity sets** `A(P)` arising from a
collection `P` of `n` points of the plane, where `A(P)` is the set of block
sizes (point counts) of the lines determined by `P`. Erdős asked (problem
607, https://erdosproblems.com/607, $250 prize) whether `F(n) ≤ exp(O(√n))`.

## Result

**Upper bound (proved here, machine-checked).** For every `n ≥ 2`, if the
number of profile sets of pairwise-balanced designs (PBDs) on an
`n`-element universe is at most `exp(c·√n)` — the bound of Theorem 2.4 of
Colbourn–Phelps–Rödl, *Block Sizes in Pairwise Balanced Designs*, Canadian
Mathematical Bulletin 27(3), 375–380 (1984) — then `F(n) ≤ exp(c·√n)` for
every `n ≥ 2`.

The quantifier is deliberately restricted to `n ≥ 2`, the range in which the
bound is meaningful (a single point determines no line); the CPR PBD bound is
a published, independently verified theorem and is taken as the hypothesis
`hCPR`, not re-proved in this repository.

**Order of growth (upper bound + cited lower bound).** The Szemerédi–Trotter
lattice-grid construction — the extremal example behind their incidence
theorem, *Extremal problems in discrete geometry*, Combinatorica 3(3),
381–392 (1983) — gives the matching lower bound `F(n) ≥ exp(c'·√n)` (cited,
not re-proved here). Together the upper bound proved in this repository and
that lower bound pin down `F(n) = exp(Θ(√n))`, confirming exactly the `√n`
scale Erdős predicted.

## What is new and what is assumed

We are explicit about which element of the result is new and which is
taken from the published literature. The full prior-art search is in
[PROVENANCE.md](PROVENANCE.md).

- **New (this work, machine-checked): the geometric corollary.** Applying
  the published CPR-1984 PBD profile-set bound to the *specific* PBD family
  arising as the lines of plane point sets gives `F(n) <= exp(c·sqrt(n))`
  for all `n >= 2`, answering Erdős 607. No source examined in the search
  states this geometric corollary; it is first presented here. The
  machine-checked reduction below is the step that makes it valid.
- **Standard characterization (textbook, not a new theorem).** The lines
  determined by `P` form a PBD on the `n` points (every pair of points lies
  on exactly one line, and each line contains at least two points), so
  `A(P)` is exactly the block-size set of such a PBD.
- **Assumed, cited.** The CPR-1984 PBD profile-set bound (hypothesis
  `hCPR`) and the Szemerédi–Trotter (1983) grid lower bound. Both are
  standard, independently published results; this repository does not
  re-prove them. The bound itself is *not* new — only its geometric
  application to point-set line sets is.
- **On "profile set".** `A(P)` is a *set* of block sizes — the
  multiplicity-set version of the question. This is the object Erdős 607
  asks about. (The finer *multiset* of line sizes grows on a larger scale,
  `exp(√n·log n)`; that is a different, strictly stronger quantity and is
  not the claim made here.) The reduction to PBD profile *sets* is the step
  that makes the `exp(√n)` bound apply at all.

## Repository map

- `Challenge.lean` is the small statement surface a reader audits
  (one `sorry` for the advertised declaration, by design).
- `Solution.lean` connects the same declaration to the completed proof.
- `Erdos607/Proof.lean` contains the full proof development (zero axioms,
  zero `sorry` in the library).
- `comparator.json` tells `lake comparator` which declarations must match.
- `formalization.yaml` records the public result description, provenance,
  authorship, automation, fidelity, and review information.
- `PROVENANCE.md` is the documented prior-art search: which element of the
  result is new (the geometric corollary) and which is cited (the CPR-1984
  PBD bound, the ST-1983 lower bound), with the sources examined.
- `LICENSE` contains the Apache License 2.0 terms declared by
  `project.license`.
- `docbuild/` is the nested doc-gen4 project.
- `scripts/verify-comparator.sh` runs the `lake comparator` that ships in
  this project's own toolchain over the checked-in `comparator.json`,
  registering the toolchain's bundled independent kernels (NanoDa and con-ron)
  exactly as Palomar does.

The root uses `lakefile.toml`, the Lean toolchain
`leanprover/lean4:v4.35.0-rc2` (Palomar requires v4.35.0-rc2 or later), and
committed Lake manifests. These pins determine the local verification
basis, which is a local check: it is a faithful local approximation of,
but not identical to, Palomar's verification (Palomar uses
verifier-pinned tools and its own protected verification process). GitHub
Actions builds the Lean project with `lean-action`,
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
audited by a human. The prior-art search distinguishing the new geometric
corollary from the cited CPR-1984 bound and the ST-1983 lower bound is
documented in [PROVENANCE.md](PROVENANCE.md). The Lean formalization and
tactic search were developed with an LLM agent (qwen3.8-27b served locally
through llama-swap); Lean's kernel re-checks every proof step. See
`formalization.yaml` for the full account.

## Submitting to Palomar

Read the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
commit the final snapshot, and
[open the submission form](https://submit.palomar-registry.org/)
with the full 40-character commit SHA.

Questions are welcome in the
[Palomar channel on the Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/621638-Palomar).
