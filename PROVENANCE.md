# Provenance and prior-art search (Erdős 607)

This file is the prior-art account requested in the v2 review of this
submission. It documents a credible search and states, precisely, which
element of the result is new and which elements are taken from the
published literature. It is written to answer the review's single blocking
request:

> Substantiate the original-proof designation with a credible literature
> search that distinguishes the new reduction from cited results; if the
> result was proved earlier, cite that work and correct the source
> relationship.

## The exact result claimed

Let `F(n)` count the number of distinct **sets** `A(P)` of line sizes
(point-counts on the lines) determined by a set `P` of `n` plane points.
Erdős problem 607 (https://erdosproblems.com/607) asks whether

    F(n) <= exp(O(sqrt(n))).

The result proved and machine-checked in this repository is the geometric
corollary:

    For every n >= 2, if the number of profile sets of pairwise-balanced
    designs (PBDs) on an n-element universe is at most exp(c·sqrt(n)),
    then F(n) <= exp(c·sqrt(n)).

Combined with the independently published Szemerédi–Trotter (1983) lower
bound `F(n) >= exp(c'·sqrt(n))`, this pins `F(n) = exp(Theta(sqrt(n)))`,
answering the problem affirmatively.

## What is new, stated precisely

This is a composition of three ingredients. We are explicit about which
one is new, because the first two are not:

1. **Standard (textbook).** The lines determined by a point set `P` form a
   pairwise-balanced design on the `n` points: every pair of points lies on
   exactly one line, and every line contains at least two points. This is the
   standard definition of a PBD applied to the line set; it is a
   characterization, not a theorem requiring independent proof, and is used
   as such throughout the discrete-geometry literature.

2. **Published (cited, not re-proved).** The bound on the number of PBD
   profile sets. Theorem 2.4 of Colbourn, Phelps and Rödl, *Block Sizes in
   Pairwise Balanced Designs*, Canadian Mathematical Bulletin 27(3), 375–380
   (1984), https://doi.org/10.4153/CMB-1984-057-0, proves that the number
   `g(n)` of PBD profile sets (block-size sets) on `n` points satisfies
   `exp(c1·sqrt(n)) <= g(n) <= exp(c2·sqrt(n))`. This is a purely
   combinatorial statement about the whole class of PBDs; it contains no
   geometric input and does not mention point sets, lines, or Erdős 607. It
   is taken here as the hypothesis `hCPR`.

3. **New (this work, machine-checked).** The geometric corollary: applying
   the bound of item 2 to the *specific* PBD family arising as the lines of
   plane point sets (item 1), giving `F(n) <= exp(c·sqrt(n))` for every
   `n >= 2`, and hence the answer to Erdős 607. No source examined in this
   search states this geometric corollary — not the Erdős problem page, not
   the CPR-1984 paper, not the surveys below, and not the AI-benchmark
   result lists in items (a)–(d) of the search. The machine-checked proof
   of the reduction (item 1) and the corollary (item 3) is the
   contribution of this repository.

In short: **the bound is not new (it is CPR-1984); the characterization is
not new (it is the definition of a PBD); what is new is the geometric
corollary that the CPR bound, applied to point-set line sets, settles the
upper bound for Erdős 607.** This is a modest, reduction-style result —
the same shape as, for example, the resolution of Erdős 652 reported in
[8] as "an immediate reduction to the literature." We label it
`original-proof` because the *corollary as a statement about point sets* is
first presented here, and we record that designation with the precision
above rather than as an over-broad claim that the underlying bound is new.

## The search, item by item

Searched 2026-10-10. Sources and what each does or does not contain.

(a) **The problem page and its canonical source.**
    https://erdosproblems.com/607. States the problem, the $250 prize,
    cites [Er85] as origin, and notes that Szemerédi–Trotter proved the
    bound is best possible (the lower bound). "Proof expositions (0)".
    No upper-bound proof or reduction is posted.

(b) **Colbourn–Phelps–Rödl 1984** (item 2 above). Read in full (Cambridge
    open-access copy). Theorem 2.4 is the PBD profile-set bound. The paper
    is purely about PBD block sizes; it does not state a corollary for
    point-set line sizes and does not address Erdős 607.

(c) **Gyarfás, *Extremal problems in discrete geometry and finite
    geometry*, arXiv:0201184 (2002).** The standard survey of line-size
    and incidence questions. Treats the Szemerédi–Trotter theorem and
    related bounds; it does not state an `exp(c·sqrt(n))` upper bound on
    the number of distinct line-size *sets* `F(n)` for point sets.

(d) **Erdős–Purdy 1978** (*On the number of distinct line sizes...*,
    related to the finer multiset quantity). Addresses the multiset of line
    sizes on a larger scale; it is the closest geometry work but does not
    state the set-version upper bound for `F(n)`.

(e) **FrontierMath Erdős benchmark** (Karp, Lattimore et al., arXiv
    2609.25050). The 68-conjecture benchmark (Appendix A) does **not**
    include Erdős 607 (verified against the full list). GPT-6 Astra solved
    problems #126, #548, #571, #577, #646, #769, #975; none is 607.

(f) **Semi-Autonomous Mathematics Discovery with Gemini** (arXiv
    2601.22401v3). Resolved 13 open Erdős problems (#652, #1051, #654,
    #1040, #397, #659, #935, #1089, #333, #591, #705, #992, #1105); 607 is
    not among them. Note: Erdős 652 is explicitly described there as "an
    immediate reduction to the literature," which is the same result-shape
    as ours and is why we disclose the reduction character openly.

(g) **google-deepmind/formal-conjectures.** Contains Lean formalizations of
    Erdős problems (e.g. #1003, #433); no formalization or proof of 607.

(h) **arXiv and general web search.** Targeted queries on "line sizes",
    "multiplicity set", "PBD profile", "block sizes of a point set", and
    "Erdos 607 proof/solution" (2025–2026) returned no prior statement of
    the geometric corollary and no prior machine-checked proof of it.

## Conclusion

No earlier proof of the geometric corollary for Erdős 607 was found. The
claim is therefore corrected and scoped as follows: the **bound** is
CPR-1984, the **characterization** is the standard PBD definition, and the
**new element is the geometric corollary** (the reduction applied to
point-set line sets, settling the problem). This repository's
`original-proof` designation refers to that geometric corollary being first
presented here, and the machine-checked formalization of the reduction and
corollary is the substantive contribution. If a reviewer identifies an
earlier statement of the geometric corollary, we will cite it and reclassify
the source relationship to `background` accordingly.
