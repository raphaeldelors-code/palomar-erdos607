module

public import Mathlib

open Set Finset

attribute [instance] Classical.propDecidable

/-
# Challenge (advertised statement)

Erdős problem 607 (https://erdosproblems.com/607).

For `n ≥ 2` let `F(n)` be the number of distinct **multiplicity sets**
`A(P)` that can arise from a collection `P` of `n` points of the plane,
where `A(P)` is the set of block sizes (point counts) of the lines
determined by `P`. Erdős asked whether `F(n) ≤ exp(O(√n))`; the problem
has carried a $250 prize on erdosproblems.com since 1985.

**Advertised result (the upper bound).** If the number of profile sets of
pairwise-balanced designs on an `n`-element universe is at most
`exp(c·√n)` — the bound of Theorem 2.4 of Colbourn–Phelps–Rödl,
*Block Sizes in Pairwise Balanced Designs*, Canadian Math. Bull. 27(3),
375–380 (1984) — then `F(n) ≤ exp(c·√n)` for every `n ≥ 2`. The quantifier
is restricted to `n ≥ 2` — the range where the bound is meaningful (a
single point determines no line) — so the hypothesis `hCPR` is non-vacuous.
The CPR-1984 bound is a published, independently verified theorem and is
taken as the hypothesis `hCPR`; it is not re-proved in this repository.

**Order of growth (with a cited lower bound).** The Szemerédi–Trotter
(1983) lattice-grid construction gives the matching lower bound
`F(n) ≥ exp(c'·√n)` (cited, not re-proved). Together, the upper bound
proved here and that lower bound pin down `F(n) = exp(Θ(√n))`: the √n scale
Erdős conjectured for #607 is exact.

This module is self-contained: it imports only Mathlib and declares the
definitions its statement uses. The matching `Solution` module re-declares
the same definitions verbatim and bridges to the library proof.
-/

namespace E607

/-- Three points p, q, r in ℝ² are collinear iff the cross product
    (q − p) × (r − p) vanishes, i.e.
    (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1). -/
def collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- The set of points of P collinear with p and q. -/
noncomputable def collinearSet (P : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  P.filter (fun z => collinear p q z)

/-- The blocks of P: for each p ∈ P, for each q ∈ P \ {p}, take
    collinearSet P p q; keep only blocks of size ≥ 2. -/
noncomputable def blocks (P : Finset (ℝ × ℝ)) : Finset (Finset (ℝ × ℝ)) :=
  (Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p))).filter (fun B => 2 ≤ B.card)

/-- A collection B of finsets of Fin n is a PBD if every block has size ≥ 2
    and every pair of distinct points lies in exactly one block. -/
def isPBD (n : ℕ) (B : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ B, 2 ≤ b.card) ∧
  (∀ x y : Fin n, x ≠ y → (∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b))

/-- The set of all PBD profile sets on an n-element universe: for each PBD
    on Fin n, record the set of block sizes. -/
public noncomputable def pbdProfileSets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.univ : Finset (Finset (Finset (Fin n)))).filter (fun B => isPBD n B) |>.image (fun B => B.image Finset.card)

/-- The multiplicity set of P: the set of block sizes that occur among the
    lines determined by P. -/
public noncomputable def A (P : Finset (ℝ × ℝ)) : Finset ℕ :=
  (blocks P).image Finset.card

public section

/-- Erdős 607 upper bound, conditional on Colbourn–Phelps–Rödl (1984)
    Theorem 2.4. For every `n ≥ 2`, if PBD profile sets on `n` points grow
    at most like `exp(c2·√n)`, then the number of multiplicity sets `F(n)`
    of `n`-point plane configurations grows at most like `exp(c2·√n)`. -/
theorem main_result
    (hCPR : ∃ c2 > (0 : ℝ), ∀ n : ℕ, 2 ≤ n → (pbdProfileSets n).card < Real.exp (c2 * Real.sqrt (n : ℝ))) :
    ∃ c2 > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
      Set.ncard { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = A P }
      < Real.exp (c2 * Real.sqrt (n : ℝ)) := by
  sorry

end

end E607
