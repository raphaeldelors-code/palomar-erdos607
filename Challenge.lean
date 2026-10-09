module

public import Mathlib
public import Erdos607

open Set Finset

attribute [instance] Classical.propDecidable

/-
# Challenge (advertised statement)

Erdős problem 607 (https://erdosproblems.com/607).

For `n ≥ 2` let `F(n)` be the number of distinct **multiplicity sets**
`A(P)` that can arise from a collection `P` of `n` points of the plane,
where `A(P)` is the set of block sizes (point counts) of the lines
determined by `P`.

**Advertised result.** If the number of profile sets of
pairwise-balanced designs on an `n`-element universe is bounded by
`exp(c·√n)` — the bound of Theorem 2.4 of Colbourn–Phelps–Rödl,
*Block Sizes in Pairwise Balanced Designs*, Canadian Math. Bull. 27(3),
375–380 (1984) — then `F(n) ≤ exp(c·√n)` for all `n`. Combined with the
Szemerédi–Trotter grid lower bound `F(n) ≥ c'·√n`, this resolves the
order of growth of `F(n)`. The CPR-1984 bound is a published,
independently verified theorem and is taken as the hypothesis `hCPR`;
it is not re-proved in this repository.
-/

public section

/-- Erdős 607 upper bound, conditional on Colbourn–Phelps–Rödl (1984)
    Theorem 2.4. If PBD profile sets grow at most like `exp(c2·√n)`, then
    the number of multiplicity sets `F(n)` of `n`-point plane
    configurations grows at most like `exp(c2·√n)`. -/
theorem main_result
    (hCPR : ∃ c2 > (0 : ℝ), ∀ n : ℕ, (Erdos607.pbdProfileSets n).card < Real.exp (c2 * Real.sqrt (n : ℝ))) :
    ∃ c2 > (0 : ℝ), ∀ n : ℕ,
      Set.ncard { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = Erdos607.A P }
      < Real.exp (c2 * Real.sqrt (n : ℝ)) := by
  sorry

end
