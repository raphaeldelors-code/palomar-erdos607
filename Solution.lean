module

public import Mathlib
public import Erdos607

open Set Finset

attribute [instance] Classical.propDecidable

/-
# Proved solution

Same statement as the Challenge; the full proof development lives in the
`Erdos607` library (`Erdos607/Proof.lean`), verified by this build.
-/

/-- Erdős 607 upper bound, conditional on Colbourn–Phelps–Rödl (1984)
    Theorem 2.4. If PBD profile sets grow at most like `exp(c2·√n)`, then
    the number of multiplicity sets `F(n)` of `n`-point plane
    configurations grows at most like `exp(c2·√n)`. -/
theorem Erdos607.main_result
    (hCPR : ∃ c2 > (0 : ℝ), ∀ n : ℕ, (Erdos607.pbdProfileSets n).card < Real.exp (c2 * Real.sqrt (n : ℝ))) :
    ∃ c2 > (0 : ℝ), ∀ n : ℕ,
      Set.ncard { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = Erdos607.A P }
      < Real.exp (c2 * Real.sqrt (n : ℝ)) :=
  Erdos607.conditional_bound hCPR
