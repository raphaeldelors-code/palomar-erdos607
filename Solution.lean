module

public import Mathlib

open Set Finset

attribute [instance] Classical.propDecidable

namespace E607

/-
# Proved solution

Self-contained: the definitions below are verbatim copies of the ones in
the Challenge (namespace `E607`), so the statement of `main_result` is
definitionally the advertised statement, and the full proof (the same
development that ships in the `Erdos607` reference library,
`Erdos607/Proof.lean`) is included inline. The library remains available
as a standalone module for reference.
-/

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

/-! ## Basic collinear symmetries -/

/-- collinear p q r ↔ collinear r q p (swapping outer arguments). -/
theorem collinearSym (p q r : ℝ × ℝ) : collinear p q r ↔ collinear r q p := by
  simp only [collinear]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

/-- collinear p q r ↔ collinear q p r (swapping first two arguments). -/
theorem collinearSym2 (p q r : ℝ × ℝ) : collinear p q r ↔ collinear q p r := by
  simp only [collinear]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

/-- collinear p x y ↔ collinear x y p (cyclic invariance). -/
theorem collinearCyclic (p x y : ℝ × ℝ) : collinear p x y ↔ collinear x y p := by
  simp only [collinear]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

/-! The key geometric lemma. For distinct a, b and a point d on line(a,b)
    with d ≠ a, the line through a and b equals the line through a and d.

    Proof: let B = b−a, D = d−a, and for a point x, X = x−a, using the
    cross products B×X, D×X and the fact B×D = 0 (d on line(a,b)).
    Two polynomial identities (each a scalar multiple of B×D = 0, proved
    by linear_combination):
      (B×X)·D.1 = B.1·(D×X)   and   (B×X)·D.2 = B.2·(D×X).
    From B×X = 0 we get B.1·(D×X) = 0 and B.2·(D×X) = 0, and since B ≠ 0
    this forces D×X = 0; the reverse direction uses D ≠ 0 symmetrically. -/
theorem line_eq
    (a b d : ℝ × ℝ) (hab : a ≠ b) (hdna : d ≠ a)
    (hcd : collinear a b d) :
    ∀ x : ℝ × ℝ, collinear a b x ↔ collinear a d x := by
  intro x
  set db1 := b.1 - a.1 with db1def
  set db2 := b.2 - a.2 with db2def
  set dd1 := d.1 - a.1 with dd1def
  set dd2 := d.2 - a.2 with dd2def
  set dx1 := x.1 - a.1 with dx1def
  set dx2 := x.2 - a.2 with dx2def
  have hcdeq : db1 * dd2 = db2 * dd1 := by
    simp only [collinear] at hcd
    exact hcd
  have hBnz : db1 ≠ 0 ∨ db2 ≠ 0 := by
    by_contra h
    push_neg at h
    have : a = b := by
      ext <;> linarith [db1def, db2def, h.1, h.2]
    contradiction
  have hDnz : dd1 ≠ 0 ∨ dd2 ≠ 0 := by
    by_contra h
    push_neg at h
    have : d = a := by
      ext <;> linarith [dd1def, dd2def, h.1, h.2]
    contradiction
  have hkey1 : (db1 * dx2 - db2 * dx1) * dd1 = db1 * (dd1 * dx2 - dd2 * dx1) := by
    linear_combination hcdeq * dx1
  have hkey2 : (db1 * dx2 - db2 * dx1) * dd2 = db2 * (dd1 * dx2 - dd2 * dx1) := by
    linear_combination hcdeq * dx2
  simp only [collinear]
  constructor
  · -- B×X = 0 → D×X = 0
    intro h
    have hEB : db1 * dx2 - db2 * dx1 = 0 := by linarith
    have h1 : db2 * (dd1 * dx2 - dd2 * dx1) = 0 := by rw [← hkey2, hEB, zero_mul]
    have h2 : db1 * (dd1 * dx2 - dd2 * dx1) = 0 := by rw [← hkey1, hEB, zero_mul]
    rcases hBnz with (hdb1 | hdb2)
    · have : dd1 * dx2 - dd2 * dx1 = 0 := by
        rcases (mul_eq_zero.mp h2) with (hdb1' | hed)
        · contradiction
        · exact hed
      linarith
    · have : dd1 * dx2 - dd2 * dx1 = 0 := by
        rcases (mul_eq_zero.mp h1) with (hed | hdb2')
        · contradiction
        · exact hdb2'
      linarith
  · -- D×X = 0 → B×X = 0
    intro h
    have hED : dd1 * dx2 - dd2 * dx1 = 0 := by linarith
    have h1 : (db1 * dx2 - db2 * dx1) * dd1 = 0 := by rw [hkey1, hED, mul_zero]
    have h2 : (db1 * dx2 - db2 * dx1) * dd2 = 0 := by rw [hkey2, hED, mul_zero]
    rcases hDnz with (hdd1 | hdd2)
    · have : db1 * dx2 - db2 * dx1 = 0 := by
        rcases (mul_eq_zero.mp h1) with (heb | hdd1')
        · exact heb
        · contradiction
      linarith
    · have : db1 * dx2 - db2 * dx1 = 0 := by
        rcases (mul_eq_zero.mp h2) with (heb | hdd2')
        · exact heb
        · contradiction
      linarith

/-- Every block of P is a subset of P. -/
lemma blocks_subset (P : Finset (ℝ × ℝ)) (B : Finset (ℝ × ℝ))
    (hB : B ∈ blocks P) : B ⊆ P := by
  have hB' : B ∈ (Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p))).filter (fun B => 2 ≤ B.card) := by
    simpa [blocks] using hB
  have hBf : B ∈ Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p)) :=
    (Finset.mem_filter.mp hB').1
  rcases (Finset.mem_biUnion.mp hBf) with ⟨p, hp, hBim⟩
  rcases (Finset.mem_image.mp hBim) with ⟨q, hq, rfl⟩
  intro z hz
  rw [collinearSet] at hz
  exact (Finset.mem_filter.mp hz).1
/-- The set of all multiplicity sets achievable by some n-point configuration.
    (A Set, not a Finset, since the universe of Finset (ℝ × ℝ) is infinite.) -/
noncomputable def achievable (n : ℕ) : Set (Finset ℕ) :=
  { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = A P }
/-! ## Reduction theorems (unconditional) -/

/-- (a) Every block of P has size ≥ 2.
    (b) PBD-pair property: for distinct x, y ∈ P there is a unique block
        containing both. Uniqueness follows from the line_eq lemma. -/
theorem pbd_lemmas (P : Finset (ℝ × ℝ)) :
    (∀ B ∈ blocks P, 2 ≤ B.card) ∧
    (∀ x ∈ P, ∀ y ∈ P, x ≠ y → (∃! B, B ∈ blocks P ∧ x ∈ B ∧ y ∈ B)) := by
  constructor
  · intro B hB
    have hB' : B ∈ (Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p))).filter (fun B => 2 ≤ B.card) := by
      simpa [blocks] using hB
    exact (Finset.mem_filter.mp hB').2
  · intro x hx y hy hxy
    -- Existence witness: collinearSet P x y
    have hxx : collinear x y x := by simp [collinear]
    have hyy : collinear x y y := by simp [collinear]; ac_rfl
    have hxin : x ∈ collinearSet P x y := by
      rw [collinearSet, mem_filter]
      exact ⟨hx, hxx⟩
    have hyin : y ∈ collinearSet P x y := by
      rw [collinearSet, mem_filter]
      exact ⟨hy, hyy⟩
    have hcard2 : 2 ≤ (collinearSet P x y).card := by
      have hsub : ({x, y} : Finset (ℝ × ℝ)) ⊆ collinearSet P x y := by
        intro z hz
        simp at hz
        rcases hz with (rfl | rfl)
        · exact hxin
        · exact hyin
      have h1 : ({x, y} : Finset (ℝ × ℝ)).card ≤ (collinearSet P x y).card :=
        Finset.card_le_card hsub
      have h2 : ({x, y} : Finset (ℝ × ℝ)).card = 2 := by
        simp [hxy]
      linarith
    have hinBi : collinearSet P x y ∈
        Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p)) := by
      rw [Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      rw [Finset.mem_image]
      refine ⟨y, ?_, rfl⟩
      rw [mem_erase]
      exact ⟨Ne.symm hxy, hy⟩
    have hcanon : collinearSet P x y ∈ blocks P := by
      rw [blocks, mem_filter]
      exact ⟨hinBi, hcard2⟩
    -- Uniqueness: any block B containing x and y equals collinearSet P x y
    refine ⟨collinearSet P x y, ⟨hcanon, ⟨hxin, hyin⟩⟩, fun B hB => ?_⟩
    obtain ⟨hBmem, hxyB⟩ := hB
    have hBf : B ∈ Finset.biUnion P (fun p => Finset.image (fun q => collinearSet P p q) (P.erase p)) := by
      rw [blocks] at hBmem
      exact (Finset.mem_filter.mp hBmem).1
    rcases (Finset.mem_biUnion.mp hBf) with ⟨p, hp, hBim⟩
    rcases (Finset.mem_image.mp hBim) with ⟨q, hinq, rfl⟩
    have hcollx : collinear p q x := by
      have : x ∈ collinearSet P p q := hxyB.1
      rw [collinearSet, Finset.mem_filter] at this
      exact this.2
    have hcolly : collinear p q y := by
      have : y ∈ collinearSet P p q := hxyB.2
      rw [collinearSet, Finset.mem_filter] at this
      exact this.2
    have hpq : p ≠ q := by
      intro heq
      rw [heq] at hinq
      exact (Finset.notMem_erase q P) hinq
    ext z
    by_cases hpex : x = p
    · -- Case 1: x = p (so y ≠ p)
      have hyneq : y ≠ p := by
        intro hy; subst hy
        subst hpex
        tauto
      have hle2 := line_eq p q y hpq hyneq hcolly
      simp only [collinearSet, mem_filter] at ⊢
      constructor
      · intro hz
        have h1 : collinear p q z := hz.2
        have h2 : collinear p y z := (hle2 z).mp h1
        have h3 : collinear x y z := by simpa [hpex] using h2
        exact ⟨hz.1, h3⟩
      · intro hz
        have h1 : collinear x y z := hz.2
        have h2 : collinear p y z := by simpa [← hpex] using h1
        have h3 : collinear p q z := (hle2 z).mpr h2
        exact ⟨hz.1, h3⟩
    · -- Case 2: x ≠ p
      have hpx : p ≠ x := Ne.symm hpex
      have hcolxy : collinear x y p := by
        have h1 := line_eq p q x hpq hpex hcollx
        have h2 : collinear p x y := (h1 y).mp hcolly
        exact (collinearCyclic p x y).mp h2
      have hle_xy_p := line_eq x y p hxy hpx hcolxy
      simp only [collinearSet, mem_filter] at ⊢
      constructor
      · intro hz
        have h1 : collinear p q z := hz.2
        have h2 : collinear p x z := (line_eq p q x hpq hpex hcollx z).mp h1
        have h3 : collinear x p z := (collinearSym2 x p z).mpr h2
        exact ⟨hz.1, (hle_xy_p z).mpr h3⟩
      · intro hz
        have h1 : collinear x y z := hz.2
        have h2 : collinear x p z := (hle_xy_p z).mp h1
        have h3 : collinear p x z := (collinearSym2 x p z).mp h2
        have h4 : collinear p q z := (line_eq p q x hpq hpex hcollx z).mpr h3
        exact ⟨hz.1, h4⟩

/-- For any n-point configuration P, its multiplicity set A P appears as an
    element of pbdProfileSets n. -/
theorem A_in_pbdProfileSets (n : ℕ) (P : Finset (ℝ × ℝ)) (h : P.card = n) :
    A P ∈ pbdProfileSets n := by
  by_cases hn0 : n = 0
  · -- n = 0: substitute n := 0 so Fin 0 is empty; P = ∅ and A P = ∅
    subst hn0
    have hP : P = ∅ := by rwa [Finset.card_eq_zero] at h
    rw [hP]
    have hAempty : A ∅ = ∅ := by simp [A, blocks]
    rw [hAempty]
    rw [pbdProfileSets, Finset.mem_image]
    use ∅
    constructor
    · rw [Finset.mem_filter]
      constructor
      · simp
      · constructor
        · intro b hb; cases hb
        · intro x; exfalso; exact Nat.not_lt_zero x.1 x.2
    · simp
  · -- n > 0
    have hn1 : 0 < n := Nat.pos_of_ne_zero hn0
    have hcard : Fintype.card P = n := by simp [Fintype.card_coe, h]
    have he : P ≃ Fin n := Fintype.equivFinOfCardEq hcard
    let f : ℝ × ℝ → Fin n := fun z =>
      if hz : z ∈ P then he ⟨z, hz⟩ else ⟨0, hn1⟩
    let blocks' : Finset (Finset (Fin n)) := (blocks P).image (fun B => B.image f)
    -- f is injective on every block (each block is a subset of P)
    have hfInjBlock : ∀ B ∈ blocks P, Set.InjOn f B := by
      intro B hB
      have hBsub : B ⊆ P := blocks_subset P B hB
      intro z1 hz1 z2 hz2 hf
      have hz1P : z1 ∈ P := hBsub hz1
      have hz2P : z2 ∈ P := hBsub hz2
      have hf1 : f z1 = he (⟨z1, hz1P⟩ : {z // z ∈ P}) := by simp [f, hz1P]
      have hf2 : f z2 = he (⟨z2, hz2P⟩ : {z // z ∈ P}) := by simp [f, hz2P]
      have h_eq : he (⟨z1, hz1P⟩ : {z // z ∈ P}) = he (⟨z2, hz2P⟩ : {z // z ∈ P}) := by
        simpa [hf1, hf2] using hf
      have hsub : (⟨z1, hz1P⟩ : {z // z ∈ P}) = (⟨z2, hz2P⟩ : {z // z ∈ P}) :=
        he.injective h_eq
      exact congrArg Subtype.val hsub
    -- blocks' is a PBD on Fin n
    have hPBD : isPBD n blocks' := by
      constructor
      · intro b hb
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hb
        have hB2 : 2 ≤ B.card := (pbd_lemmas P).1 B hB
        have hcard' : (B.image f).card = B.card :=
          Finset.card_image_of_injOn (hfInjBlock B hB)
        rw [hcard']
        exact hB2
      · intro x y hxy
        have hexy : (he.symm x).1 ≠ (he.symm y).1 := by
          intro hexy
          have hsub : he.symm x = he.symm y := by
            apply Subtype.ext
            exact hexy
          have : x = y := (he.symm).injective hsub
          contradiction
        have hpair : ∃! B, B ∈ blocks P ∧ (he.symm x).1 ∈ B ∧ (he.symm y).1 ∈ B :=
          (pbd_lemmas P).2 (he.symm x).1 (he.symm x).2 (he.symm y).1 (he.symm y).2 hexy
        obtain ⟨B, hQ, huniq⟩ := hpair
        let B' := (B : Finset (ℝ × ℝ)).image f
        have hB' : B' ∈ blocks' := by
          rw [Finset.mem_image]
          exact ⟨B, hQ.1, rfl⟩
        have hpx : (he.symm x).1 ∈ P := (he.symm x).2
        have hfpx : f (he.symm x).1 = x := by
          have h1 : f (he.symm x).1 = he (he.symm x) := by simp [f, hpx]
          simpa [← h1] using he.apply_symm_apply x
        have hpy : (he.symm y).1 ∈ P := (he.symm y).2
        have hfpy : f (he.symm y).1 = y := by
          have h1 : f (he.symm y).1 = he (he.symm y) := by simp [f, hpy]
          simpa [← h1] using he.apply_symm_apply y
        have hx' : x ∈ B' := by
          rw [Finset.mem_image]
          exact ⟨(he.symm x).1, hQ.2.1, hfpx⟩
        have hy' : y ∈ B' := by
          rw [Finset.mem_image]
          exact ⟨(he.symm y).1, hQ.2.2, hfpy⟩
        refine ⟨B', ⟨hB', ⟨hx', hy'⟩⟩, fun B2' hb2' => ?_⟩
        obtain ⟨B2, hB2mem, hB2eq⟩ := Finset.mem_image.mp hb2'.1
        have hhex : (he.symm x).1 ∈ B2 := by
          have : x ∈ B2.image f := by rw [hB2eq]; exact hb2'.2.1
          rcases (Finset.mem_image.mp this) with ⟨w, hw, hwf⟩
          have hwP : w ∈ P := blocks_subset P B2 hB2mem hw
          have h_eq : he (⟨w, hwP⟩ : {z // z ∈ P}) = he (he.symm x) := by
            simp [f, hwP] at hwf
            rw [← he.apply_symm_apply x] at hwf
            exact hwf
          have hval : (he.symm x).1 = w :=
            (congrArg Subtype.val (he.injective h_eq)).symm
          rw [hval]
          exact hw
        have hhey : (he.symm y).1 ∈ B2 := by
          have : y ∈ B2.image f := by rw [hB2eq]; exact hb2'.2.2
          rcases (Finset.mem_image.mp this) with ⟨w, hw, hwf⟩
          have hwP : w ∈ P := blocks_subset P B2 hB2mem hw
          have h_eq : he (⟨w, hwP⟩ : {z // z ∈ P}) = he (he.symm y) := by
            simp [f, hwP] at hwf
            rw [← he.apply_symm_apply y] at hwf
            exact hwf
          have hval : (he.symm y).1 = w :=
            (congrArg Subtype.val (he.injective h_eq)).symm
          rw [hval]
          exact hw
        have hB2eqB : B2 = B := huniq B2 ⟨hB2mem, ⟨hhex, hhey⟩⟩
        rw [← hB2eq, hB2eqB]
    -- A P = (blocks').image Finset.card, because f is injective on each block
    have hAP : A P = blocks'.image Finset.card := by
      have h1 : blocks'.image Finset.card =
          ((blocks P).image (fun B => B.image f)).image Finset.card := by
        unfold blocks'
        rfl
      have h2 : ((blocks P).image (fun B => B.image f)).image Finset.card =
          (blocks P).image (fun B => (B.image f).card) := by
        rw [Finset.image_image]
        rfl
      have h3 : (blocks P).image (fun B => (B.image f).card) =
          (blocks P).image Finset.card := by
        apply Finset.ext
        intro c
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨B, hB, hBc⟩
          use B
          constructor
          · exact hB
          · rw [← Finset.card_image_of_injOn (hfInjBlock B hB)]
            exact hBc
        · rintro ⟨B, hB, hBc⟩
          use B
          constructor
          · exact hB
          · rw [Finset.card_image_of_injOn (hfInjBlock B hB)]
            exact hBc
      unfold A
      rw [h3.symm, h2.symm, h1.symm]
    rw [pbdProfileSets, hAP, Finset.mem_image]
    refine ⟨blocks', ?_, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · exact hPBD

/-- The achievable set is contained in (the image of) pbdProfileSets n,
    and hence its cardinality is bounded by (pbdProfileSets n).card. -/
theorem reduction_le (n : ℕ) :
    (achievable n).ncard ≤ (pbdProfileSets n).card := by
  have hsub : achievable n ⊆ (↑(pbdProfileSets n) : Set (Finset ℕ)) := by
    intro S hS
    obtain ⟨P, hP, hS⟩ := hS
    have hmem := A_in_pbdProfileSets n P hP
    simpa [achievable, hS] using hmem
  have hncard : (achievable n).ncard ≤ (↑(pbdProfileSets n) : Set (Finset ℕ)).ncard :=
    ncard_le_ncard hsub
  have hncard2 : (↑(pbdProfileSets n) : Set (Finset ℕ)).ncard = (pbdProfileSets n).card := by
    simp [ncard_coe_finset]
  simpa [hncard2] using hncard

public section

/-- Erdős 607 upper bound, conditional on Colbourn–Phelps–Rödl (1984)
    Theorem 2.4. For every `n ≥ 2`, if the number of PBD profile sets on an
    `n`-element universe is at most `exp(c2·√n)`, then the number of
    multiplicity sets `F(n)` of `n`-point plane configurations is at most
    `exp(c2·√n)`. The PBD profile-set bound is Theorem 2.4 of
    Colbourn–Phelps–Rödl, "Block Sizes in Pairwise Balanced Designs",
    Canadian Mathematical Bulletin 27(3), 375–380 (1984); it is a published
    theorem taken as hypothesis `hCPR`, not re-proved here. The quantifier is
    restricted to `n ≥ 2` — the range in which the bound is meaningful (a
    single point determines no line) — so the hypothesis is non-vacuous.
    Together with the Szemerédi–Trotter (1983) lower bound
    `F(n) ≥ exp(c'·√n)` (cited, not re-proved), this pins
    `F(n) = exp(Θ(√n))`. -/
theorem main_result
    (hCPR : ∃ c2 > (0 : ℝ), ∀ n : ℕ, 2 ≤ n → (pbdProfileSets n).card < Real.exp (c2 * Real.sqrt (n : ℝ))) :
    ∃ c2 > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
      Set.ncard { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = A P }
      < Real.exp (c2 * Real.sqrt (n : ℝ)) := by
  obtain ⟨c2, hc2, hbound⟩ := hCPR
  refine ⟨c2, hc2, fun n hn2 => ?_⟩
  have hset : { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = A P } = achievable n := by
    ext S
    simp [achievable]
  have h1 : Set.ncard { S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ S = A P } = (achievable n).ncard := by
    simp [hset]
  have h2 : (achievable n).ncard ≤ (pbdProfileSets n).card := reduction_le n
  have h3 : (pbdProfileSets n).card < Real.exp (c2 * Real.sqrt (n : ℝ)) := hbound n hn2
  have h4 : (achievable n).ncard < Real.exp (c2 * Real.sqrt (n : ℝ)) := by
    have h2' : (↑(achievable n).ncard : ℝ) ≤ (↑(pbdProfileSets n).card : ℝ) := by
      exact_mod_cast h2
    exact lt_of_le_of_lt h2' h3
  simpa [h1] using h4
end

end E607
