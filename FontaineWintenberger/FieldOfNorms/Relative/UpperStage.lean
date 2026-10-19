/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Residue
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.Mathlib.RingTheory.PolynomialDiscriminant

/-!
# Coordinates at full upper stages

## Coordinates at arbitrary high-break stages

The relative full upper product is compared with the absolute APF stage.
The resulting wild finite norms descend the existing deep integral projection
to the finite field and its maximal-ideal quotient.

## Discriminants of the finite-coordinate polynomials

The integral coordinates need not be additive. Their polynomial is
formed coefficient by coefficient; only its reduction is compared using the
proved high-break ring homomorphism. The normalized discriminant
value is then stable as soon as the precision exceeds that value.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local instance FiniteIntermediateField.instNontriviallyNormedField (E : FiniteIntermediateField K
    L) :
    NontriviallyNormedField E.val :=
  spectralNorm.nontriviallyNormedField K E.val
local instance FiniteIntermediateField.instNormedAlgebra (E : FiniteIntermediateField K L) :
    NormedAlgebra K E.val :=
  spectralNorm.normedAlgebra K E.val
local instance FiniteIntermediateField.instIsUltrametricDist (E : FiniteIntermediateField K L) :
    IsUltrametricDist E.val :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
local instance FiniteIntermediateField.instCompleteSpace (E : FiniteIntermediateField K L) :
    CompleteSpace E.val :=
  spectralNorm.completeSpace K E.val
local instance FiniteIntermediateField.instIsPerfectResidueLocalField (E : FiniteIntermediateField
    K L) :
    IsPerfectResidueLocalField E.val :=
  normedAlgebra_isPerfectResidueLocalField K E.val
local instance FiniteIntermediateField.instIsSeparable (E : FiniteIntermediateField K L) :
    Algebra.IsSeparable E.val L :=
  Algebra.isSeparable_tower_top_of_isSeparable K E.val L

/-- The high-break condition is the full relative upper product,
on the canonical separable embedding of the extension over `E`. -/
def FiniteIntermediateField.HasFullUpper (E : FiniteIntermediateField K L) (b : ℝ) : Prop :=
  apfSubgroup E.val (IsSepClosed.lift : L →ₐ[E.val] SeparableClosure E.val).fieldRange b = ⊤

/-- The high-break condition is unchanged for every choice of separable
embedding over the finite field. -/
theorem FiniteIntermediateField.hasFullUpper_iff_embedding (E : FiniteIntermediateField K L)
    (i : L →ₐ[E.val] SeparableClosure E.val) (b : ℝ) :
    E.HasFullUpper K L b ↔ apfSubgroup E.val i.fieldRange b = ⊤ :=
  apfSubgroup_fieldRange_eq_top_iff E.val L _ i b

/-- At the finite-base Herbrand parameter, the full relative product
is exactly containment of the absolute APF stage in the field. -/
theorem FiniteIntermediateField.hasFullUpper_apfPsi_iff (E : FiniteIntermediateField K L)
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : 0 ≤ u) :
    E.HasFullUpper K L (apfPsi K E.val u) ↔
      apfFiniteStage K j.fieldRange u ≤ E.val.map j := by
  let jE := j.comp E.val.val
  let : Algebra E.val (SeparableClosure K) := jE.toRingHom.toAlgebra
  let : IsScalarTower K E.val (SeparableClosure K) := IsScalarTower.of_algHom jE
  let e := AbstractFiniteBase.closureEquiv K E.val
  let jL : L →ₐ[E.val] SeparableClosure K :=
    { j.toRingHom with commutes' := fun _ => rfl }
  let i := e.symm.toAlgHom.comp jL
  have he : AbstractFiniteBase.embedding K E.val i = j := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply (jL x)
  have hr : (AbstractFiniteBase.closureHom K E.val).range = (E.val.map j).fixingSubgroup := by
    rw [AbstractFiniteBase.closureHom_range K E.val]
    have hjE : IsScalarTower.toAlgHom K E.val (SeparableClosure K) = jE := by
      ext x
      rfl
    rw [hjE, IntermediateField.fieldRange_comp_val]
  have hcomp := AbstractFiniteBase.comap_apf K E.val i (by linarith : -1 ≤ u)
  rw [he] at hcomp
  have hiff : E.HasFullUpper K L (apfPsi K E.val u) ↔
      (apfSubgroup K j.fieldRange u).comap (AbstractFiniteBase.closureHom K E.val) = ⊤ := by
    rw [hcomp]
    exact apfSubgroup_fieldRange_eq_top_iff E.val L _ _ _
  rw [hiff]
  constructor
  · intro h
    have hfix : (E.val.map j).fixingSubgroup ≤ apfSubgroup K j.fieldRange u := by
      rw [← hr]
      rintro g ⟨a, rfl⟩
      exact (show a ∈ (apfSubgroup K j.fieldRange u).comap
        (AbstractFiniteBase.closureHom K E.val) from h ▸ Subgroup.mem_top a)
    exact (IntermediateField.fixedField_le hfix).trans_eq
      (InfiniteGalois.fixedField_fixingSubgroup (E.val.map j))
  · intro h
    have hfix : (AbstractFiniteBase.closureHom K E.val).range ≤
        apfSubgroup K j.fieldRange u := by
      rw [hr]
      exact (IntermediateField.fixingSubgroup_le h).trans_eq
        (fixingSubgroup_apfFiniteStage K j.fieldRange u)
    apply top_unique
    intro g _
    exact hfix ⟨g, rfl⟩

/-- A positive relative upper parameter corresponds to the positive
absolute stage through the finite-base inverse Herbrand function. -/
theorem FiniteIntermediateField.hasFullUpper_iff_stage_le (E : FiniteIntermediateField K L)
    (j : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : 0 ≤ b) :
    E.HasFullUpper K L b ↔ apfFiniteStage K j.fieldRange
      (apfPhi K E.val b) ≤ E.val.map j := by
  have hu : 0 ≤ apfPhi K E.val b := by
    have h := (strictMono_apfPhi K E.val).monotone hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using h
  simpa only [apfPsi_apfPhi] using E.hasFullUpper_apfPsi_iff K L j hu

section PositiveWild

/-- At every positive upper stage, all finite oversteps
have p-power degree. This extends the upper-one wild-tail argument without
requiring either intermediate field to be normal. -/
theorem finrank_eq_prime_pow_of_apfFiniteStage_pos_le
    (L E F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (hFL : F ≤ L) (hEF : E ≤ F) {u : ℝ} (hu : 0 < u)
    (hstage : apfFiniteStage K L u ≤ E) :
    ∃ n : ℕ, Module.finrank E (IntermediateField.extendScalars hEF) = p ^ n := by
  let Ω := finiteGaloisNormalClosure K F
  let M := E.comap Ω.toIntermediateField.val
  let N := F.comap Ω.toIntermediateField.val
  have hFΩ : F ≤ Ω.toIntermediateField := le_finiteGaloisNormalClosure K F
  have hEΩ : E ≤ Ω.toIntermediateField := hEF.trans hFΩ
  have hM : M.map Ω.toIntermediateField.val = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hEΩ hx⟩, hx, rfl⟩
  have hN : N.map Ω.toIntermediateField.val = F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hFΩ hx⟩, hx, rfl⟩
  let ρ : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* (Ω ≃ₐ[K] Ω) :=
    AlgEquiv.restrictNormalHom Ω
  let A := L.fixingSubgroup.map ρ
  let B := N.fixingSubgroup
  let C := M.fixingSubgroup
  let U := upperRamificationGroup (R := spectralIntegerRing K Ω) (Ω ≃ₐ[K] Ω) u
  have hρ : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Ω) (SeparableClosure K)
  have hfixE : E.fixingSubgroup = C.comap ρ := by
    rw [← hM]
    exact IntermediateField.map_fixingSubgroup (F := K) (E := Ω)
      (E' := SeparableClosure K) (L := M)
  have hfixF : F.fixingSubgroup = B.comap ρ := by
    rw [← hN]
    exact IntermediateField.map_fixingSubgroup (F := K) (E := Ω)
      (E' := SeparableClosure K) (L := N)
  have hmapE : E.fixingSubgroup.map ρ = C := by
    rw [hfixE, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hρ, top_inf_eq]
  have hmapF : F.fixingSubgroup.map ρ = B := by
    rw [hfixF, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hρ, top_inf_eq]
  have hAB : A ≤ B := by
    rw [← hmapF]
    exact Subgroup.map_mono (IntermediateField.fixingSubgroup_le hFL)
  have hBC : B ≤ C :=
    IntermediateField.fixingSubgroup_le (show M ≤ N from fun _ hx => hEF hx)
  have hCU : C ≤ A ⊔ U := by
    have hfix : E.fixingSubgroup ≤ apfSubgroup K L u :=
      (IntermediateField.fixingSubgroup_le hstage).trans_eq
        (fixingSubgroup_apfFiniteStage K L u)
    have h := Subgroup.map_mono (f := ρ) hfix
    rw [hmapE] at h
    change C ≤ (L.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u).map ρ at h
    rw [Subgroup.map_sup, absolute_map_upperRamificationGroup K Ω u (by linarith)] at h
    exact h
  have hU : IsPGroup p U := by
    let : CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField
          (NormedField.valuation (K := K)).valuationSubring)
          (IsLocalRing.ResidueField (spectralIntegerRing K Ω))).injective p
    exact (lowerRamificationGroup_one_isPGroup (Ω ≃ₐ[K] Ω) p).to_le
      (upperRamificationGroup_le_lower_one (Ω ≃ₐ[K] Ω) hu)
  obtain ⟨n, hn⟩ := relIndex_eq_prime_pow_of_le_sup p A B C U hU hAB hBC hCU
  refine ⟨n, ?_⟩
  rw [← fixingSubgroup_relIndex_eq_finrank K E F hEF, hfixF,
    Subgroup.relIndex_comap, hmapE]
  exact hn

end PositiveWild

/-- Decreasing a nonnegative upper parameter preserves the full product. -/
theorem FiniteIntermediateField.HasFullUpper.of_le {E : FiniteIntermediateField K L} {b c : ℝ}
    (h : E.HasFullUpper K L b) (hc : 0 ≤ c) (hcb : c ≤ b) :
    E.HasFullUpper K L c := by
  apply top_unique
  have hm := apfSubgroup_antitoneOn E.val
    (IsSepClosed.lift : L →ₐ[E.val] SeparableClosure E.val).fieldRange
    (by linarith : -1 ≤ c) (by linarith : -1 ≤ b) hcb
  exact h ▸ hm

/-- Full relative upper products become arbitrarily deep on an
finite-field tail; this retains the product, rather than only its first bound. -/
theorem IsAPF.exists_finiteIntermediateField_fullUpper_tail [IsAPF K L] (b : ℝ) (hb : 0 ≤ b) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E → E.HasFullUpper K
        L b := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨T, hT⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (by linarith : -1 ≤ b)
  refine ⟨T, fun E hTE ↦ ?_⟩
  have hstage : apfFiniteStage K j.fieldRange b ≤ E.val.map j := by
    rw [← hT]
    exact IntermediateField.map_mono j hTE
  have h := (E.hasFullUpper_apfPsi_iff K L j hb).mpr hstage
  exact h.of_le K L hb (IsAPF.le_apfPsi K E.val b)

/-- A positive full relative product forces every finite overstep
to have surjective residue inclusion. -/
theorem FiniteIntermediateField.HasFullUpper.residue_surjective
    [IsAPF K L] {E : FiniteIntermediateField K L} {b : ℝ} (hb : 0 < b)
    (h : E.HasFullUpper K L b) (F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    Function.Surjective (spectralResidueInclusion K (IntermediateField.inclusion hEF)) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := apfPhi K E.val b
  have hu : 0 < u := by
    have ht := strictMono_apfPhi K E.val hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using ht
  have hstage := (E.hasFullUpper_iff_stage_le K L j hb.le).mp h
  have hzero : apfFiniteStage K j.fieldRange 0 ≤ E.val.map j :=
    (apfFiniteStage_mono K j.fieldRange (by norm_num) (by linarith) hu.le).trans hstage
  have hmap : E.val.map j ≤ F.val.map j := IntermediateField.map_mono j hEF
  have : FiniteDimensional K (E.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap E.val j).toLinearEquiv
  have : FiniteDimensional K (F.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap F.val j).toLinearEquiv
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro z ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hd := (residueDegree_eq_zeroStage_of_apfFiniteStage_le K j.fieldRange
    (E.val.map j) (hmap.trans hFL) hzero).trans
      (residueDegree_eq_zeroStage_of_apfFiniteStage_le K j.fieldRange
        (F.val.map j) hFL (hzero.trans hmap)).symm
  rw [spectral_residueDegree_algEquiv K E.val (IntermediateField.equivMap E.val j),
    spectral_residueDegree_algEquiv K F.val (IntermediateField.equivMap F.val j)] at hd
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := (spectralResidueInclusion K (IntermediateField.inclusion hEF)).toLinearMap)).mp
      (spectralResidueInclusion K (IntermediateField.inclusion hEF)).injective

/-- Every finite overstep above a positive full relative product has p-power
degree, on the finite carriers. -/
theorem FiniteIntermediateField.HasFullUpper.finrank_eq_prime_pow
    {E : FiniteIntermediateField K L} {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)
    (F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    ∃ n : ℕ, Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ n := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := apfPhi K E.val b
  have hu : 0 < u := by
    have ht := strictMono_apfPhi K E.val hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using ht
  have hstage := (E.hasFullUpper_iff_stage_le K L j hb.le).mp h
  have : FiniteDimensional K (F.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap F.val j).toLinearEquiv
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro z ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : E.val.map j ≤ F.val.map j := IntermediateField.map_mono j hEF
  obtain ⟨n, hn⟩ := finrank_eq_prime_pow_of_apfFiniteStage_pos_le K
    j.fieldRange (E.val.map j) (F.val.map j) hFL hmap hu hstage
  refine ⟨n, ?_⟩
  rw [← IntermediateField.relfinrank_eq_finrank_of_le hmap,
    IntermediateField.relfinrank_map_map,
    IntermediateField.relfinrank_eq_finrank_of_le hEF] at hn
  exact hn

/-- The relative first bound of every finite overstep is at least the
specified full relative upper parameter, including the identity step. -/
theorem FiniteIntermediateField.HasFullUpper.le_relativeFirstBound
    {E : FiniteIntermediateField K L} {b : ℝ} (hb : 0 ≤ b) (h : E.HasFullUpper K L b)
    (F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    (b : EReal) ≤ apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := apfPhi K E.val b
  have hu : 0 ≤ u := by
    have ht := (strictMono_apfPhi K E.val).monotone hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using ht
  have hstage := (E.hasFullUpper_iff_stage_le K L j hb).mp h
  have ht := apfPsi_le_relativeFirstBound_of_apfFiniteStage_le K L E F hEF j hu hstage
  simpa only [u, apfPsi_apfPhi] using ht

/-- At a positive full relative upper product the E-coordinate
computes the normalized valuation of every norm family, including
zero and nonintegral families. -/
theorem FieldOfNorms.valuation_eq_coordinate_of_fullUpper
    [IsAPF K L] {E : FiniteIntermediateField K L} {b : ℝ} (hb : 0 < b)
    (h : E.HasFullUpper K L b) (α : FieldOfNorms K L) :
    FieldOfNorms.valuation K L α = FieldOfNorms.coordinateValuation K L E α := by
  obtain ⟨V, hV⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  let F := FiniteIntermediateField.sup E V
  have hEF : E ≤ F := FiniteIntermediateField.le_sup_left E V
  rw [hV F (FiniteIntermediateField.le_sup_right E V)]
  have hv := FiniteIntermediateField.normalizedValuation_norm_of_residueInclusion_surjective K L
    E F hEF (h.residue_surjective K L hb F hEF) (FieldOfNorms.coord K L F α)
  rw [FieldOfNorms.coord_norm] at hv
  exact hv.symm

/-- Any prescribed nonnegative depths are attained by an increasing cofinal
sequence of finite subfields, each with its full upper product.
No growth assumption on the depths is needed for this stronger statement. -/
theorem IsAPF.exists_monotone_cofinal_fullUpper_stages [IsAPF K L]
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    ∃ E : ℕ → FiniteIntermediateField K L, Monotone E ∧
      (∀ n, (E n).HasFullUpper K L (b n)) ∧
      ∀ D : FiniteIntermediateField K L, ∃ n, D ≤ E n := by
  let T (n : ℕ) := (IsAPF.exists_finiteIntermediateField_fullUpper_tail K L (b n) (hb n)).choose
  obtain ⟨E, hmono, hTE, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_finiteIntermediateFields_ge K L T
  exact ⟨E, hmono, fun n ↦
    (IsAPF.exists_finiteIntermediateField_fullUpper_tail K L (b n) (hb n)).choose_spec
      (E n) (hTE n), hcofinal⟩

section Projections

variable [IsAPF K L]
variable {E : FiniteIntermediateField K L} {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)

/-- The finite norm on integer quotients, whose wildness,
total ramification and first-bound hypotheses follow from the full
upper product of the infinite extension. -/
def FiniteIntermediateField.HasFullUpper.truncatedNorm (F : FiniteIntermediateField K L) (hEF : E ≤
    F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let hd := h.finrank_eq_prime_pow K L hb F hEF
  exact FiniteIntermediateField.truncatedNorm E F hEF hd.choose b
    (FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective K L E F hEF
      (h.residue_surjective K L hb F hEF)) hd.choose_spec
    (h.le_relativeFirstBound K L hb.le F hEF) r s hrs hrb

/-- The finite quotient map is the class of the integer norm. -/
@[simp]
theorem FiniteIntermediateField.HasFullUpper.truncatedNorm_mk (F : FiniteIntermediateField K L)
    (hEF : E ≤ F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val) :
    h.truncatedNorm K L hb F hEF r s hrs hrb (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (FiniteIntermediateField.integerNorm E F hEF x) := rfl

/-- Surjectivity is supplied by the finite wild norm digit argument. -/
theorem FiniteIntermediateField.HasFullUpper.truncatedNorm_surjective
    (F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (h.truncatedNorm K L hb F hEF r s hrs hrb) := by
  let hd := h.finrank_eq_prime_pow K L hb F hEF
  exact FiniteIntermediateField.truncatedNorm_surjective E F hEF hd.choose b
    (FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective K L E F hEF
      (h.residue_surjective K L hb F hEF)) hd.choose_spec
    (h.le_relativeFirstBound K L hb.le F hEF) r s hrs hrb

variable [Fact (¬ Module.Finite K L)]

/-- Integral evaluation in any finite intermediate field, with no chosen model. -/
def FieldOfNorms.integralCoordinateAt (E : FiniteIntermediateField K L) :
    (FieldOfNorms.fieldValuation K L).valuationSubring → spectralIntegerRing K E.val :=
        by
  exact fun α ↦ ⟨FieldOfNorms.coord K L E α.val,
    FieldOfNorms.coord_mem_of_valuation_le_one K L α.val α.property E⟩

/-- The high-break coordinate ring map. Its construction composes the
proved deep projection with the finite truncated norm back to E. -/
def FieldOfNorms.highBreakProjection (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (FieldOfNorms.fieldValuation K L).valuationSubring →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  exact (h.truncatedNorm K L hb (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) r (r + 2) (by omega) hrb).comp
      (FieldOfNorms.truncation K L E r)

/-- The constructed ring homomorphism is precisely reduction of the
E-coordinate, by the norm-family compatibility. -/
@[simp]
theorem FieldOfNorms.highBreakProjection_apply
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
      FieldOfNorms.highBreakProjection K L hb h r hrb α =
        Ideal.Quotient.mk _ (FieldOfNorms.integralCoordinateAt K L E α) := by
  intro α
  change h.truncatedNorm K L hb _ _ r (r + 2) (by omega) hrb
    (FieldOfNorms.truncation K L E r α) = _
  rw [FieldOfNorms.truncation_apply, FiniteIntermediateField.HasFullUpper.truncatedNorm_mk]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  rw [FiniteIntermediateField.coe_integerNorm]
  exact FieldOfNorms.coord_norm K L E (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) α.val

/-- Every class of the integer quotient occurs as an
norm-family coordinate. Both surjections are proved on their carriers. -/
theorem FieldOfNorms.highBreakProjection_surjective
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (FieldOfNorms.highBreakProjection K L hb h r hrb) := by
  exact (h.truncatedNorm_surjective K L hb
    (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) r (r + 2) (by omega) hrb).comp
      (FieldOfNorms.truncation_surjective K L E r)

/-- The exact kernel is the normalized valuation ball of depth r. -/
theorem FieldOfNorms.highBreakProjection_eq_zero_iff
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
      FieldOfNorms.highBreakProjection K L hb h r hrb α = 0 ↔
        FieldOfNorms.valuation K L α.val ≤ WithZero.exp (-(r : ℤ)) := by
  intro α
  rw [FieldOfNorms.highBreakProjection_apply, Ideal.Quotient.eq_zero_iff_mem,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    FieldOfNorms.valuation_eq_coordinate_of_fullUpper K L hb h]
  rfl

/-- Equality of quotient coordinates is measured by the same
valuation, at the exact requested precision. -/
theorem FieldOfNorms.highBreakProjection_eq_iff
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α β : (FieldOfNorms.fieldValuation K L).valuationSubring,
      FieldOfNorms.highBreakProjection K L hb h r hrb α =
        FieldOfNorms.highBreakProjection K L hb h r hrb β ↔
          FieldOfNorms.valuation K L (α.val - β.val) ≤ WithZero.exp (-(r : ℤ)) := by
  intro α β
  rw [← sub_eq_zero, ← map_sub, FieldOfNorms.highBreakProjection_eq_zero_iff]
  rfl

/-- The kernel ideal is exactly the r-th maximal-ideal power in the
field of norms valuation ring, with its proved normalized valuation. -/
theorem ker_fieldOfNormsHighBreakProjection
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    RingHom.ker (FieldOfNorms.highBreakProjection K L hb h r hrb) =
      IsLocalRing.maximalIdeal
        (FieldOfNorms.fieldValuation K L).valuationSubring ^ r := by
  ext α
  rw [RingHom.mem_ker, FieldOfNorms.highBreakProjection_eq_zero_iff,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    FieldOfNorms.fieldValuation_eq_normalized K L]
  rfl

end Projections

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

open Polynomial

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring (FieldOfNorms.fieldValuation K L)

/-- Integral coordinate evaluation preserves zero. -/
@[simp]
theorem FieldOfNorms.integralCoordinateAt_zero (E : FiniteIntermediateField K L) :
    FieldOfNorms.integralCoordinateAt K L E 0 = 0 := by
  exact Subtype.ext (_root_.map_zero (FieldOfNorms.coord K L E))

/-- Integral coordinate evaluation preserves one. -/
@[simp]
theorem FieldOfNorms.integralCoordinateAt_one (E : FiniteIntermediateField K L) :
    FieldOfNorms.integralCoordinateAt K L E 1 = 1 := by
  exact Subtype.ext (_root_.map_one (FieldOfNorms.coord K L E))

/-- The polynomial of coordinates, formed by its finite
coefficient expansion. No additive coordinate homomorphism is presumed. -/
def FieldOfNorms.coordinatePolynomial (E : FiniteIntermediateField K L) :
    Oₓ[X] → (spectralIntegerRing K E.val)[X] := by
  intro f
  exact ∑ i ∈ f.support,
    monomial i (FieldOfNorms.integralCoordinateAt K L E (f.coeff i))

/-- Every coefficient is the finite coordinate of that same
coefficient of the polynomial. -/
@[simp]
theorem coeff_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ (f : Oₓ[X]) (i : ℕ),
      (FieldOfNorms.coordinatePolynomial K L E f).coeff i =
        FieldOfNorms.integralCoordinateAt K L E (f.coeff i) := by
  classical
  intro f i
  by_cases hi : f.coeff i = 0
  · simp [FieldOfNorms.coordinatePolynomial, coeff_monomial, mem_support_iff, hi]
  · simp [FieldOfNorms.coordinatePolynomial, coeff_monomial, mem_support_iff, hi]

/-- The coordinate polynomial has exactly the monic degree. -/
theorem natDegree_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      (FieldOfNorms.coordinatePolynomial K L E f).natDegree = f.natDegree := by
  intro f hf
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_fieldOfNormsCoordinatePolynomial, coeff_eq_zero_of_natDegree_lt hi,
      FieldOfNorms.integralCoordinateAt_zero]
  · rw [coeff_fieldOfNormsCoordinatePolynomial, hf.coeff_natDegree,
      FieldOfNorms.integralCoordinateAt_one]
    exact one_ne_zero

/-- The same coordinate polynomial is monic in the integers. -/
theorem monic_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      (FieldOfNorms.coordinatePolynomial K L E f).Monic := by
  intro f hf
  change (FieldOfNorms.coordinatePolynomial K L E f).coeff
    (FieldOfNorms.coordinatePolynomial K L E f).natDegree = 1
  rw [natDegree_fieldOfNormsCoordinatePolynomial K L E f hf,
    coeff_fieldOfNormsCoordinatePolynomial, hf.coeff_natDegree,
        FieldOfNorms.integralCoordinateAt_one]

/-- Passing the integral coefficient polynomial into its finite
field preserves monicity. -/
theorem monic_map_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Monic := by
  intro f hf
  exact (monic_fieldOfNormsCoordinatePolynomial K L E f hf).map _

/-- The finite-field polynomial also has precisely the degree. -/
theorem natDegree_map_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).natDegree = f.natDegree := by
  intro f hf
  rw [(monic_fieldOfNormsCoordinatePolynomial K L E f hf).natDegree_map,
    natDegree_fieldOfNormsCoordinatePolynomial K L E f hf]

variable (E : FiniteIntermediateField K L) {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)

/-- Reduction of the coefficient polynomial agrees with mapping the
polynomial by the high-break quotient ring homomorphism. -/
theorem map_fieldOfNormsCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X],
      (FieldOfNorms.coordinatePolynomial K L E f).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)) =
          f.map (FieldOfNorms.highBreakProjection K L hb h r hrb) := by
  intro f
  ext i
  simp only [coeff_map, coeff_fieldOfNormsCoordinatePolynomial,
      FieldOfNorms.highBreakProjection_apply]

/-- The existing discriminant commutes with the original-coordinate reduction;
the unreduced coordinate evaluation is never used as a ring homomorphism. -/
theorem FieldOfNorms.highBreakProjection_discr
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X], f.Monic →
      FieldOfNorms.highBreakProjection K L hb h r hrb f.discr =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)
          (FieldOfNorms.coordinatePolynomial K L E f).discr := by
  intro f hf
  have hd := congrArg Polynomial.discr
    (map_fieldOfNormsCoordinatePolynomial K L E hb h r hrb f)
  rw [Polynomial.Monic.discr_map _ (monic_fieldOfNormsCoordinatePolynomial K L E f hf),
    Polynomial.Monic.discr_map f hf] at hd
  exact hd.symm

include hb h in
/-- The coordinate of the discriminant and the discriminant
of the coordinate polynomial differ by the proved ideal precision. -/
theorem FieldOfNorms.coordinatePolynomial_discr_sub_mem
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X], f.Monic →
      FieldOfNorms.integralCoordinateAt K L E f.discr -
        (FieldOfNorms.coordinatePolynomial K L E f).discr ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  intro f hf
  apply Ideal.Quotient.eq.mp
  rw [← FieldOfNorms.highBreakProjection_apply]
  exact FieldOfNorms.highBreakProjection_discr K L E hb h r hrb f hf

include hb h in
/-- Above the discriminant precision, the finite-coordinate
discriminant has exactly the stable normalized valuation. -/
theorem FieldOfNorms.coordinatePolynomial_discr_valuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) =
        FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) := by
  intro f hf hr
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  let x := FieldOfNorms.integralCoordinateAt K L E f.discr
  let y := (FieldOfNorms.coordinatePolynomial K L E f).discr
  have hc : v (x : E.val) = FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) :=
    (FieldOfNorms.valuation_eq_coordinate_of_fullUpper K L hb h
      (f.discr : FieldOfNorms K L)).symm
  have hm : y - x ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
    simpa only [neg_sub] using (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r).neg_mem
      (FieldOfNorms.coordinatePolynomial_discr_sub_mem K L E hb h r hrb f hf)
  have hv := (ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) (y - x) r).mp hm
  change v ((y : E.val) - (x : E.val)) ≤ WithZero.exp (-(r : ℤ)) at hv
  exact (v.map_eq_of_sub_lt (hv.trans_lt (hr.trans_eq hc.symm))).trans hc

include hb h in
/-- The equality is also equality of the associated normalized
additive valuations on the two fields. -/
theorem FieldOfNorms.coordinatePolynomial_discr_additiveValuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      (Valuation.toAddValuation
        ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val))
          ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) =
        (Valuation.toAddValuation (FieldOfNorms.fieldValuation K L))
          (f.discr : FieldOfNorms K L) := by
  intro f hf hr
  exact congrArg (fun z ↦ OrderDual.toDual (Additive.ofMul z))
    (FieldOfNorms.coordinatePolynomial_discr_valuation K L E hb h r hrb f hf hr)

include hb h in
/-- At the same proved precision the finite-field coordinate polynomial
is separable, because its discriminant has nonzero valuation. -/
theorem separable_fieldOfNormsCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Separable := by
  intro f hf hr
  have hfE := monic_fieldOfNormsCoordinatePolynomial K L E f hf
  apply (monic_discr_ne_zero_iff _ (hfE.map
    (algebraMap (spectralIntegerRing K E.val) E.val))).mp
  rw [Polynomial.Monic.discr_map _ hfE]
  intro hz
  change ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) = 0 at hz
  have hv := FieldOfNorms.coordinatePolynomial_discr_valuation K L E hb h r hrb f hf hr
  rw [hz, map_zero] at hv
  exact (not_lt_of_ge zero_le) (hr.trans_eq hv.symm)

/-- Separability supplies a finite precision strictly beyond the
nonzero discriminant value. -/
theorem exists_fieldOfNorms_discr_precision :
    ∀ (f : Oₓ[X]), f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
      ∃ r : ℕ, WithZero.exp (-(r : ℤ)) <
        FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) := by
  intro f hf hsep
  have hd := (monic_discr_ne_zero_iff _ (hf.map (algebraMap Oₓ (FieldOfNorms K L)))).mpr hsep
  rw [Polynomial.Monic.discr_map f hf] at hd
  change (f.discr : FieldOfNorms K L) ≠ 0 at hd
  let w := FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L)
  have hw : w ≠ 0 := fun hz ↦ hd ((FieldOfNorms.valuation_eq_zero_iff K L _).mp hz)
  let r := (-WithZero.log w).toNat + 1
  refine ⟨r, (WithZero.lt_log_iff_exp_lt hw).mp ?_⟩
  dsimp [r]
  omega

/-- Along every finite-coordinate sequence with full products
at depths tending to infinity, the discriminant value is eventually
constant and the coordinate polynomials are separable. -/
theorem eventually_fieldOfNormsCoordinatePolynomial_discr_stable
    (F : ℕ → FiniteIntermediateField K L) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hF : ∀ n, (F n).HasFullUpper K L (c n))
    (hctop : Filter.Tendsto c Filter.atTop Filter.atTop) :
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
      ∀ᶠ n in Filter.atTop,
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
            (F n).val ((FieldOfNorms.coordinatePolynomial K L (F n) f).discr : (F n).val)
                =
          FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) ∧
        ((FieldOfNorms.coordinatePolynomial K L (F n) f).map
          (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  intro f hf hsep
  obtain ⟨r, hr⟩ := exists_fieldOfNorms_discr_precision K L f hf hsep
  have hp : 0 < ((p - 1 : ℕ) : ℝ) / p := by
    have hp' := (Fact.out : Nat.Prime p).two_le
    have h₁ : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
    exact div_pos h₁ (by exact_mod_cast (Fact.out : Nat.Prime p).pos)
  have htop := Filter.Tendsto.const_mul_atTop hp hctop
  filter_upwards [htop.eventually (Filter.eventually_ge_atTop (r : ℝ))] with n hn
  have hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * c n⌉₊ := by
    exact_mod_cast hn.trans (Nat.le_ceil _)
  exact ⟨FieldOfNorms.coordinatePolynomial_discr_valuation K L (F n)
      (hc n) (hF n) r hrb f hf hr,
    separable_fieldOfNormsCoordinatePolynomial K L (F n)
      (hc n) (hF n) r hrb f hf hr⟩

/-- An increasing cofinal sequence of finite fields has full
upper depths tending to infinity and stabilizes every monic separable
polynomial's discriminant, with eventual finite-field separability. -/
theorem exists_cofinal_fieldOfNormsCoordinatePolynomial_discr_stable :
    ∃ F : ℕ → FiniteIntermediateField K L, Monotone F ∧
      (∀ n, (F n).HasFullUpper K L ((n : ℝ) + 1)) ∧
      (∀ D : FiniteIntermediateField K L, ∃ n, D ≤ F n) ∧
      ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
        ∀ᶠ n in Filter.atTop,
          (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
              (F n).val ((FieldOfNorms.coordinatePolynomial K L (F n) f).discr : (F
                  n).val) =
            FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) ∧
          ((FieldOfNorms.coordinatePolynomial K L (F n) f).map
            (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  let c (n : ℕ) : ℝ := (n : ℝ) + 1
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  obtain ⟨F, hmono, hF, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_fullUpper_stages K L c (fun n ↦ (hc n).le)
  refine ⟨F, hmono, hF, hcofinal, ?_⟩
  apply eventually_fieldOfNormsCoordinatePolynomial_discr_stable K L F c hc hF
  exact Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
    tendsto_natCast_atTop_atTop

end FontaineWintenberger
