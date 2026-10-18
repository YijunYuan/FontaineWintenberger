/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Residue
public import FontaineWintenberger.APF.DeepTail

/-!
# Original coordinates at arbitrary high-break stages

The relative full upper product is compared with the actual absolute APF stage.
The resulting wild finite norms descend the existing deep integral projection
to the original finite field and its original maximal-ideal quotient.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local instance FiniteLayer.instNontriviallyNormedField (E : FiniteLayer K L) :
    NontriviallyNormedField E.val :=
  spectralNorm.nontriviallyNormedField K E.val
local instance FiniteLayer.instNormedAlgebra (E : FiniteLayer K L) : NormedAlgebra K E.val :=
  spectralNorm.normedAlgebra K E.val
local instance FiniteLayer.instIsUltrametricDist (E : FiniteLayer K L) : IsUltrametricDist E.val :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
local instance FiniteLayer.instCompleteSpace (E : FiniteLayer K L) : CompleteSpace E.val :=
  spectralNorm.completeSpace K E.val
local instance FiniteLayer.instIsPerfectResidueLocalField (E : FiniteLayer K L) :
    IsPerfectResidueLocalField E.val :=
  normedAlgebra_isPerfectResidueLocalField K E.val
local instance FiniteLayer.instIsSeparable (E : FiniteLayer K L) : Algebra.IsSeparable E.val L :=
  Algebra.isSeparable_tower_top_of_isSeparable K E.val L

/-- The source high-break condition is the actual full relative upper product,
on the canonical separable embedding of the original extension over `E`. -/
def FiniteLayer.HasFullUpper (E : FiniteLayer K L) (b : ℝ) : Prop :=
  apfSubgroup E.val (IsSepClosed.lift : L →ₐ[E.val] SeparableClosure E.val).fieldRange b = ⊤

/-- The high-break condition is unchanged for every actual choice of separable
embedding over the original finite field. -/
theorem FiniteLayer.hasFullUpper_iff_embedding (E : FiniteLayer K L)
    (i : L →ₐ[E.val] SeparableClosure E.val) (b : ℝ) :
    E.HasFullUpper K L b ↔ apfSubgroup E.val i.fieldRange b = ⊤ :=
  apfSubgroup_fieldRange_eq_top_iff E.val L _ i b

/-- At the original finite-base Herbrand parameter, the full relative product
is exactly containment of the actual absolute APF stage in the original field. -/
theorem FiniteLayer.hasFullUpper_apfPsi_iff (E : FiniteLayer K L)
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

/-- A positive relative upper parameter corresponds to the actual positive
absolute stage through the original finite-base inverse Herbrand function. -/
theorem FiniteLayer.hasFullUpper_iff_stage_le (E : FiniteLayer K L)
    (j : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : 0 ≤ b) :
    E.HasFullUpper K L b ↔ apfFiniteStage K j.fieldRange
      (apfPhi K E.val b) ≤ E.val.map j := by
  have hu : 0 ≤ apfPhi K E.val b := by
    have h := (strictMono_apfPhi K E.val).monotone hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using h
  simpa only [apfPsi_apfPhi] using E.hasFullUpper_apfPsi_iff K L j hu

section PositiveWild

/-- At every positive actual upper stage, all original finite oversteps
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

/-- Decreasing a nonnegative upper parameter preserves the actual full product. -/
theorem FiniteLayer.HasFullUpper.of_le {E : FiniteLayer K L} {b c : ℝ}
    (h : E.HasFullUpper K L b) (hc : 0 ≤ c) (hcb : c ≤ b) :
    E.HasFullUpper K L c := by
  apply top_unique
  have hm := apfSubgroup_antitoneOn E.val
    (IsSepClosed.lift : L →ₐ[E.val] SeparableClosure E.val).fieldRange
    (by linarith : -1 ≤ c) (by linarith : -1 ≤ b) hcb
  exact h ▸ hm

/-- Actual full relative upper products become arbitrarily deep on an original
finite-field tail; this retains the product, rather than only its first bound. -/
theorem IsAPF.exists_finiteLayer_fullUpper_tail [IsAPF K L] (b : ℝ) (hb : 0 ≤ b) :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E → E.HasFullUpper K L b := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨T, hT⟩ := exists_finiteLayer_map_eq_apfFiniteStage K L j
    (by linarith : -1 ≤ b)
  refine ⟨T, fun E hTE ↦ ?_⟩
  have hstage : apfFiniteStage K j.fieldRange b ≤ E.val.map j := by
    rw [← hT]
    exact IntermediateField.map_mono j hTE
  have h := (E.hasFullUpper_apfPsi_iff K L j hb).mpr hstage
  exact h.of_le K L hb (IsAPF.le_apfPsi K E.val b)

/-- A positive full relative product forces every original finite overstep
to have surjective original residue inclusion. -/
theorem FiniteLayer.HasFullUpper.residue_surjective
    [IsAPF K L] {E : FiniteLayer K L} {b : ℝ} (hb : 0 < b)
    (h : E.HasFullUpper K L b) (F : FiniteLayer K L) (hEF : E ≤ F) :
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
degree, on the original finite carriers. -/
theorem FiniteLayer.HasFullUpper.finrank_eq_prime_pow
    {E : FiniteLayer K L} {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)
    (F : FiniteLayer K L) (hEF : E ≤ F) :
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

/-- The actual relative first bound of every finite overstep is at least the
specified full relative upper parameter, including the identity step. -/
theorem FiniteLayer.HasFullUpper.le_relativeFirstBound
    {E : FiniteLayer K L} {b : ℝ} (hb : 0 ≤ b) (h : E.HasFullUpper K L b)
    (F : FiniteLayer K L) (hEF : E ≤ F) :
    (b : EReal) ≤ apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := apfPhi K E.val b
  have hu : 0 ≤ u := by
    have ht := (strictMono_apfPhi K E.val).monotone hb
    simpa only [apfPhi_of_nonpos K E.val le_rfl] using ht
  have hstage := (E.hasFullUpper_iff_stage_le K L j hb).mp h
  have ht := apfPsi_le_relativeFirstBound_of_apfFiniteStage_le K L E F hEF j hu hstage
  simpa only [u, apfPsi_apfPhi] using ht

/-- At a positive full relative upper product the original E-coordinate
computes the normalized valuation of every original norm family, including
zero and nonintegral families. -/
theorem normLimitValuation_eq_coordinate_of_fullUpper
    [IsAPF K L] {E : FiniteLayer K L} {b : ℝ} (hb : 0 < b)
    (h : E.HasFullUpper K L b) (α : NormLimit K L) :
    normLimitValuation K L α = normLimitCoordinateValuation K L E α := by
  obtain ⟨V, hV⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L
  let F := FiniteLayer.sup E V
  have hEF : E ≤ F := FiniteLayer.le_sup_left E V
  rw [hV F (FiniteLayer.le_sup_right E V)]
  have hv := FiniteLayer.normalizedValuation_norm_of_residueInclusion_surjective K L
    E F hEF (h.residue_surjective K L hb F hEF) (normLimitEval K L F α)
  rw [normLimitEval_norm] at hv
  exact hv.symm

/-- Any prescribed nonnegative depths are attained by an increasing cofinal
sequence of original finite subfields, each with its actual full upper product.
No growth assumption on the depths is needed for this stronger statement. -/
theorem IsAPF.exists_monotone_cofinal_fullUpper_stages [IsAPF K L]
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    ∃ E : ℕ → FiniteLayer K L, Monotone E ∧
      (∀ n, (E n).HasFullUpper K L (b n)) ∧
      ∀ D : FiniteLayer K L, ∃ n, D ≤ E n := by
  let T (n : ℕ) := (IsAPF.exists_finiteLayer_fullUpper_tail K L (b n) (hb n)).choose
  obtain ⟨E, hmono, hTE, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_finiteLayers_ge K L T
  exact ⟨E, hmono, fun n ↦
    (IsAPF.exists_finiteLayer_fullUpper_tail K L (b n) (hb n)).choose_spec
      (E n) (hTE n), hcofinal⟩

section Projections

variable [IsAPF K L]
variable {E : FiniteLayer K L} {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)

/-- The original finite norm on original integer quotients, whose wildness,
total ramification and first-bound hypotheses follow from the actual full
upper product of the original infinite extension. -/
def FiniteLayer.HasFullUpper.truncatedNorm (F : FiniteLayer K L) (hEF : E ≤ F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let hd := h.finrank_eq_prime_pow K L hb F hEF
  exact FiniteLayer.truncatedNorm E F hEF hd.choose b
    (FiniteLayer.ramificationIdx_eq_finrank_of_residueInclusion_surjective K L E F hEF
      (h.residue_surjective K L hb F hEF)) hd.choose_spec
    (h.le_relativeFirstBound K L hb.le F hEF) r s hrs hrb

/-- The finite quotient map is the class of the original integer norm. -/
@[simp]
theorem FiniteLayer.HasFullUpper.truncatedNorm_mk (F : FiniteLayer K L) (hEF : E ≤ F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val) :
    h.truncatedNorm K L hb F hEF r s hrs hrb (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (FiniteLayer.integerNorm E F hEF x) := rfl

/-- Surjectivity is supplied by the actual finite wild norm digit argument. -/
theorem FiniteLayer.HasFullUpper.truncatedNorm_surjective
    (F : FiniteLayer K L) (hEF : E ≤ F)
    (r s : ℕ) (hrs : r ≤ s) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (h.truncatedNorm K L hb F hEF r s hrs hrb) := by
  let hd := h.finrank_eq_prime_pow K L hb F hEF
  exact FiniteLayer.truncatedNorm_surjective E F hEF hd.choose b
    (FiniteLayer.ramificationIdx_eq_finrank_of_residueInclusion_surjective K L E F hEF
      (h.residue_surjective K L hb F hEF)) hd.choose_spec
    (h.le_relativeFirstBound K L hb.le F hEF) r s hrs hrb

variable [Fact (¬ Module.Finite K L)]

/-- Integral evaluation in any original finite layer, with no chosen model. -/
def normLimitIntegralCoordinateAt (E : FiniteLayer K L) :
    (normLimitFieldValuation K L).valuationSubring → spectralIntegerRing K E.val :=
        by
  exact fun α ↦ ⟨normLimitEval K L E α.val,
    normLimitEval_mem_of_valuation_le_one K L α.val α.property E⟩

/-- The original high-break coordinate ring map. Its construction composes the
proved deep projection with the actual finite truncated norm back to E. -/
def normLimitHighBreakProjection (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (normLimitFieldValuation K L).valuationSubring →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  exact (h.truncatedNorm K L hb (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) r (r + 2) (by omega) hrb).comp
      (normLimitTruncation K L E r)

/-- The constructed ring homomorphism is precisely reduction of the original
E-coordinate, by the original norm-family compatibility. -/
@[simp]
theorem normLimitHighBreakProjection_apply
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
      normLimitHighBreakProjection K L hb h r hrb α =
        Ideal.Quotient.mk _ (normLimitIntegralCoordinateAt K L E α) := by
  intro α
  change h.truncatedNorm K L hb _ _ r (r + 2) (by omega) hrb
    (normLimitTruncation K L E r α) = _
  rw [normLimitTruncation_apply, FiniteLayer.HasFullUpper.truncatedNorm_mk]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  rw [FiniteLayer.coe_integerNorm]
  exact normLimitEval_norm K L E (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) α.val

/-- Every class of the original integer quotient occurs as an actual original
norm-family coordinate. Both surjections are proved on their actual carriers. -/
theorem normLimitHighBreakProjection_surjective
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (normLimitHighBreakProjection K L hb h r hrb) := by
  exact (h.truncatedNorm_surjective K L hb
    (deepFiniteTower K L E r)
    (le_deepFiniteTower K L E r) r (r + 2) (by omega) hrb).comp
      (normLimitTruncation_surjective K L E r)

/-- The exact kernel is the original normalized valuation ball of depth r. -/
theorem normLimitHighBreakProjection_eq_zero_iff
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
      normLimitHighBreakProjection K L hb h r hrb α = 0 ↔
        normLimitValuation K L α.val ≤ WithZero.exp (-(r : ℤ)) := by
  intro α
  rw [normLimitHighBreakProjection_apply, Ideal.Quotient.eq_zero_iff_mem,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    normLimitValuation_eq_coordinate_of_fullUpper K L hb h]
  rfl

/-- Equality of original quotient coordinates is measured by the same original
valuation, at the exact requested precision. -/
theorem normLimitHighBreakProjection_eq_iff
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ α β : (normLimitFieldValuation K L).valuationSubring,
      normLimitHighBreakProjection K L hb h r hrb α =
        normLimitHighBreakProjection K L hb h r hrb β ↔
          normLimitValuation K L (α.val - β.val) ≤ WithZero.exp (-(r : ℤ)) := by
  intro α β
  rw [← sub_eq_zero, ← map_sub, normLimitHighBreakProjection_eq_zero_iff]
  rfl

/-- The kernel ideal is exactly the r-th maximal-ideal power in the original
norm-limit valuation ring, with its proved normalized valuation. -/
theorem ker_normLimitHighBreakProjection
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    RingHom.ker (normLimitHighBreakProjection K L hb h r hrb) =
      IsLocalRing.maximalIdeal
        (normLimitFieldValuation K L).valuationSubring ^ r := by
  ext α
  rw [RingHom.mem_ker, normLimitHighBreakProjection_eq_zero_iff,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    normLimitFieldValuation_eq_normalized K L]
  rfl

end Projections

end FontaineWintenberger
