/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.AbstractFiniteBase
public import FontaineWintenberger.APF.FiniteStages
public import FontaineWintenberger.APF.Bound

/-!
# Cofinal growth of the actual relative first ramification bounds

The original finite-base closure homomorphism carries an actual stage
containment to a full relative APF product. Its actual Herbrand parameter
therefore bounds the extended first ramification bound from below. The
extended-real statement includes trivial finite steps.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger.AbstractFiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsCompleteDiscreteValuedField M]
    [NormedAlgebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)]
    [Algebra M (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]
variable (N : Type*) [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable M N]

/-- Containment of the actual finite-base fixing range in the old APF
product gives an actual extended relative first bound at the original
finite-base Herbrand parameter. -/
theorem apfPsi_le_apfRamificationBound_of_range_le
    (i : N →ₐ[M] SeparableClosure M) {u : ℝ} (hu : 0 ≤ u)
    (h : (closureHom K M).range ≤ apfSubgroup K (embedding K M i).fieldRange u) :
    (apfPsi K M u : EReal) ≤ apfRamificationBound M N := by
  have hu' : -1 ≤ u := by linarith
  have htop : (apfSubgroup K (embedding K M i).fieldRange u).comap
      (closureHom K M) = ⊤ := by
    apply top_unique
    intro g _
    exact h ⟨g, rfl⟩
  rw [comap_apf K M i hu'] at htop
  exact le_apfRamificationBound M N i
    (IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu') htop

end FontaineWintenberger.AbstractFiniteBase

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A genuine APF-stage containment gives the actual relative extended
first bound on the original finite fields and their canonical spectral norm. -/
theorem apfPsi_le_relativeFirstBound_of_apfFiniteStage_le
    (E F : FiniteLayer K L) (hEF : E ≤ F) (j : L →ₐ[K] SeparableClosure K)
    {u : ℝ} (hu : 0 ≤ u) (hstage : apfFiniteStage K j.fieldRange u ≤ E.val.map j) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
    (apfPsi K E.val u : EReal) ≤
      apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := normedAlgebra_residueField_perfectField K E.val
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  let jE := j.comp E.val.val
  let : Algebra E.val (SeparableClosure K) := jE.toRingHom.toAlgebra
  let : IsScalarTower K E.val (SeparableClosure K) := IsScalarTower.of_algHom jE
  let e := AbstractFiniteBase.closureEquiv K E.val
  let jF : F.val →ₐ[E.val] SeparableClosure K :=
    { (j.comp F.val.val).toRingHom with commutes' := fun _ => rfl }
  let i := e.symm.toAlgHom.comp jF
  have he : AbstractFiniteBase.embedding K E.val i = j.comp F.val.val := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply (jF x)
  have hr : (AbstractFiniteBase.closureHom K E.val).range = (E.val.map j).fixingSubgroup := by
    rw [AbstractFiniteBase.closureHom_range K E.val]
    have hjE : IsScalarTower.toAlgHom K E.val (SeparableClosure K) = jE := by
      ext x
      rfl
    rw [hjE, IntermediateField.fieldRange_comp_val]
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have hfix : (AbstractFiniteBase.closureHom K E.val).range ≤
      apfSubgroup K (AbstractFiniteBase.embedding K E.val i).fieldRange u := by
    rw [hr, he, IntermediateField.fieldRange_comp_val]
    exact ((IntermediateField.fixingSubgroup_le hstage).trans_eq
      (fixingSubgroup_apfFiniteStage K j.fieldRange u)).trans
        (sup_le_sup_right (IntermediateField.fixingSubgroup_le hFL) _)
  exact AbstractFiniteBase.apfPsi_le_apfRamificationBound_of_range_le K E.val F.val i hu hfix

/-- The actual relative first bounds become arbitrarily large on a genuine
finite-layer tail of the original abstract separable APF extension. Trivial
steps retain their extended bound `∞`. -/
theorem IsAPF.exists_finiteLayer_relativeFirstBound_ge (hL : IsAPF K L) (c : ℝ) :
    ∃ T : FiniteLayer K L, ∀ E F : FiniteLayer K L, T ≤ E → ∀ hEF : E ≤ F,
      letI := spectralNorm.nontriviallyNormedField K E.val
      letI := spectralNorm.normedAlgebra K E.val
      letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := E.val))
      letI := spectralNorm.completeSpace K E.val
      letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
      (c : EReal) ≤ apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := max c 0
  have hu : 0 ≤ u := le_max_right _ _
  obtain ⟨T, hT⟩ := exists_finiteLayer_map_eq_apfFiniteStage K L hL j
    (by linarith : -1 ≤ u)
  refine ⟨T, fun E F hTE hEF ↦ ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  have hstage : apfFiniteStage K j.fieldRange u ≤ E.val.map j := by
    rw [← hT]
    exact IntermediateField.map_mono j hTE
  have hb := apfPsi_le_relativeFirstBound_of_apfFiniteStage_le K L E F hEF j hu hstage
  have hpsi : c ≤ apfPsi K E.val u :=
    (le_max_left c 0).trans (IsAPF.le_apfPsi K E.val (isAPF_of_finite K E.val) u)
  exact (EReal.coe_le_coe_iff.mpr hpsi).trans hb

end FontaineWintenberger
