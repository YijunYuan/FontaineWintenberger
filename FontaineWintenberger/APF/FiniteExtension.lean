/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.StrictDescent
public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.FieldTheory.RelativeIndex
public import Mathlib.Order.Filter.ENNReal

/-!
# APF under actual finite extension

The fixing-subgroup index is the actual field degree, even when the
intermediate fields have infinite degree over the original base.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

section Embeddings

variable (K : Type*) [Field K]
variable {L P : Type*} [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra P L] [IsScalarTower K P L] [FiniteDimensional P L]

/-- Actual embedding images preserve finiteness over the actual image of the scalar field. -/
theorem finiteDimensional_fieldRange_extendScalars (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional (i.comp (IsScalarTower.toAlgHom K P L)).fieldRange
      (IntermediateField.extendScalars
        (show (i.comp (IsScalarTower.toAlgHom K P L)).fieldRange ≤ i.fieldRange from by
          rintro x ⟨y, rfl⟩
          exact ⟨algebraMap P L y, rfl⟩)) := by
  let j := i.comp (IsScalarTower.toAlgHom K P L)
  let σ := j.equivFieldRange.toRingEquiv.toRingHom
  let f : L →ₛₗ[σ] (IntermediateField.extendScalars
      (show j.fieldRange ≤ i.fieldRange from by
        rintro x ⟨y, rfl⟩
        exact ⟨algebraMap P L y, rfl⟩)) :=
    { toFun := fun x => ⟨i x, ⟨x, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (i.map_add x y)
      map_smul' := fun c x => Subtype.ext (by
        simp only [Algebra.smul_def]
        exact i.map_mul _ _) }
  exact Module.Finite.of_surjective f i.equivFieldRange.surjective

end Embeddings

section Valued

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (M N : IntermediateField K (SeparableClosure K))

/-- APF is unchanged by an actual finite extension above an arbitrary intermediate field. -/
theorem isAPFSubextension_finiteExtension_iff (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] :
    IsAPFSubextension K N ↔ IsAPFSubextension K M := by
  constructor
  · exact fun hN => hN.of_le K hMN
  · intro hM
    rw [isAPFSubextension_iff_finiteIndex] at hM ⊢
    intro u hu
    have hd := Nat.ne_of_gt (fixingSubgroup_relIndex_pos K M N hMN)
    have hprod : (apfSubgroup K N u).relIndex (apfSubgroup K M u) ≠ 0 := by
      rw [apfSubgroup, apfSubgroup, Subgroup.relIndex_sup_sup_normal]
      exact fun h => hd (Subgroup.relIndex_eq_zero_of_le_left le_sup_left h)
    have hm := Subgroup.finiteIndex_iff.mp (hM u hu)
    apply Subgroup.finiteIndex_iff.mpr
    have hle : apfSubgroup K N u ≤ apfSubgroup K M u :=
      sup_le_sup_right (IntermediateField.fixingSubgroup_le hMN) _
    rw [← Subgroup.relIndex_mul_index hle]
    exact Nat.mul_ne_zero hprod hm

/-- The actual intermediate inertia fixing index is positive for a finite extension. -/
theorem inertiaFixingRelIndex_pos (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] :
    0 < (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) :=
  Nat.pos_of_ne_zero (Subgroup.relIndex_inter_ne_zero
    (Nat.ne_of_gt (fixingSubgroup_relIndex_pos K M N hMN)) _)

/-- Finite extension gives a uniform finite upper bound for the actual tower factor. -/
theorem apfTowerIndexFactor_le_inertiaFixingRelIndex (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] (u : ℝ) :
    apfTowerIndexFactor K M N u ≤
      (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
        (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) := by
  rw [apfTowerIndexFactor_eq_inertiaRelIndex K M N hMN]
  exact Subgroup.relIndex_le_of_le_left le_sup_left
    (Nat.ne_of_gt (inertiaFixingRelIndex_pos K M N hMN))

/-- Nested APF indices give monotonicity of the actual Herbrand integral. -/
theorem apfPsi_mono_extension (hN : IsAPF K N) (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) : apfPsi K M u ≤ apfPsi K N u := by
  have hM := IsAPF.of_algHom K hN (IntermediateField.inclusion hMN)
  have hN' := (isAPF_iff_subextension K N).mp hN
  apply intervalIntegral.integral_mono_on hu
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M hM 0 u)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K N hN 0 u)
  intro v hv
  simp only [apfHerbrandSlope, max_eq_left hv.1]
  apply Nat.cast_le.mpr
  rw [apfIndex_eq_mul_towerIndexFactor K M N hMN hv.1]
  exact Nat.le_mul_of_pos_right _
    (IsAPFSubextension.towerIndexFactor_pos K M N hN' hv.1)

/-- The finite inertia fixing index bounds the reverse strictness-ratio comparison. -/
theorem apfStrictnessRatio_le_finiteExtension_mul (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] (hN : IsAPF K N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio K M u ≤
      ((N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
        (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) : ℝ≥0∞) *
      apfStrictnessRatio K N u := by
  let C := (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
    (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
  have hM := IsAPF.of_algHom K hN (IntermediateField.inclusion hMN)
  have hapos : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hM hu)
  have hbpos : (0 : ℝ) < (apfIndex K N u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K N hN hu)
  have hpsi := apfPsi_mono_extension K M N hN hMN hu
  have hfac : (apfIndex K N u : ℝ) ≤ (C : ℝ) * (apfIndex K M u : ℝ) := by
    rw [apfIndex_eq_mul_towerIndexFactor K M N hMN hu, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (apfTowerIndexFactor_le_inertiaFixingRelIndex K M N hMN u)) hapos.le
  change ENNReal.ofReal _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg C)]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hapos hbpos).mpr
  calc
    _ ≤ apfPsi K N u * (apfIndex K N u : ℝ) :=
      mul_le_mul_of_nonneg_right hpsi hbpos.le
    _ ≤ apfPsi K N u * ((C : ℝ) * (apfIndex K M u : ℝ)) :=
      mul_le_mul_of_nonneg_left hfac (hu.trans (IsAPF.le_apfPsi K N hN u))
    _ = _ := by ring

/-- Strict APF is unchanged by an actual finite extension, including nonnormal ones. -/
theorem isStrictlyAPF_finiteExtension_iff (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] :
    IsStrictlyAPF K N ↔ IsStrictlyAPF K M := by
  constructor
  · exact fun hN => hN.of_le K M N hMN
  · intro hM
    have hN : IsAPF K N := (isAPF_iff_subextension K N).mpr
      ((isAPFSubextension_finiteExtension_iff K M N hMN).mpr
        ((isAPF_iff_subextension K M).mp hM.1))
    refine ⟨hN, ?_⟩
    let C := (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
    have hlim : liminf (apfStrictnessRatio K M) atTop ≤
        liminf (fun u => (C : ℝ≥0∞) * apfStrictnessRatio K N u) atTop :=
      liminf_le_liminf (eventually_atTop.mpr ⟨0, fun u hu =>
        apfStrictnessRatio_le_finiteExtension_mul K M N hMN hN hu⟩)
    rw [ENNReal.liminf_const_mul_of_ne_top (by simp : (C : ℝ≥0∞) ≠ ⊤)] at hlim
    by_contra! hzero
    have hz : liminf (apfStrictnessRatio K N) atTop = 0 := le_antisymm hzero bot_le
    rw [hz, mul_zero] at hlim
    exact (not_le_of_gt hM.2) hlim

end Valued

section Abstract

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L P : Type*) [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]
    [Algebra P L] [IsScalarTower K P L] [FiniteDimensional P L]

/-- APF is unchanged by finite extension of arbitrary abstract separable fields. -/
theorem isAPF_finite_extension_iff : IsAPF K L ↔ IsAPF K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp (IsScalarTower.toAlgHom K P L)
  have hMN : j.fieldRange ≤ i.fieldRange := by
    rintro x ⟨y, rfl⟩
    exact ⟨algebraMap P L y, rfl⟩
  have : FiniteDimensional j.fieldRange (IntermediateField.extendScalars hMN) :=
    finiteDimensional_fieldRange_extendScalars K i
  rw [isAPF_algEquiv K i.equivFieldRange, isAPF_algEquiv K j.equivFieldRange,
    isAPF_iff_subextension, isAPF_iff_subextension]
  exact isAPFSubextension_finiteExtension_iff K j.fieldRange i.fieldRange hMN

/-- Strict APF is unchanged by finite extension of arbitrary abstract separable fields. -/
theorem isStrictlyAPF_finite_extension_iff :
    IsStrictlyAPF K L ↔ IsStrictlyAPF K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp (IsScalarTower.toAlgHom K P L)
  have hMN : j.fieldRange ≤ i.fieldRange := by
    rintro x ⟨y, rfl⟩
    exact ⟨algebraMap P L y, rfl⟩
  have : FiniteDimensional j.fieldRange (IntermediateField.extendScalars hMN) :=
    finiteDimensional_fieldRange_extendScalars K i
  rw [isStrictlyAPF_algEquiv K L i.equivFieldRange,
    isStrictlyAPF_algEquiv K P j.equivFieldRange]
  exact isStrictlyAPF_finiteExtension_iff K j.fieldRange i.fieldRange hMN

end Abstract

end FontaineWintenberger
