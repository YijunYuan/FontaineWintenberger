/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Index
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.Mathlib.FieldTheory.RelIndex
public import Mathlib.Order.Filter.ENNReal

/-!
# APF and strict APF under finite extension

## Strict APF descent through actual index factors

## APF under actual finite extension

The fixing-subgroup index is the actual field degree, even when the
intermediate fields have infinite degree over the original base.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M N : IntermediateField K (SeparableClosure K))

/-- The monotone actual tower factor bounds the whole integral up to the endpoint. -/
theorem apfPsi_le_towerIndexFactor_mul [IsAPF K N] (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfPsi K N u ≤ (apfTowerIndexFactor K M N u : ℝ) * apfPsi K M u := by
  have := IsAPF.of_algHom K (IntermediateField.inclusion hMN)
  have hmono := IsAPFSubextension.towerIndexFactor_monotoneOn K M N hMN
  have hbound := intervalIntegral.integral_mono_on hu
    (IsAPF.intervalIntegrable_apfHerbrandSlope K N 0 u)
    ((IsAPF.intervalIntegrable_apfHerbrandSlope K M 0 u).const_mul
      (apfTowerIndexFactor K M N u : ℝ)) (fun v hv => ?_)
  · simpa only [apfPsi, intervalIntegral.integral_const_mul] using hbound
  · simp only [apfHerbrandSlope, max_eq_left hv.1]
    rw [apfIndex_eq_mul_towerIndexFactor K M N hMN hv.1, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hmono hv.1 hu hv.2)) (Nat.cast_nonneg _)

/-- The source strictness ratio decreases when the extension field increases. -/
theorem apfStrictnessRatio_le_of_le [IsAPF K N] (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio K N u ≤ apfStrictnessRatio K M u := by
  have := IsAPF.of_algHom K (IntermediateField.inclusion hMN)
  have hapos : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hu)
  have hbpos : (0 : ℝ) < (apfIndex K N u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K N hu)
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hbpos hapos).mpr
  have hbound := apfPsi_le_towerIndexFactor_mul K M N hMN hu
  have heq : (apfIndex K N u : ℝ) =
      (apfIndex K M u : ℝ) * (apfTowerIndexFactor K M N u : ℝ) := by
    exact_mod_cast apfIndex_eq_mul_towerIndexFactor K M N hMN hu
  rw [heq]
  calc
    _ ≤ ((apfTowerIndexFactor K M N u : ℝ) * apfPsi K M u) * (apfIndex K M u : ℝ) :=
      mul_le_mul_of_nonneg_right hbound hapos.le
    _ = _ := by ring

/-- Strict APF descends to every actual subextension, without a normality assumption. -/
theorem IsStrictlyAPF.of_le [IsStrictlyAPF K N] (hMN : M ≤ N) :
    IsStrictlyAPF K M := by
  have := IsAPF.of_algHom K (IntermediateField.inclusion hMN)
  refine ⟨(IsStrictlyAPF.liminf_pos (K := K) (L := N)).trans_le ?_⟩
  exact liminf_le_liminf
    (eventually_atTop.mpr ⟨0, fun u hu => apfStrictnessRatio_le_of_le K M N hMN hu⟩)

/-- The extended ramification bound increases when the extension field decreases. -/
theorem apfRamificationBound_le_of_le (hMN : M ≤ N) :
    apfRamificationBound K N ≤ apfRamificationBound K M := by
  rw [apfRamificationBound_eq_embedding K N N.val,
    apfRamificationBound_eq_embedding K M M.val]
  apply sSup_le_sSup
  rintro x ⟨u, hu, htop, rfl⟩
  refine ⟨u, hu, ?_, rfl⟩
  simp only [IntermediateField.fieldRange_val] at htop ⊢
  have hle : apfSubgroup K N u ≤ apfSubgroup K M u :=
    sup_le_sup_right (IntermediateField.fixingSubgroup_le hMN) _
  exact top_unique (htop ▸ hle)

/-- The extended strictness constant increases on subextensions above a positive first bound. -/
theorem apfStrictnessConstant_le_of_le [IsAPF K N] (hMN : M ≤ N)
    (hi : (0 : EReal) < apfRamificationBound K N) :
    apfStrictnessConstant K N ≤ apfStrictnessConstant K M := by
  apply le_iInf
  intro u
  apply le_iInf
  intro hu
  have hNu : apfRamificationBound K N ≤ (u : EReal) :=
    (apfRamificationBound_le_of_le K M N hMN).trans hu
  have hu0 : 0 ≤ u := EReal.coe_nonneg.mp (hi.le.trans hNu)
  exact (apfStrictnessConstant_le K N hNu).trans
    (apfStrictnessRatio_le_of_le K M N hMN hu0)

section Abstract

variable {L P : Type*} [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]

/-- Strict APF descends along every algebra embedding of abstract separable extensions. -/
theorem IsStrictlyAPF.of_algHom [IsStrictlyAPF K L] (f : P →ₐ[K] L) :
    IsStrictlyAPF K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp f
  have hj : j.fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f y, hy⟩
  have hi := (isStrictlyAPF_algEquiv K L i.equivFieldRange).mp ‹_›
  exact (isStrictlyAPF_algEquiv K P j.equivFieldRange).mpr
    (IsStrictlyAPF.of_le K j.fieldRange i.fieldRange hj)

/-- The public extended first bound is monotone under every separable-extension embedding. -/
theorem apfRamificationBound_le_of_algHom (f : P →ₐ[K] L) :
    apfRamificationBound K L ≤ apfRamificationBound K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp f
  have hj : j.fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f y, hy⟩
  rw [apfRamificationBound_algEquiv K L i.equivFieldRange,
    apfRamificationBound_algEquiv K P j.equivFieldRange]
  exact apfRamificationBound_le_of_le K j.fieldRange i.fieldRange hj

/-- The public extended strictness constant is monotone above a positive first bound. -/
theorem apfStrictnessConstant_le_of_algHom [IsAPF K L] (f : P →ₐ[K] L)
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfStrictnessConstant K L ≤ apfStrictnessConstant K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp f
  have hj : j.fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f y, hy⟩
  have hi' : (0 : EReal) < apfRamificationBound K i.fieldRange := by
    rwa [← apfRamificationBound_algEquiv K L i.equivFieldRange]
  rw [apfStrictnessConstant_algEquiv K L i.equivFieldRange,
    apfStrictnessConstant_algEquiv K P j.equivFieldRange]
  have := (isAPF_algEquiv K i.equivFieldRange).mp ‹_›
  exact apfStrictnessConstant_le_of_le K j.fieldRange i.fieldRange hj hi'

end Abstract

end FontaineWintenberger

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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

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
theorem apfPsi_mono_extension [IsAPF K N] (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) : apfPsi K M u ≤ apfPsi K N u := by
  have := IsAPF.of_algHom K (IntermediateField.inclusion hMN)
  apply intervalIntegral.integral_mono_on hu
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M 0 u)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K N 0 u)
  intro v hv
  simp only [apfHerbrandSlope, max_eq_left hv.1]
  apply Nat.cast_le.mpr
  rw [apfIndex_eq_mul_towerIndexFactor K M N hMN hv.1]
  exact Nat.le_mul_of_pos_right _
    (IsAPFSubextension.towerIndexFactor_pos K M N hv.1)

/-- The finite inertia fixing index bounds the reverse strictness-ratio comparison. -/
theorem apfStrictnessRatio_le_finiteExtension_mul (hMN : M ≤ N)
    [FiniteDimensional M (IntermediateField.extendScalars hMN)] [IsAPF K N]
    {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio K M u ≤
      ((N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
        (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) : ℝ≥0∞) *
      apfStrictnessRatio K N u := by
  let C := (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
    (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
  have := IsAPF.of_algHom K (IntermediateField.inclusion hMN)
  have hapos : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hu)
  have hbpos : (0 : ℝ) < (apfIndex K N u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K N hu)
  have hpsi := apfPsi_mono_extension K M N hMN hu
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
      mul_le_mul_of_nonneg_left hfac (hu.trans (IsAPF.le_apfPsi K N u))
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
        ((isAPF_iff_subextension K M).mp hM.toIsAPF))
    refine ⟨?_⟩
    let C := (N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
    have hlim : liminf (apfStrictnessRatio K M) atTop ≤
        liminf (fun u => (C : ℝ≥0∞) * apfStrictnessRatio K N u) atTop :=
      liminf_le_liminf (eventually_atTop.mpr ⟨0, fun u hu =>
        apfStrictnessRatio_le_finiteExtension_mul K M N hMN hu⟩)
    rw [ENNReal.liminf_const_mul_of_ne_top (by simp : (C : ℝ≥0∞) ≠ ⊤)] at hlim
    by_contra! hzero
    have hz : liminf (apfStrictnessRatio K N) atTop = 0 := le_antisymm hzero bot_le
    rw [hz, mul_zero] at hlim
    exact (not_le_of_gt hM.liminf_pos) hlim

end Valued

section Abstract

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

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
