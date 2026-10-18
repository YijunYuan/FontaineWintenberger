/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.IndexTower
public import FontaineWintenberger.APF.Strict

/-!
# Strict APF descent through actual index factors
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M N : IntermediateField K (SeparableClosure K))

/-- The monotone actual tower factor bounds the whole integral up to the endpoint. -/
theorem apfPsi_le_towerIndexFactor_mul (hN : IsAPF K N) (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfPsi K N u ≤ (apfTowerIndexFactor K M N u : ℝ) * apfPsi K M u := by
  have hM := IsAPF.of_algHom K hN (IntermediateField.inclusion hMN)
  have hN' := (isAPF_iff_subextension K N).mp hN
  have hmono := IsAPFSubextension.towerIndexFactor_monotoneOn K M N hN' hMN
  have hbound := intervalIntegral.integral_mono_on hu
    (IsAPF.intervalIntegrable_apfHerbrandSlope K N hN 0 u)
    ((IsAPF.intervalIntegrable_apfHerbrandSlope K M hM 0 u).const_mul
      (apfTowerIndexFactor K M N u : ℝ)) (fun v hv => ?_)
  · simpa only [apfPsi, intervalIntegral.integral_const_mul] using hbound
  · simp only [apfHerbrandSlope, max_eq_left hv.1]
    rw [apfIndex_eq_mul_towerIndexFactor K M N hMN hv.1, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hmono hv.1 hu hv.2)) (Nat.cast_nonneg _)

/-- The source strictness ratio decreases when the extension field increases. -/
theorem apfStrictnessRatio_le_of_le (hN : IsAPF K N) (hMN : M ≤ N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio K N u ≤ apfStrictnessRatio K M u := by
  have hM := IsAPF.of_algHom K hN (IntermediateField.inclusion hMN)
  have hapos : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hM hu)
  have hbpos : (0 : ℝ) < (apfIndex K N u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K N hN hu)
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hbpos hapos).mpr
  have hbound := apfPsi_le_towerIndexFactor_mul K M N hN hMN hu
  have heq : (apfIndex K N u : ℝ) =
      (apfIndex K M u : ℝ) * (apfTowerIndexFactor K M N u : ℝ) := by
    exact_mod_cast apfIndex_eq_mul_towerIndexFactor K M N hMN hu
  rw [heq]
  calc
    _ ≤ ((apfTowerIndexFactor K M N u : ℝ) * apfPsi K M u) * (apfIndex K M u : ℝ) :=
      mul_le_mul_of_nonneg_right hbound hapos.le
    _ = _ := by ring

/-- Strict APF descends to every actual subextension, without a normality assumption. -/
theorem IsStrictlyAPF.of_le (hN : IsStrictlyAPF K N) (hMN : M ≤ N) :
    IsStrictlyAPF K M := by
  refine ⟨IsAPF.of_algHom K hN.1 (IntermediateField.inclusion hMN), hN.2.trans_le ?_⟩
  exact liminf_le_liminf
    (eventually_atTop.mpr ⟨0, fun u hu => apfStrictnessRatio_le_of_le K M N hN.1 hMN hu⟩)

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
theorem apfStrictnessConstant_le_of_le (hN : IsAPF K N) (hMN : M ≤ N)
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
    (apfStrictnessRatio_le_of_le K M N hN hMN hu0)

section Abstract

variable {L P : Type*} [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]

/-- Strict APF descends along every algebra embedding of abstract separable extensions. -/
theorem IsStrictlyAPF.of_algHom (hL : IsStrictlyAPF K L) (f : P →ₐ[K] L) :
    IsStrictlyAPF K P := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  let j := i.comp f
  have hj : j.fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f y, hy⟩
  have hi := (isStrictlyAPF_algEquiv K L i.equivFieldRange).mp hL
  exact (isStrictlyAPF_algEquiv K P j.equivFieldRange).mpr
    (IsStrictlyAPF.of_le K j.fieldRange i.fieldRange hi hj)

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
theorem apfStrictnessConstant_le_of_algHom (hL : IsAPF K L) (f : P →ₐ[K] L)
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
  exact apfStrictnessConstant_le_of_le K j.fieldRange i.fieldRange
    ((isAPF_algEquiv K i.equivFieldRange).mp hL) hj hi'

end Abstract

end FontaineWintenberger
