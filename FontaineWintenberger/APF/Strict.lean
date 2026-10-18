/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.APF.Bound
public import Mathlib.Order.LiminfLimsup

/-!
# Strict APF and the extended strictness constant

The lower limit and infimum use nonnegative extended reals. In particular the
empty tail at an infinite ramification bound has infimum infinity. This case
is proved directly from the actual upper groups and their intrinsic indices.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

theorem apfSubgroup_eq_top_of_bound_eq_top (h : apfRamificationBound K L = ⊤)
    (i : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K i.fieldRange u = ⊤ := by
  have hlt : (u : EReal) < apfRamificationBound K L := by rw [h]; exact EReal.coe_lt_top u
  rw [apfRamificationBound_eq_embedding K L i] at hlt
  obtain ⟨x, ⟨v, hv, htop, rfl⟩, huv⟩ := lt_sSup_iff.mp hlt
  apply top_unique
  rw [← htop]
  exact apfSubgroup_antitoneOn K i.fieldRange hu hv (EReal.coe_lt_coe_iff.mp huv).le

theorem isAPF_of_bound_eq_top (h : apfRamificationBound K L = ⊤) : IsAPF K L := by
  intro i u hu
  simpa only [apfSubgroup_eq_top_of_bound_eq_top K L h i hu, Subgroup.coe_top] using
    (isOpen_univ : IsOpen (Set.univ : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)))

theorem apfIndex_eq_one_of_bound_eq_top (h : apfRamificationBound K L = ⊤)
    {u : ℝ} (hu : 0 ≤ u) : apfIndex K L u = 1 := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfIndex_eq_embedding K L i, apfInertiaIndex, apfInertiaSubgroup_eq_inf K _ u hu,
    apfSubgroup_eq_top_of_bound_eq_top K L h i (by linarith), top_inf_eq,
    Subgroup.relIndex_self]

theorem apfPsi_eq_self_of_bound_eq_top (h : apfRamificationBound K L = ⊤) (u : ℝ) :
    apfPsi K L u = u := by
  have hs : apfHerbrandSlope K L = fun _ ↦ (1 : ℝ) := by
    funext v
    simp only [apfHerbrandSlope, apfIndex_eq_one_of_bound_eq_top K L h (le_max_right v 0),
      Nat.cast_one]
  simp only [apfPsi, hs, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

theorem apfPhi_eq_self_of_bound_eq_top (h : apfRamificationBound K L = ⊤)
    (hL : IsAPF K L) (u : ℝ) : apfPhi K L hL u = u := by
  simpa only [apfPsi_eq_self_of_bound_eq_top K L h] using apfPhi_apfPsi K L hL u

/-- The source ratio, embedded in the nonnegative extended reals. -/
noncomputable def apfStrictnessRatio (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (apfPsi K L u / (apfIndex K L u : ℝ))

/-- The source strictness constant, with the empty infimum equal to infinity. -/
noncomputable def apfStrictnessConstant : ℝ≥0∞ :=
  ⨅ u : ℝ, ⨅ (_ : apfRamificationBound K L ≤ (u : EReal)), apfStrictnessRatio K L u

/-- Strict arithmetic profiniteness of an abstract separable extension. -/
def IsStrictlyAPF : Prop :=
  IsAPF K L ∧ 0 < liminf (apfStrictnessRatio K L) atTop

theorem apfStrictnessConstant_le {u : ℝ} (hu : apfRamificationBound K L ≤ (u : EReal)) :
    apfStrictnessConstant K L ≤ apfStrictnessRatio K L u :=
  iInf_le_of_le u (iInf_le _ hu)

theorem apfStrictnessConstant_of_bound_eq_top (h : apfRamificationBound K L = ⊤) :
    apfStrictnessConstant K L = ⊤ := by
  apply top_unique
  apply le_iInf
  intro u
  apply le_iInf
  intro hu
  have hu' : (⊤ : EReal) ≤ (u : EReal) := h ▸ hu
  exact False.elim ((not_le_of_gt (EReal.coe_lt_top u)) hu')

theorem isStrictlyAPF_of_bound_eq_top (h : apfRamificationBound K L = ⊤) :
    IsStrictlyAPF K L := by
  refine ⟨isAPF_of_bound_eq_top K L h, ?_⟩
  have hlower : (1 : ℝ≥0∞) ≤ liminf (apfStrictnessRatio K L) atTop := by
    refine le_liminf_of_le (h := ?_)
    apply eventually_atTop.mpr
    refine ⟨1, fun u hu ↦ ?_⟩
    rw [apfStrictnessRatio, apfPsi_eq_self_of_bound_eq_top K L h,
      apfIndex_eq_one_of_bound_eq_top K L h (by linarith : 0 ≤ u), Nat.cast_one, div_one]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hu
  exact lt_of_lt_of_le (by norm_num) hlower

theorem isStrictlyAPF_self : IsStrictlyAPF K K :=
  isStrictlyAPF_of_bound_eq_top K K (apfRamificationBound_self K)

@[simp]
theorem apfStrictnessConstant_self : apfStrictnessConstant K K = ⊤ :=
  apfStrictnessConstant_of_bound_eq_top K K (apfRamificationBound_self K)

theorem apfStrictnessRatio_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) (u : ℝ) :
    apfStrictnessRatio K L u = apfStrictnessRatio K M u := by
  rw [apfStrictnessRatio, apfStrictnessRatio, apfPsi_algEquiv K L e,
    apfIndex_algEquiv K L e]

theorem apfStrictnessConstant_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    apfStrictnessConstant K L = apfStrictnessConstant K M := by
  simp only [apfStrictnessConstant, apfRamificationBound_algEquiv K L e,
    apfStrictnessRatio_algEquiv K L e]

theorem isStrictlyAPF_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    IsStrictlyAPF K L ↔ IsStrictlyAPF K M := by
  simp only [IsStrictlyAPF, isAPF_algEquiv K e,
    funext (apfStrictnessRatio_algEquiv K L e)]

end FontaineWintenberger
