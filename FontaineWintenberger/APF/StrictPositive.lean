/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Strict

/-!
# Positivity of the intrinsic APF strictness constant

A positive finite first bound controls every bounded interval, because the
actual APF index is positive and monotone. A positive lower limit controls
the remaining tail. The infinite first bound uses its proved empty-infimum case.
-/

@[expose] public section

namespace FontaineWintenberger

open Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

theorem isStrictlyAPF_of_constant_pos_of_bound_eq_coe (hL : IsAPF K L)
    {b : ℝ} (hb : apfRamificationBound K L = (b : EReal))
    (hc : 0 < apfStrictnessConstant K L) : IsStrictlyAPF K L := by
  refine ⟨hL, hc.trans_le ?_⟩
  refine le_liminf_of_le (h := ?_)
  apply eventually_atTop.mpr
  refine ⟨b, fun u hu ↦ apfStrictnessConstant_le K L ?_⟩
  rw [hb]
  exact EReal.coe_le_coe_iff.mpr hu

theorem IsStrictlyAPF.constant_pos_of_bound_eq_coe (hL : IsStrictlyAPF K L)
    {b : ℝ} (hb : apfRamificationBound K L = (b : EReal)) (hbpos : 0 < b) :
    0 < apfStrictnessConstant K L := by
  obtain ⟨ε, hεpos, hεlim⟩ := exists_between hL.2
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hεlim)
  let T := max T₀ b
  have hTnonneg : 0 ≤ T := hbpos.le.trans (le_max_right T₀ b)
  have hapos : (0 : ℝ) < (apfIndex K L T : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L hL.1 hTnonneg)
  have hpositive : 0 < min ε (ENNReal.ofReal (b / (apfIndex K L T : ℝ))) :=
    lt_min hεpos (ENNReal.ofReal_pos.mpr (div_pos hbpos hapos))
  apply hpositive.trans_le
  apply le_iInf
  intro u
  apply le_iInf
  intro hu
  have hbu : b ≤ u := EReal.coe_le_coe_iff.mp (hb ▸ hu)
  have hunonneg : 0 ≤ u := hbpos.le.trans hbu
  by_cases huT : u ≤ T
  · have hau : (0 : ℝ) < (apfIndex K L u : ℝ) :=
      Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L hL.1 hunonneg)
    have ha_le : (apfIndex K L u : ℝ) ≤ (apfIndex K L T : ℝ) :=
      Nat.cast_le.mpr (IsAPF.apfIndex_monotoneOn K L hL.1 hunonneg hTnonneg huT)
    have hbound : b / (apfIndex K L T : ℝ) ≤ apfPsi K L u / (apfIndex K L u : ℝ) :=
      (div_le_div_of_nonneg_left hbpos.le hau ha_le).trans
        ((div_le_div_iff_of_pos_right hau).mpr (hbu.trans (IsAPF.le_apfPsi K L hL.1 u)))
    exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal hbound)
  · exact (min_le_left _ _).trans (hT₀ u ((le_max_left T₀ b).trans (le_of_not_ge huT))).le

/-- The source positivity criterion, including the infinite first-bound endpoint. -/
theorem isStrictlyAPF_iff_constant_pos (hL : IsAPF K L)
    (hi : (0 : EReal) < apfRamificationBound K L) :
    IsStrictlyAPF K L ↔ 0 < apfStrictnessConstant K L := by
  generalize hb : apfRamificationBound K L = b at hi
  cases b using EReal.rec with
  | bot => simp at hi
  | coe b =>
    exact ⟨fun h ↦ IsStrictlyAPF.constant_pos_of_bound_eq_coe K L h hb (EReal.coe_pos.mp hi),
      fun hc ↦ isStrictlyAPF_of_constant_pos_of_bound_eq_coe K L hL hb hc⟩
  | top =>
    exact iff_of_true (isStrictlyAPF_of_bound_eq_top K L hb)
      (by rw [apfStrictnessConstant_of_bound_eq_top K L hb]; simp)

end FontaineWintenberger
