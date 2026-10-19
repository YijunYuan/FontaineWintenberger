/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.APF.RamificationBound
public import Mathlib.Order.LiminfLimsup

/-!
# Strictly APF extensions

## Strict APF and the extended strictness constant

The lower limit and infimum use nonnegative extended reals. In particular the
empty tail at an infinite ramification bound has infimum infinity. This case
is proved directly from the upper groups and their intrinsic indices.

## Positivity of the intrinsic APF strictness constant

A positive finite first bound controls every bounded interval, because the
APF index is positive and monotone. A positive lower limit controls
the remaining tail. The infinite first bound uses its proved empty-infimum case.

## Bounded growth of the intrinsic APF index

A positive interval of the Herbrand integral gives an uniform lower
bound for the strictness ratio whenever the intrinsic index has bounded
growth across intervals of a fixed positive length. This implements
blueprint `fw:apf-bounded-index-growth` for an abstract separable extension.

## Main definitions

* `apfStrictnessRatio`: The ratio, embedded in the nonnegative extended reals.
* `apfStrictnessConstant`: The strictness constant, with the empty infimum equal to infinity.
* `IsStrictlyAPF`: Strict arithmetic profiniteness of an abstract separable extension (Wintenberger
  1.2.1): APF, and the ratio `ψ_{L/K}(u) / (G_K^0 : G_L^0 G_K^u)` stays bounded below as `u → ∞`.

## Main results

* `isStrictlyAPF_iff_constant_pos`: The positivity criterion, including the infinite first-bound
  endpoint.
* `IsAPF.window_mul_index_le_apfPsi`: A nonnegative interval of the Herbrand integral controls its
  endpoint by the intrinsic index at the interval's left endpoint.
* `IsAPF.apfPsi_div_index_ge_of_boundedGrowth`: Bounded growth across an interval of fixed positive
  length gives the strictness-ratio lower bound after an explicit finite cutoff.
* `IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth`: The ratio has a positive constant
  eventual lower bound under bounded growth of the intrinsic index.
* `isStrictlyAPF_of_apfIndex_boundedGrowth`: Eventual bounded growth of the APF index implies strict
  APF for an abstract separable extension, without any residue-field hypothesis.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
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
  refine ⟨fun i => ⟨fun u hu => ?_⟩⟩
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
    [IsAPF K L] (u : ℝ) : apfPhi K L u = u := by
  simpa only [apfPsi_eq_self_of_bound_eq_top K L h] using apfPhi_apfPsi K L u

/-- The ratio, embedded in the nonnegative extended reals. -/
noncomputable def apfStrictnessRatio (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (apfPsi K L u / (apfIndex K L u : ℝ))

/-- The strictness constant, with the empty infimum equal to infinity. -/
noncomputable def apfStrictnessConstant : ℝ≥0∞ :=
  ⨅ u : ℝ, ⨅ (_ : apfRamificationBound K L ≤ (u : EReal)), apfStrictnessRatio K L u

/-- Strict arithmetic profiniteness of an abstract separable extension (Wintenberger 1.2.1):
APF, and the ratio `ψ_{L/K}(u) / (G_K^0 : G_L^0 G_K^u)` stays bounded below as `u → ∞`. -/
class IsStrictlyAPF : Prop extends IsAPF K L where
  liminf_pos : 0 < liminf (apfStrictnessRatio K L) atTop

theorem isStrictlyAPF_iff :
    IsStrictlyAPF K L ↔ IsAPF K L ∧ 0 < liminf (apfStrictnessRatio K L) atTop :=
  ⟨fun h => ⟨h.toIsAPF, h.liminf_pos⟩, fun h => { toIsAPF := h.1, liminf_pos := h.2 }⟩

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
  have := isAPF_of_bound_eq_top K L h
  refine ⟨?_⟩
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
  simp only [isStrictlyAPF_iff, isAPF_algEquiv K e,
    funext (apfStrictnessRatio_algEquiv K L e)]

end FontaineWintenberger

namespace FontaineWintenberger

open Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

theorem isStrictlyAPF_of_constant_pos_of_bound_eq_coe [IsAPF K L]
    {b : ℝ} (hb : apfRamificationBound K L = (b : EReal))
    (hc : 0 < apfStrictnessConstant K L) : IsStrictlyAPF K L := by
  refine ⟨hc.trans_le ?_⟩
  refine le_liminf_of_le (h := ?_)
  apply eventually_atTop.mpr
  refine ⟨b, fun u hu ↦ apfStrictnessConstant_le K L ?_⟩
  rw [hb]
  exact EReal.coe_le_coe_iff.mpr hu

theorem IsStrictlyAPF.constant_pos_of_bound_eq_coe [IsStrictlyAPF K L]
    {b : ℝ} (hb : apfRamificationBound K L = (b : EReal)) (hbpos : 0 < b) :
    0 < apfStrictnessConstant K L := by
  obtain ⟨ε, hεpos, hεlim⟩ := exists_between (IsStrictlyAPF.liminf_pos (K := K) (L := L))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hεlim)
  let T := max T₀ b
  have hTnonneg : 0 ≤ T := hbpos.le.trans (le_max_right T₀ b)
  have hapos : (0 : ℝ) < (apfIndex K L T : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L hTnonneg)
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
      Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L hunonneg)
    have ha_le : (apfIndex K L u : ℝ) ≤ (apfIndex K L T : ℝ) :=
      Nat.cast_le.mpr (IsAPF.apfIndex_monotoneOn K L hunonneg hTnonneg huT)
    have hbound : b / (apfIndex K L T : ℝ) ≤ apfPsi K L u / (apfIndex K L u : ℝ) :=
      (div_le_div_of_nonneg_left hbpos.le hau ha_le).trans
        ((div_le_div_iff_of_pos_right hau).mpr (hbu.trans (IsAPF.le_apfPsi K L u)))
    exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal hbound)
  · exact (min_le_left _ _).trans (hT₀ u ((le_max_left T₀ b).trans (le_of_not_ge huT))).le

/-- The positivity criterion, including the infinite first-bound endpoint. -/
theorem isStrictlyAPF_iff_constant_pos [IsAPF K L]
    (hi : (0 : EReal) < apfRamificationBound K L) :
    IsStrictlyAPF K L ↔ 0 < apfStrictnessConstant K L := by
  generalize hb : apfRamificationBound K L = b at hi
  cases b using EReal.rec with
  | bot => simp at hi
  | coe b =>
    exact ⟨fun h ↦ haveI := h;
        IsStrictlyAPF.constant_pos_of_bound_eq_coe K L hb (EReal.coe_pos.mp hi),
      fun hc ↦ isStrictlyAPF_of_constant_pos_of_bound_eq_coe K L hb hc⟩
  | top =>
    exact iff_of_true (isStrictlyAPF_of_bound_eq_top K L hb)
      (by rw [apfStrictnessConstant_of_bound_eq_top K L hb]; simp)

end FontaineWintenberger

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A nonnegative interval of the Herbrand integral controls its
endpoint by the intrinsic index at the interval's left endpoint. -/
theorem IsAPF.window_mul_index_le_apfPsi [IsAPF K L]
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (t - s) * (apfIndex K L s : ℝ) ≤ apfPsi K L t := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 s)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L s t)
  change apfPsi K L s + _ = apfPsi K L t at hadd
  have hbound := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ ↦ apfHerbrandSlope K L s) volume s t)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L s t)
    (fun v hv ↦ IsAPF.monotone_apfHerbrandSlope K L hv.1)
  have hslope : apfHerbrandSlope K L s = (apfIndex K L s : ℝ) := by
    simp only [apfHerbrandSlope, max_eq_left hs]
  rw [intervalIntegral.integral_const, hslope, smul_eq_mul] at hbound
  linarith [IsAPF.le_apfPsi K L s]

/-- Bounded growth across an interval of fixed positive length gives the
strictness-ratio lower bound after an explicit finite cutoff. -/
theorem IsAPF.apfPsi_div_index_ge_of_boundedGrowth [IsAPF K L]
    {ℓ C U v : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ))
    (hv : max (U + ℓ) ℓ ≤ v) :
    ℓ / C ≤ apfPsi K L v / (apfIndex K L v : ℝ) := by
  have hvℓ : ℓ ≤ v := (le_max_right _ _).trans hv
  have hs : 0 ≤ v - ℓ := by linarith
  have hsU : U ≤ v - ℓ := by linarith [(le_max_left (U + ℓ) ℓ).trans hv]
  have hwindow : ℓ * (apfIndex K L (v - ℓ) : ℝ) ≤ apfPsi K L v := by
    convert IsAPF.window_mul_index_le_apfPsi K L hs (by linarith : v - ℓ ≤ v) using 1
    ring
  have hg : (apfIndex K L v : ℝ) ≤ C * (apfIndex K L (v - ℓ) : ℝ) := by
    simpa only [sub_add_cancel] using hgrowth (v - ℓ) hsU
  have hapos : 0 < (apfIndex K L v : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L (by linarith : 0 ≤ v))
  apply (div_le_div_iff₀ hC hapos).mpr
  calc
    ℓ * (apfIndex K L v : ℝ) ≤ ℓ * (C * (apfIndex K L (v - ℓ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hg hℓ.le
    _ = (ℓ * (apfIndex K L (v - ℓ) : ℝ)) * C := by ring
    _ ≤ apfPsi K L v * C := mul_le_mul_of_nonneg_right hwindow hC.le

/-- The ratio has a positive constant eventual lower bound under
bounded growth of the intrinsic index. -/
theorem IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth [IsAPF K L]
    {ℓ C U : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ)) :
    ∀ᶠ v in atTop, ENNReal.ofReal (ℓ / C) ≤ apfStrictnessRatio K L v := by
  apply eventually_atTop.mpr
  refine ⟨max (U + ℓ) ℓ, fun v hv ↦ ?_⟩
  exact ENNReal.ofReal_le_ofReal
    (IsAPF.apfPsi_div_index_ge_of_boundedGrowth K L hℓ hC hgrowth hv)

/-- Eventual bounded growth of the APF index implies strict APF for
an abstract separable extension, without any residue-field hypothesis. -/
theorem isStrictlyAPF_of_apfIndex_boundedGrowth [IsAPF K L]
    {ℓ C U : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ)) :
    IsStrictlyAPF K L := by
  have hlower : ENNReal.ofReal (ℓ / C) ≤ liminf (apfStrictnessRatio K L) atTop :=
    le_liminf_of_le (h :=
      IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth K L hℓ hC hgrowth)
  exact ⟨(ENNReal.ofReal_pos.mpr (div_pos hℓ hC)).trans_le hlower⟩

end FontaineWintenberger
