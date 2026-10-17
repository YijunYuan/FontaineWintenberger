module

public import FontaineWintenberger.APF.Strict

/-!
# Bounded growth of the intrinsic APF index

A positive interval of the actual Herbrand integral gives a uniform lower
bound for the strictness ratio whenever the intrinsic index has bounded
growth across intervals of a fixed positive length. This implements
blueprint `fw:apf-bounded-index-growth` for an abstract separable extension.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A nonnegative interval of the actual Herbrand integral controls its
endpoint by the intrinsic index at the interval's left endpoint. -/
theorem IsAPF.window_mul_index_le_apfPsi (hL : IsAPF K L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (t - s) * (apfIndex K L s : ℝ) ≤ apfPsi K L t := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL 0 s)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL s t)
  change apfPsi K L s + _ = apfPsi K L t at hadd
  have hbound := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ ↦ apfHerbrandSlope K L s) volume s t)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL s t)
    (fun v hv ↦ IsAPF.monotone_apfHerbrandSlope K L hL hv.1)
  have hslope : apfHerbrandSlope K L s = (apfIndex K L s : ℝ) := by
    simp only [apfHerbrandSlope, max_eq_left hs]
  rw [intervalIntegral.integral_const, hslope, smul_eq_mul] at hbound
  linarith [IsAPF.le_apfPsi K L hL s]

/-- Bounded growth across an interval of fixed positive length gives the
actual strictness-ratio lower bound after an explicit finite cutoff. -/
theorem IsAPF.apfPsi_div_index_ge_of_boundedGrowth (hL : IsAPF K L)
    {ℓ C U v : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ))
    (hv : max (U + ℓ) ℓ ≤ v) :
    ℓ / C ≤ apfPsi K L v / (apfIndex K L v : ℝ) := by
  have hvℓ : ℓ ≤ v := (le_max_right _ _).trans hv
  have hs : 0 ≤ v - ℓ := by linarith
  have hsU : U ≤ v - ℓ := by linarith [(le_max_left (U + ℓ) ℓ).trans hv]
  have hwindow : ℓ * (apfIndex K L (v - ℓ) : ℝ) ≤ apfPsi K L v := by
    convert IsAPF.window_mul_index_le_apfPsi K L hL hs (by linarith : v - ℓ ≤ v) using 1
    ring
  have hg : (apfIndex K L v : ℝ) ≤ C * (apfIndex K L (v - ℓ) : ℝ) := by
    simpa only [sub_add_cancel] using hgrowth (v - ℓ) hsU
  have hapos : 0 < (apfIndex K L v : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K L hL (by linarith : 0 ≤ v))
  apply (div_le_div_iff₀ hC hapos).mpr
  calc
    ℓ * (apfIndex K L v : ℝ) ≤ ℓ * (C * (apfIndex K L (v - ℓ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hg hℓ.le
    _ = (ℓ * (apfIndex K L (v - ℓ) : ℝ)) * C := by ring
    _ ≤ apfPsi K L v * C := mul_le_mul_of_nonneg_right hwindow hC.le

/-- The source ratio has a positive constant eventual lower bound under
bounded growth of the actual intrinsic index. -/
theorem IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth (hL : IsAPF K L)
    {ℓ C U : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ)) :
    ∀ᶠ v in atTop, ENNReal.ofReal (ℓ / C) ≤ apfStrictnessRatio K L v := by
  apply eventually_atTop.mpr
  refine ⟨max (U + ℓ) ℓ, fun v hv ↦ ?_⟩
  exact ENNReal.ofReal_le_ofReal
    (IsAPF.apfPsi_div_index_ge_of_boundedGrowth K L hL hℓ hC hgrowth hv)

/-- Eventual bounded growth of the actual APF index implies strict APF for
an abstract separable extension, without any residue-field hypothesis. -/
theorem isStrictlyAPF_of_apfIndex_boundedGrowth (hL : IsAPF K L)
    {ℓ C U : ℝ} (hℓ : 0 < ℓ) (hC : 0 < C)
    (hgrowth : ∀ u : ℝ, U ≤ u →
      (apfIndex K L (u + ℓ) : ℝ) ≤ C * (apfIndex K L u : ℝ)) :
    IsStrictlyAPF K L := by
  have hlower : ENNReal.ofReal (ℓ / C) ≤ liminf (apfStrictnessRatio K L) atTop :=
    le_liminf_of_le (h :=
      IsAPF.eventually_le_apfStrictnessRatio_of_boundedGrowth K L hL hℓ hC hgrowth)
  exact ⟨hL, (ENNReal.ofReal_pos.mpr (div_pos hℓ hC)).trans_le hlower⟩

end FontaineWintenberger
