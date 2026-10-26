/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Index
public import FontaineWintenberger.LocalField.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The intrinsic APF Herbrand functions

The positive finite inertia indices define the integral. Extending its
slope by one below zero gives a primitive on the real line; its order
isomorphism supplies the inverse. On the half-line both functions have
the prescribed normalization.

## Main definitions

* `apfHerbrandSlope`: The intrinsic index, extended by one on the negative half-line.
* `apfPsi`: The inverse Herbrand integral, with its identity continuation below zero.
* `apfHerbrandOrderIso`: The order isomorphism is obtained from strict monotonicity and
  surjectivity.
* `apfPhi`: The inverse of the APF Herbrand integral.

## Main results

* `apfHerbrandSlope_of_nonpos`
* `IsAPF.one_le_apfHerbrandSlope`
* `IsAPF.monotone_apfHerbrandSlope`
* `IsAPF.intervalIntegrable_apfHerbrandSlope`
* `apfPsi_of_nonpos`
* `apfPsi_zero`
* `apfPsi_eq_integral_index`
* `IsAPF.continuous_apfPsi`

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The intrinsic index, extended by one on the negative half-line. -/
noncomputable def apfHerbrandSlope (u : ℝ) : ℝ :=
  apfIndex K L (max u 0)

theorem apfHerbrandSlope_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    apfHerbrandSlope K L u = 1 := by
  simp only [apfHerbrandSlope, max_eq_right hu, apfIndex_zero, Nat.cast_one]

theorem IsAPF.one_le_apfHerbrandSlope [IsAPF K L] (u : ℝ) :
    1 ≤ apfHerbrandSlope K L u := by
  change (1 : ℝ) ≤ (apfIndex K L (max u 0) : ℝ)
  exact_mod_cast (IsAPF.apfIndex_pos K L (le_max_right u 0))

theorem IsAPF.monotone_apfHerbrandSlope [IsAPF K L] :
    Monotone (apfHerbrandSlope K L) := by
  intro u v huv
  exact Nat.cast_le.mpr (IsAPF.apfIndex_monotoneOn K L
    (le_max_right u 0) (le_max_right v 0) (max_le_max huv le_rfl))

theorem IsAPF.intervalIntegrable_apfHerbrandSlope [IsAPF K L] (a b : ℝ) :
    IntervalIntegrable (apfHerbrandSlope K L) volume a b :=
  (IsAPF.monotone_apfHerbrandSlope K L).intervalIntegrable

/-- The inverse Herbrand integral, with its identity continuation below zero. -/
noncomputable def apfPsi (u : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..u, apfHerbrandSlope K L v

theorem apfPsi_of_nonpos {u : ℝ} (hu : u ≤ 0) : apfPsi K L u = u := by
  have h : apfPsi K L u = ∫ v in (0 : ℝ)..u, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_ge hu]
    exact fun v hv ↦ apfHerbrandSlope_of_nonpos K L hv.2
  simpa using h

@[simp]
theorem apfPsi_zero : apfPsi K L 0 = 0 := apfPsi_of_nonpos K L le_rfl

theorem apfPsi_eq_integral_index {u : ℝ} (hu : 0 ≤ u) :
    apfPsi K L u = ∫ v in (0 : ℝ)..u, (apfIndex K L v : ℝ) := by
  apply intervalIntegral.integral_congr
  rw [Set.uIcc_of_le hu]
  intro v hv
  simp only [apfHerbrandSlope, max_eq_left hv.1]

theorem IsAPF.continuous_apfPsi [IsAPF K L] : Continuous (apfPsi K L) :=
  intervalIntegral.continuous_primitive (IsAPF.intervalIntegrable_apfHerbrandSlope K L) 0

theorem IsAPF.apfPsi_sub_ge [IsAPF K L] {s t : ℝ} (hst : s ≤ t) :
    t - s ≤ apfPsi K L t - apfPsi K L s := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 s)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L s t)
  have hbound := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume s t)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L s t)
    (fun v _ ↦ IsAPF.one_le_apfHerbrandSlope K L v)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hbound
  change apfPsi K L s + _ = apfPsi K L t at hadd
  linarith

theorem IsAPF.strictMono_apfPsi [IsAPF K L] : StrictMono (apfPsi K L) := by
  intro s t hst
  have h := IsAPF.apfPsi_sub_ge K L hst.le
  linarith

theorem IsAPF.le_apfPsi [IsAPF K L] (u : ℝ) : u ≤ apfPsi K L u := by
  by_cases hu : u ≤ 0
  · exact (apfPsi_of_nonpos K L hu).ge
  · have h := IsAPF.apfPsi_sub_ge K L (le_of_not_ge hu)
    simpa only [apfPsi_zero, sub_zero] using h

theorem IsAPF.surjective_apfPsi [IsAPF K L] : Function.Surjective (apfPsi K L) := by
  intro u
  apply intermediate_value_univ (min u 0) (max u 0) (IsAPF.continuous_apfPsi K L)
  constructor
  · rw [apfPsi_of_nonpos K L (min_le_right u 0)]
    exact min_le_left u 0
  · exact (le_max_left u 0).trans (IsAPF.le_apfPsi K L (max u 0))

/-- The inverse Herbrand function `apfPsi K L` as an order isomorphism of the real line. -/
noncomputable def apfHerbrandOrderIso [IsAPF K L] : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (apfPsi K L) (IsAPF.strictMono_apfPsi K L)
    (IsAPF.surjective_apfPsi K L)

@[simp]
theorem apfHerbrandOrderIso_apply [IsAPF K L] (u : ℝ) :
    apfHerbrandOrderIso K L u = apfPsi K L u := rfl

/-- The inverse of the APF Herbrand integral. -/
noncomputable def apfPhi [IsAPF K L] (u : ℝ) : ℝ :=
  (apfHerbrandOrderIso K L).symm u

@[simp]
theorem apfPsi_apfPhi [IsAPF K L] (u : ℝ) :
    apfPsi K L (apfPhi K L u) = u :=
  (apfHerbrandOrderIso K L).apply_symm_apply u

@[simp]
theorem apfPhi_apfPsi [IsAPF K L] (u : ℝ) :
    apfPhi K L (apfPsi K L u) = u :=
  (apfHerbrandOrderIso K L).symm_apply_apply u

theorem apfPhi_of_nonpos [IsAPF K L] {u : ℝ} (hu : u ≤ 0) :
    apfPhi K L u = u := by
  simpa only [apfPsi_of_nonpos K L hu] using apfPhi_apfPsi K L u

theorem continuous_apfPhi [IsAPF K L] : Continuous (apfPhi K L) :=
  (apfHerbrandOrderIso K L).symm.toHomeomorph.continuous

theorem strictMono_apfPhi [IsAPF K L] : StrictMono (apfPhi K L) :=
  (apfHerbrandOrderIso K L).symm.strictMono

theorem IsAPF.apfPsi_mem_Ici [IsAPF K L] {u : ℝ} (hu : -1 ≤ u) :
    -1 ≤ apfPsi K L u := by
  have h := (IsAPF.strictMono_apfPsi K L).monotone hu
  simpa only [apfPsi_of_nonpos K L (by norm_num : (-1 : ℝ) ≤ 0)] using h

theorem apfPhi_mem_Ici [IsAPF K L] {u : ℝ} (hu : -1 ≤ u) :
    -1 ≤ apfPhi K L u := by
  have h := (strictMono_apfPhi K L).monotone hu
  simpa only [apfPhi_of_nonpos K L (by norm_num : (-1 : ℝ) ≤ 0)] using h

theorem apfPsi_algEquiv {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]
    (e : L ≃ₐ[K] M) (u : ℝ) : apfPsi K L u = apfPsi K M u := by
  unfold apfPsi
  apply intervalIntegral.integral_congr
  intro v _
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) (apfIndex_algEquiv K L e (max v 0))

theorem apfPhi_algEquiv {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]
    (e : L ≃ₐ[K] M) [IsAPF K L] [IsAPF K M] (u : ℝ) :
    apfPhi K L u = apfPhi K M u := by
  apply (IsAPF.strictMono_apfPsi K M).injective
  rw [← apfPsi_algEquiv K L e, apfPsi_apfPhi, apfPsi_apfPhi]

end FontaineWintenberger
