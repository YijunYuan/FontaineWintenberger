/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Upper.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# The inverse Herbrand integral

The derivative of the proved inverse is the reciprocal of the
lower-cardinality slope. Lagrange's formula identifies this ratio with
the relative index of the upper groups.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

/-- The upper subgroup relative index is the cardinality ratio. -/
theorem upperRamificationGroup_relIndex_eq_div {u : ℝ} (hu : 0 ≤ u) :
    ((upperRamificationGroup (R := R) G u).relIndex
      (upperRamificationGroup (R := R) G 0) : ℝ) =
      (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) /
        Nat.card (upperRamificationGroup (R := R) G u) := by
  have hle := upperRamificationGroup_antitoneOn (R := R) G
    (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
  have h := (upperRamificationGroup (R := R) G u).relIndex_mul_card
    (upperRamificationGroup (R := R) G 0)
  rw [inf_eq_left.mpr hle] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Nat.card_pos.ne')).mpr
  simpa only [Nat.cast_mul, upperRamificationGroup_zero, lowerRamificationGroup_zero] using
    congrArg (fun n : ℕ => (n : ℝ)) h

theorem intervalIntegrable_inverseHerbrand_slope {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun v : ℝ =>
      (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) /
        Nat.card (upperRamificationGroup (R := R) G v)) volume 0 u := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hu]
  intro v hv w hw hvw
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr Nat.card_pos)
  apply Nat.cast_le.mpr
  have hle := upperRamificationGroup_antitoneOn (R := R) G
    (by linarith [hv.1] : -1 ≤ v) (by linarith [hw.1] : -1 ≤ w) hvw
  exact Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)

/-- Inverting the derivative leaves only finitely many exceptional upper parameters. -/
theorem exists_inverseHerbrandFunction_finite_derivative_breaks [FaithfulSMul G R] :
    ∃ S : Finset ℝ, ∀ u : ℝ, 0 < u → u ∉ S →
      HasDerivAt (inverseHerbrandFunction (R := R) G)
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) /
          Nat.card (upperRamificationGroup (R := R) G u)) u := by
  classical
  obtain ⟨S, hS⟩ := exists_herbrandFunction_finite_derivative_breaks (R := R) G
  refine ⟨S.image (herbrandFunction (R := R) G), ?_⟩
  intro u hu hnot
  have hpos : 0 < inverseHerbrandFunction (R := R) G u := by
    have h := strictMonoOn_inverseHerbrandFunction (R := R) G
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
    simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl] using h
  have hnot' : inverseHerbrandFunction (R := R) G u ∉ S := by
    intro h
    exact hnot (Finset.mem_image.mpr ⟨_, h,
      herbrandFunction_inverseHerbrandFunction G (by linarith)⟩)
  have hderiv := HasDerivAt.of_local_left_inverse
    (continuous_inverseHerbrandFunction (R := R) G).continuousAt (hS _ hpos hnot')
    (div_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')) (by
        filter_upwards [Ioi_mem_nhds (by linarith : (-1 : ℝ) < u)] with v hv
        exact herbrandFunction_inverseHerbrandFunction G hv.le)
  simpa only [inv_div, upperRamificationGroup] using hderiv

/-- The inverse is the integral of the reciprocal lower-cardinality slope. -/
theorem inverseHerbrandFunction_eq_integral_div [FaithfulSMul G R] {u : ℝ} (hu : 0 ≤ u) :
    inverseHerbrandFunction (R := R) G u =
      ∫ v in (0 : ℝ)..u,
        (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) /
          Nat.card (upperRamificationGroup (R := R) G v) := by
  obtain ⟨S, hS⟩ := exists_inverseHerbrandFunction_finite_derivative_breaks (R := R) G
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (inverseHerbrandFunction (R := R) G) _ hu S.countable_toSet
    (continuous_inverseHerbrandFunction (R := R) G).continuousOn
    (fun v hv => hS v hv.1.1 hv.2) (intervalIntegrable_inverseHerbrand_slope G hu)
  simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl, sub_zero] using h.symm

/-- The inverse integral uses the relative indices of upper subgroups. -/
theorem inverseHerbrandFunction_eq_integral_relIndex [FaithfulSMul G R] {u : ℝ}
    (hu : 0 ≤ u) :
    inverseHerbrandFunction (R := R) G u =
      ∫ v in (0 : ℝ)..u,
        ((upperRamificationGroup (R := R) G v).relIndex
          (upperRamificationGroup (R := R) G 0) : ℝ) := by
  rw [inverseHerbrandFunction_eq_integral_div G hu]
  apply intervalIntegral.integral_congr
  rw [Set.uIcc_of_le hu]
  intro v hv
  exact (upperRamificationGroup_relIndex_eq_div G hv.1).symm

end FontaineWintenberger
