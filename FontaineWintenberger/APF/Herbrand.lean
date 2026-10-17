module

public import FontaineWintenberger.APF.IndexTransport
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The intrinsic APF Herbrand functions

The positive finite inertia indices define the source integral. Extending its
slope by one below zero gives a primitive on the real line; its actual order
isomorphism supplies the inverse. On the source half-line both functions have
the prescribed normalization.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The intrinsic index, extended by one on the negative half-line. -/
noncomputable def apfHerbrandSlope (u : ℝ) : ℝ :=
  apfIndex K L (max u 0)

theorem apfHerbrandSlope_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    apfHerbrandSlope K L u = 1 := by
  simp only [apfHerbrandSlope, max_eq_right hu, apfIndex_zero, Nat.cast_one]

theorem IsAPF.one_le_apfHerbrandSlope (hL : IsAPF K L) (u : ℝ) :
    1 ≤ apfHerbrandSlope K L u := by
  change (1 : ℝ) ≤ (apfIndex K L (max u 0) : ℝ)
  exact_mod_cast (IsAPF.apfIndex_pos K L hL (le_max_right u 0))

theorem IsAPF.monotone_apfHerbrandSlope (hL : IsAPF K L) :
    Monotone (apfHerbrandSlope K L) := by
  intro u v huv
  exact Nat.cast_le.mpr (IsAPF.apfIndex_monotoneOn K L hL
    (le_max_right u 0) (le_max_right v 0) (max_le_max huv le_rfl))

theorem IsAPF.intervalIntegrable_apfHerbrandSlope (hL : IsAPF K L) (a b : ℝ) :
    IntervalIntegrable (apfHerbrandSlope K L) volume a b :=
  (IsAPF.monotone_apfHerbrandSlope K L hL).intervalIntegrable

/-- The source inverse Herbrand integral, with its identity continuation below zero. -/
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

theorem IsAPF.continuous_apfPsi (hL : IsAPF K L) : Continuous (apfPsi K L) :=
  intervalIntegral.continuous_primitive (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL) 0

theorem IsAPF.apfPsi_sub_ge (hL : IsAPF K L) {s t : ℝ} (hst : s ≤ t) :
    t - s ≤ apfPsi K L t - apfPsi K L s := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL 0 s)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL s t)
  have hbound := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume s t)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L hL s t)
    (fun v _ ↦ IsAPF.one_le_apfHerbrandSlope K L hL v)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hbound
  change apfPsi K L s + _ = apfPsi K L t at hadd
  linarith

theorem IsAPF.strictMono_apfPsi (hL : IsAPF K L) : StrictMono (apfPsi K L) := by
  intro s t hst
  have h := IsAPF.apfPsi_sub_ge K L hL hst.le
  linarith

theorem IsAPF.le_apfPsi (hL : IsAPF K L) (u : ℝ) : u ≤ apfPsi K L u := by
  by_cases hu : u ≤ 0
  · exact (apfPsi_of_nonpos K L hu).ge
  · have h := IsAPF.apfPsi_sub_ge K L hL (le_of_not_ge hu)
    simpa only [apfPsi_zero, sub_zero] using h

theorem IsAPF.surjective_apfPsi (hL : IsAPF K L) : Function.Surjective (apfPsi K L) := by
  intro u
  apply intermediate_value_univ (min u 0) (max u 0) (IsAPF.continuous_apfPsi K L hL)
  constructor
  · rw [apfPsi_of_nonpos K L (min_le_right u 0)]
    exact min_le_left u 0
  · exact (le_max_left u 0).trans (IsAPF.le_apfPsi K L hL (max u 0))

/-- The order isomorphism is obtained from strict monotonicity and actual surjectivity. -/
noncomputable def apfHerbrandOrderIso (hL : IsAPF K L) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (apfPsi K L) (IsAPF.strictMono_apfPsi K L hL)
    (IsAPF.surjective_apfPsi K L hL)

@[simp]
theorem apfHerbrandOrderIso_apply (hL : IsAPF K L) (u : ℝ) :
    apfHerbrandOrderIso K L hL u = apfPsi K L u := rfl

/-- The actual inverse of the APF Herbrand integral. -/
noncomputable def apfPhi (hL : IsAPF K L) (u : ℝ) : ℝ :=
  (apfHerbrandOrderIso K L hL).symm u

@[simp]
theorem apfPsi_apfPhi (hL : IsAPF K L) (u : ℝ) :
    apfPsi K L (apfPhi K L hL u) = u :=
  (apfHerbrandOrderIso K L hL).apply_symm_apply u

@[simp]
theorem apfPhi_apfPsi (hL : IsAPF K L) (u : ℝ) :
    apfPhi K L hL (apfPsi K L u) = u :=
  (apfHerbrandOrderIso K L hL).symm_apply_apply u

theorem apfPhi_of_nonpos (hL : IsAPF K L) {u : ℝ} (hu : u ≤ 0) :
    apfPhi K L hL u = u := by
  simpa only [apfPsi_of_nonpos K L hu] using apfPhi_apfPsi K L hL u

theorem continuous_apfPhi (hL : IsAPF K L) : Continuous (apfPhi K L hL) :=
  (apfHerbrandOrderIso K L hL).symm.toHomeomorph.continuous

theorem strictMono_apfPhi (hL : IsAPF K L) : StrictMono (apfPhi K L hL) :=
  (apfHerbrandOrderIso K L hL).symm.strictMono

theorem IsAPF.apfPsi_mem_Ici (hL : IsAPF K L) {u : ℝ} (hu : -1 ≤ u) :
    -1 ≤ apfPsi K L u := by
  have h := (IsAPF.strictMono_apfPsi K L hL).monotone hu
  simpa only [apfPsi_of_nonpos K L (by norm_num : (-1 : ℝ) ≤ 0)] using h

theorem apfPhi_mem_Ici (hL : IsAPF K L) {u : ℝ} (hu : -1 ≤ u) :
    -1 ≤ apfPhi K L hL u := by
  have h := (strictMono_apfPhi K L hL).monotone hu
  simpa only [apfPhi_of_nonpos K L hL (by norm_num : (-1 : ℝ) ≤ 0)] using h

theorem apfPsi_algEquiv {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]
    (e : L ≃ₐ[K] M) (u : ℝ) : apfPsi K L u = apfPsi K M u := by
  unfold apfPsi
  apply intervalIntegral.integral_congr
  intro v _
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) (apfIndex_algEquiv K L e (max v 0))

theorem apfPhi_algEquiv {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]
    (e : L ≃ₐ[K] M) (hL : IsAPF K L) (hM : IsAPF K M) (u : ℝ) :
    apfPhi K L hL u = apfPhi K M hM u := by
  apply (IsAPF.strictMono_apfPsi K M hM).injective
  rw [← apfPsi_algEquiv K L e, apfPsi_apfPhi, apfPsi_apfPhi]

end FontaineWintenberger
