module

public import FontaineWintenberger.APF.Herbrand
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Finite APF indices stabilize and their actual integral is eventually affine
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- Actual inertia has positive finite index relative to the finite-base fixing subgroup. -/
theorem fixingSubgroup_inertiaRelIndex_pos :
    0 < M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0) := by
  have hindex : M.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) M]
    exact Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K M)
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := Subgroup.relIndex_eq_zero_of_le_right
    (show absoluteUpperRamificationGroup K 0 ≤ ⊤ from le_top) hzero
  exact hindex (by simpa only [Subgroup.relIndex_top_right] using h)

/-- The actual finite-base inertia fixing index bounds every nonnegative APF index. -/
theorem apfIndex_le_fixingSubgroup_inertiaRelIndex (u : ℝ) :
    apfIndex K M u ≤ M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0) := by
  rw [apfIndex_eq_embedding K M M.val, IntermediateField.fieldRange_val, apfInertiaIndex]
  have hnonzero :
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
        (absoluteUpperRamificationGroup K 0) ≠ 0 := by
    simpa only [Subgroup.inf_relIndex_right] using
      Nat.ne_of_gt (fixingSubgroup_inertiaRelIndex_pos K M)
  change ((M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
    absoluteUpperRamificationGroup K u).relIndex (absoluteUpperRamificationGroup K 0) ≤ _
  have hle : M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0 ≤
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
        absoluteUpperRamificationGroup K u := le_sup_left
  have h := Subgroup.relIndex_le_of_le_left hle hnonzero
  simpa only [Subgroup.inf_relIndex_right] using h

/-- Monotonicity and a genuine finite upper bound force the finite-base index to stabilize. -/
theorem exists_apfIndex_finite_constant :
    ∃ C : ℕ, 0 < C ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, b ≤ u → apfIndex K M u = C := by
  let f : ℝ → ℕ := fun u => apfIndex K M (max u 0)
  have hbound : BddAbove (Set.range f) := by
    refine ⟨M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0), ?_⟩
    rintro x ⟨u, rfl⟩
    exact apfIndex_le_fixingSubgroup_inertiaRelIndex K M (max u 0)
  obtain ⟨C, ⟨⟨a, ha⟩, hmax⟩⟩ :=
    hbound.exists_isGreatest_of_nonempty (show (Set.range f).Nonempty from ⟨f 0, 0, rfl⟩)
  have hM := isAPF_of_finite K M
  refine ⟨C, ?_, max a 0, le_max_right a 0, ?_⟩
  · rw [← ha]
    exact IsAPF.apfIndex_pos K M hM (le_max_right a 0)
  · intro u hu
    have hu0 : 0 ≤ u := (le_max_right a 0).trans hu
    apply le_antisymm
    · simpa only [f, max_eq_left hu0] using hmax (show f u ∈ Set.range f from ⟨u, rfl⟩)
    · rw [← ha]
      exact IsAPF.apfIndex_monotoneOn K M hM (le_max_right a 0) hu0 hu

/-- The actual finite-base Herbrand integral is affine on a genuine eventual constant-index tail. -/
theorem exists_apfPsi_finite_affine :
    ∃ C : ℕ, 0 < C ∧ ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, b ≤ u → apfIndex K M u = C) ∧
      ∀ u : ℝ, b ≤ u → apfPsi K M u = apfPsi K M b + (C : ℝ) * (u - b) := by
  obtain ⟨C, hC, b, hb, hidx⟩ := exists_apfIndex_finite_constant K M
  refine ⟨C, hC, b, hb, hidx, ?_⟩
  intro u hu
  have hi : (∫ v in b..u, apfHerbrandSlope K M v) = (u - b) * (C : ℝ) := by
    calc
      _ = ∫ _v in b..u, (C : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hu]
        intro v hv
        simp only [apfHerbrandSlope, max_eq_left (hb.trans hv.1), hidx v hv.1]
      _ = _ := by simp
  have hM := isAPF_of_finite K M
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M hM 0 b)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M hM b u)
  change apfPsi K M b + (∫ v in b..u, apfHerbrandSlope K M v) = apfPsi K M u at hadd
  rw [hi] at hadd
  exact hadd.symm.trans (by ring)

end FontaineWintenberger
