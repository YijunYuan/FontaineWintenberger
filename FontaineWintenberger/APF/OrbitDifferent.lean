/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.FiniteNonnormal
public import FontaineWintenberger.Ramification.OrbitDifferent

/-!
# Intrinsic APF indices of prime-degree nonnormal extensions

The finite upper orbit index equals the actual intrinsic APF inertia index
with its residue-degree factor. The actual different therefore determines
the full intrinsic profile of a totally ramified prime-degree subextension.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (Valuation.valuationSubring (NormedField.valuation (K := K)))]
variable [PerfectField (IsLocalRing.ResidueField
    (Valuation.valuationSubring (NormedField.valuation (K := K))))]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
variable (M : IntermediateField K E)

local notation "H" => M.fixingSubgroup
local notation "U" => upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E)

/-- The actual finite upper orbit index retains the zero-index residue factor. -/
theorem finite_upperOrbitIndex_eq_zeroIndex_mul_apfIndex {u : ℝ} (hu : 0 ≤ u) :
    (H ⊔ U u).index = (H ⊔ U 0).index * apfIndex K M u := by
  rw [apfIndex_eq_subgroupRelIndex K E M hu]
  simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
    upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex
      (R := spectralIntegerRing K E) (E ≃ₐ[K] E) H hu

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => Valuation.valuationSubring (Valuation.comap (algebraMap M E)
    (spectralValuation K E))

/-- The actual different determines the intrinsic APF profile of every
prime-degree totally ramified intermediate field; normality is not required. -/
theorem apfIndex_prime_degree_different_profile_of_finiteGaloisIntermediateField
    (hp : (Module.finrank K M).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K M) :
    letI := intermediate_spectral_isDiscreteValuationRing K E M
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K M u = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) := by
  have := intermediate_spectral_isDiscreteValuationRing K E M
  have hfinite : ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → (H ⊔ U u).index = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) :=
    intermediate_spectral_prime_degree_different_profile K E M hp he
  obtain ⟨b, hb, hprofile, hd⟩ := hfinite
  have hz : (H ⊔ U 0).index = 1 := by
    simpa only [ite_eq_left hb] using hprofile 0 le_rfl
  refine ⟨b, hb, ?_, hd⟩
  intro u hu
  have hfactor := finite_upperOrbitIndex_eq_zeroIndex_mul_apfIndex K E M hu
  rw [hz, one_mul] at hfactor
  rw [← hfactor]
  exact hprofile u hu

end FontaineWintenberger
