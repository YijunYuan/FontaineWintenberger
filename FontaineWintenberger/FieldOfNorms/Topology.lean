/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Integral
public import FontaineWintenberger.LocalField.NormedTower
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of actual finite norms and ideal-power topology

The determinant of the original multiplication matrix is continuous over
the complete finite-dimensional base. Discrete ideal powers are actual balls.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section NormContinuity

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
variable (E F : Type*) [NormedField E] [NormedField F]
    [NormedAlgebra K E] [NormedAlgebra K F] [Algebra E F]
    [IsScalarTower K E F] [FiniteDimensional K F]

include K

/-- The actual relative field norm is continuous for the original compatible
norms, by the finite multiplication matrix over the complete base. -/
theorem continuous_algebraNorm_of_finiteDimensional :
    Continuous (Algebra.norm E : F → E) := by
  have : FiniteDimensional E F := Module.Finite.right K E F
  let b := Module.finBasis E F
  have hmat : Continuous (Algebra.leftMulMatrix b : F →
      Matrix (Fin (Module.finrank E F)) (Fin (Module.finrank E F)) E) :=
    ((Algebra.leftMulMatrix b).toLinearMap.restrictScalars K).continuous_of_finiteDimensional
  simpa only [← Algebra.norm_eq_matrix_det b] using hmat.matrix_det

end NormContinuity

section FiniteLayers

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Continuity of the same original finite-layer norm, with the canonical
spectral norms on the original two finite fields. -/
theorem FiniteLayer.continuous_norm (E F : FiniteLayer K L) (hEF : E ≤ F) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.nontriviallyNormedField K F.val
    Continuous (norm E F hEF : F.val → E.val) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K F.val
  let := spectralNorm.normedAlgebra K E.val
  let := spectralNorm.normedAlgebra K F.val
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  exact continuous_algebraNorm_of_finiteDimensional K E.val F.val

end FiniteLayers

section IdealPowers

variable (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := E))
variable [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]

/-- An actual uniformizer of the norm unit ball has norm strictly between
zero and one. -/
theorem norm_uniformizer_pos_lt_one (π : R) (hπ : Irreducible π) :
    0 < ‖(π : E)‖ ∧ ‖(π : E)‖ < 1 := by
  have hmem : π ∈ IsLocalRing.maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hlt := (Valuation.mem_maximalIdeal_iff E (NormedField.valuation (K := E))).mp hmem
  refine ⟨norm_pos_iff.mpr (fun h => hπ.ne_zero (Subtype.ext h)), ?_⟩
  exact_mod_cast hlt

/-- The canonical norm topology identifies an actual ideal power with
the corresponding uniformizer-radius closed ball, including exponent zero. -/
theorem mem_maximalIdeal_pow_iff_norm_le (π : R) (hπ : Irreducible π)
    (x : R) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖(x : E)‖ ≤ ‖(π : E)‖ ^ n := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hπ₀ : (π : E) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  constructor
  · rintro ⟨y, rfl⟩
    change ‖(π : E) ^ n * (y : E)‖ ≤ ‖(π : E)‖ ^ n
    rw [norm_mul, norm_pow]
    apply mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _)
    exact_mod_cast y.property
  · intro hx
    have hy : ‖(x : E) / (π : E) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (pow_pos (norm_pos_iff.mpr hπ₀) n)]
      exact hx
    let y : R := ⟨(x : E) / (π : E) ^ n, by exact_mod_cast hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change (x : E) = (π : E) ^ n * ((x : E) / (π : E) ^ n)
    field_simp

/-- The image of the actual ideal power in its original field is exactly
the corresponding closed norm ball. -/
theorem image_maximalIdeal_pow_eq_closedBall (π : R) (hπ : Irreducible π) (n : ℕ) :
    (fun x : R => (x : E)) '' ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) =
      Metric.closedBall (0 : E) (‖(π : E)‖ ^ n) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (mem_maximalIdeal_pow_iff_norm_le E π hπ y n).mp hy
  · intro hx
    have hx' : ‖x‖ ≤ ‖(π : E)‖ ^ n := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hx1 : ‖x‖ ≤ 1 := hx'.trans
      (pow_le_one₀ (norm_nonneg _) (norm_uniformizer_pos_lt_one E π hπ).2.le)
    let y : R := ⟨x, by exact_mod_cast hx1⟩
    exact ⟨y, (mem_maximalIdeal_pow_iff_norm_le E π hπ y n).mpr hx', rfl⟩

/-- Every actual ideal power has closed image in the original field. -/
theorem isClosed_image_maximalIdeal_pow (n : ℕ) :
    IsClosed ((fun x : R => (x : E)) ''
      ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [image_maximalIdeal_pow_eq_closedBall E π hπ]
  exact Metric.isClosed_closedBall

/-- The original discrete ideal powers form a neighborhood basis at zero
for the original field norm. -/
theorem nhds_zero_hasBasis_maximalIdeal_pow :
    (nhds (0 : E)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun x : R => (x : E)) ''
        ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  simp_rw [image_maximalIdeal_pow_eq_closedBall E π hπ]
  exact Metric.nhds_basis_closedBall_pow
    (norm_uniformizer_pos_lt_one E π hπ).1 (norm_uniformizer_pos_lt_one E π hπ).2

/-- Closed actual ideal powers are complete inside the original complete
field; no residue-field compactness is used. -/
theorem isComplete_image_maximalIdeal_pow [CompleteSpace E] (n : ℕ) :
    IsComplete ((fun x : R => (x : E)) ''
      ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) :=
  (isClosed_image_maximalIdeal_pow E n).isComplete

end IdealPowers

section SpectralIdealPowers

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Actual spectral ideal powers have closed image for the canonical norm
on the original finite field. -/
theorem FiniteLayer.isClosed_image_maximalIdeal_pow (E : FiniteLayer K L) (n : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    IsClosed ((fun x : spectralIntegerRing K E.val => (x : E.val)) ''
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
        Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val))) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
  exact FontaineWintenberger.isClosed_image_maximalIdeal_pow E.val n

/-- The original spectral ideal powers give the actual field topology at
zero for every actual finite layer. -/
theorem FiniteLayer.nhds_zero_hasBasis_maximalIdeal_pow (E : FiniteLayer K L) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    (nhds (0 : E.val)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
          Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val))) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
  exact FontaineWintenberger.nhds_zero_hasBasis_maximalIdeal_pow E.val

end SpectralIdealPowers

end FontaineWintenberger
