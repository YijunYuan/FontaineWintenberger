/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Infinite.Restriction

/-!
# Restricting infinite upper groups to an abstract finite Galois extension

The finite extension is given by an algebra in a scalar tower, rather than by a particular
intermediate-field carrier. Its image in the ambient extension reduces the comparison to
ordinary finite Galois restriction.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K Ω E : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω] [Field E] [Algebra K E] [Algebra E Ω]
    [IsScalarTower K E Ω] [FiniteDimensional K E] [IsGalois K E]

private def finiteGaloisScalarImage : FiniteGaloisIntermediateField K Ω := by
  let j := IsScalarTower.toAlgHom K E Ω
  let := Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  let := IsGalois.of_algEquiv j.equivFieldRange
  exact .mk j.fieldRange

private def finiteGaloisScalarImageEquiv : E ≃ₐ[K] finiteGaloisScalarImage K Ω E :=
  (IsScalarTower.toAlgHom K E Ω).equivFieldRange

omit [IsCompleteDiscreteValuedField K] in
private theorem restrictNormal_finiteGaloisScalarImage (σ : Ω ≃ₐ[K] Ω) :
    σ.restrictNormal (finiteGaloisScalarImage K Ω E) =
      (finiteGaloisScalarImageEquiv K Ω E).autCongr (σ.restrictNormal E) := by
  let e := finiteGaloisScalarImageEquiv K Ω E
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  apply Subtype.ext
  change (σ.restrictNormal (finiteGaloisScalarImage K Ω E) (e y) : Ω) =
    (e ((σ.restrictNormal E) (e.symm (e y))) : Ω)
  rw [e.symm_apply_apply]
  exact (AlgEquiv.restrictNormal_commutes σ (finiteGaloisScalarImage K Ω E) (e y)).trans
    (AlgEquiv.restrictNormal_commutes σ E y).symm

/-- Infinite upper ramification restricts to the upper group of every abstract finite
Galois subextension, using that subextension's spectral integer ring. -/
theorem restrictNormal_mem_upperRamificationGroup_of_finite
    {u : ℝ} (hu : -1 ≤ u) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ upperRamificationGroupInfinite K Ω u) :
    σ.restrictNormal E ∈ upperRamificationGroup (R := spectralIntegerRing K E)
      (E ≃ₐ[K] E) u := by
  have h := (mem_upperRamificationGroupInfinite K Ω u σ).mp hσ
    (finiteGaloisScalarImage K Ω E)
  rw [restrictNormal_finiteGaloisScalarImage,
    ← upperRamificationGroup_map_autCongr K (finiteGaloisScalarImageEquiv K Ω E) hu,
    Subgroup.mem_map_equiv] at h
  simpa only [MulEquiv.symm_apply_apply] using h

variable [IsGalois K Ω] [PerfectField 𝓀[K]]

/-- Every upper automorphism of an abstract finite Galois subextension lifts to the
ambient infinite upper group. -/
theorem exists_lift_upperRamificationGroup_of_finite
    {u : ℝ} (hu : -1 ≤ u) (σ : E ≃ₐ[K] E)
    (hσ : σ ∈ upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u) :
    ∃ τ ∈ upperRamificationGroupInfinite K Ω u, τ.restrictNormal E = σ := by
  let e := finiteGaloisScalarImageEquiv K Ω E
  have h : e.autCongr σ ∈ upperRamificationGroup
      (R := spectralIntegerRing K (finiteGaloisScalarImage K Ω E))
        ((finiteGaloisScalarImage K Ω E) ≃ₐ[K] (finiteGaloisScalarImage K Ω E)) u := by
    rw [← upperRamificationGroup_map_autCongr K e hu]
    exact Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτ, he⟩ := exists_lift_upperRamificationGroupInfinite K Ω
    (finiteGaloisScalarImage K Ω E) u hu (e.autCongr σ) h
  refine ⟨τ, hτ, e.autCongr.injective ?_⟩
  exact (restrictNormal_finiteGaloisScalarImage K Ω E τ).symm.trans he

/-- Ordinary restriction onto an abstract finite Galois extension maps upper groups onto
upper groups. -/
theorem restrictNormalHom_map_upperRamificationGroup_of_finite
    {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K Ω u).map (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact restrictNormal_mem_upperRamificationGroup_of_finite K Ω E hu σ hσ
  · intro σ hσ
    obtain ⟨τ, hτ, he⟩ := exists_lift_upperRamificationGroup_of_finite K Ω E hu σ hσ
    exact Subgroup.mem_map.mpr ⟨τ, hτ, he⟩

end FontaineWintenberger
