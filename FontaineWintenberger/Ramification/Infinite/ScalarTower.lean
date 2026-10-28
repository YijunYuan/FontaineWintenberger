/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Infinite.Restriction

/-!
# Infinite upper ramification in an abstract scalar tower

Restriction onto a Galois subextension preserves upper groups even when the subextension
is represented by an abstract field rather than an intermediate-field carrier.
-/

@[expose] public section

noncomputable section

namespace AlgEquiv

variable (K C M Ω : Type*) [Field K] [Field C] [Field M] [Field Ω]
    [Algebra K C] [Algebra K M] [Algebra K Ω] [Algebra C M] [Algebra C Ω] [Algebra M Ω]
    [IsScalarTower K C M] [IsScalarTower K C Ω] [IsScalarTower K M Ω]
    [IsScalarTower C M Ω] [Normal K M] [Normal C M]

/-- Normal restriction commutes with restriction of the base scalars. -/
theorem restrictNormal_restrictScalars (σ : Ω ≃ₐ[C] Ω) :
    (σ.restrictScalars K).restrictNormal M = (σ.restrictNormal M).restrictScalars K := by
  ext x
  apply (algebraMap M Ω).injective
  exact (restrictNormal_commutes (σ.restrictScalars K) M x).trans
    (restrictNormal_commutes σ M x).symm

end AlgEquiv

namespace FontaineWintenberger

variable (K Ω M : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω] [Field M] [Algebra K M] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsGalois K M]

omit [IsCompleteDiscreteValuedField K] in
private theorem restrictNormal_scalarImage (σ : Ω ≃ₐ[K] Ω) :
    let j := IsScalarTower.toAlgHom K M Ω
    letI := IsGalois.of_algEquiv j.equivFieldRange
    σ.restrictNormal j.fieldRange = j.equivFieldRange.autCongr (σ.restrictNormal M) := by
  let j := IsScalarTower.toAlgHom K M Ω
  let := IsGalois.of_algEquiv j.equivFieldRange
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := j.equivFieldRange.surjective x
  apply Subtype.ext
  change (σ.restrictNormal j.fieldRange (j.equivFieldRange y) : Ω) =
    (j.equivFieldRange ((σ.restrictNormal M)
      (j.equivFieldRange.symm (j.equivFieldRange y))) : Ω)
  rw [j.equivFieldRange.symm_apply_apply]
  exact (AlgEquiv.restrictNormal_commutes σ j.fieldRange (j.equivFieldRange y)).trans
    (AlgEquiv.restrictNormal_commutes σ M y).symm

/-- Restriction in an abstract scalar tower carries infinite upper groups into the
corresponding upper groups of the Galois subextension. -/
theorem restrictNormal_mem_upperRamificationGroupInfinite_tower
    {u : ℝ} (hu : -1 ≤ u) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ upperRamificationGroupInfinite K Ω u) :
    σ.restrictNormal M ∈ upperRamificationGroupInfinite K M u := by
  let j := IsScalarTower.toAlgHom K M Ω
  let := IsGalois.of_algEquiv j.equivFieldRange
  have h := restrictNormal_mem_upperRamificationGroupInfinite K Ω j.fieldRange u hu σ hσ
  rw [restrictNormal_scalarImage] at h
  exact (mem_upperRamificationGroupInfinite_autCongr_iff K j.equivFieldRange hu _).mp h

variable [IsGalois K Ω] [PerfectField 𝓀[K]]

/-- Every upper automorphism of an abstract Galois subextension lifts to the ambient
infinite upper group. -/
theorem exists_lift_upperRamificationGroupInfinite_tower
    {u : ℝ} (hu : -1 ≤ u) (σ : M ≃ₐ[K] M)
    (hσ : σ ∈ upperRamificationGroupInfinite K M u) :
    ∃ τ ∈ upperRamificationGroupInfinite K Ω u, τ.restrictNormal M = σ := by
  let j := IsScalarTower.toAlgHom K M Ω
  let := IsGalois.of_algEquiv j.equivFieldRange
  have h := (mem_upperRamificationGroupInfinite_autCongr_iff K j.equivFieldRange hu σ).mpr hσ
  obtain ⟨τ, hτ, he⟩ := exists_lift_infinite_upper_restriction K Ω j.fieldRange u hu
    (j.equivFieldRange.autCongr σ) h
  refine ⟨τ, hτ, j.equivFieldRange.autCongr.injective ?_⟩
  exact (restrictNormal_scalarImage K Ω M τ).symm.trans he

/-- Ordinary infinite Galois restriction preserves upper numbering in an abstract tower. -/
theorem restrictNormalHom_map_upperRamificationGroupInfinite_tower
    {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K Ω u).map (AlgEquiv.restrictNormalHom M) =
      upperRamificationGroupInfinite K M u := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact restrictNormal_mem_upperRamificationGroupInfinite_tower K Ω M hu σ hσ
  · intro σ hσ
    obtain ⟨τ, hτ, he⟩ := exists_lift_upperRamificationGroupInfinite_tower K Ω M hu σ hσ
    exact Subgroup.mem_map.mpr ⟨τ, hτ, he⟩

end FontaineWintenberger
