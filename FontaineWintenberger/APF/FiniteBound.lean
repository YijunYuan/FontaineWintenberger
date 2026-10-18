/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Finite
public import FontaineWintenberger.APF.Bound

/-!
# The actual finite Galois meaning of the APF ramification bound

Absolute restriction has the actual fixing subgroup as kernel, and its
upper image is the actual finite upper group. Thus the public supremum is
computed by the finite extension's own upper filtration.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

theorem apfSubgroup_eq_top_iff_finite_upper_eq_top
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K E u = ⊤ ↔
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u = ⊤ := by
  rw [apfSubgroup_eq_comap_upper K
    (⟨E⟩ : FiniteGaloisIntermediateField K (SeparableClosure K)) hu]
  constructor
  · intro h
    apply top_unique
    intro σ _
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (SeparableClosure K) σ
    have ht : τ ∈ (upperRamificationGroup (R := spectralIntegerRing K E)
        (E ≃ₐ[K] E) u).comap (AlgEquiv.restrictNormalHom E) := by rw [h]; trivial
    simpa only [Subgroup.mem_comap, hτ] using ht
  · intro h
    rw [h, Subgroup.comap_top]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The full-group condition is intrinsic to the actual abstract finite
extension, independently of its separable embedding. -/
theorem apfSubgroup_fieldRange_eq_top_iff_finite_upper_eq_top
    (i : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K i.fieldRange u = ⊤ ↔
      upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u = ⊤ := by
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let : IsGalois K i.fieldRange := IsGalois.of_algEquiv i.equivFieldRange
  rw [apfSubgroup_eq_top_iff_finite_upper_eq_top K i.fieldRange hu,
    ← upperRamificationGroup_map_autCongr K i.equivFieldRange hu]
  constructor
  · intro h
    apply top_unique
    intro g _
    have hg : i.equivFieldRange.autCongr g ∈
        (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).map
          i.equivFieldRange.autCongr.toMonoidHom := by rw [h]; trivial
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp hg
    exact i.equivFieldRange.autCongr.injective hsg ▸ hs
  · intro h
    apply top_unique
    intro g _
    obtain ⟨s, rfl⟩ := i.equivFieldRange.autCongr.surjective g
    exact Subgroup.mem_map.mpr ⟨s, by rw [h]; trivial, rfl⟩

/-- The public extended-real bound is exactly the supremum where the
actual finite upper group is full. -/
theorem apfRamificationBound_eq_sSup_finite_upper :
    apfRamificationBound K L = sSup {x : EReal | ∃ u : ℝ, -1 ≤ u ∧
      upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u = ⊤ ∧
        x = (u : EReal)} := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfRamificationBound_eq_embedding K L i]
  congr 1
  ext x
  constructor <;> rintro ⟨u, hu, hg, rfl⟩
  · exact ⟨u, hu,
      (apfSubgroup_fieldRange_eq_top_iff_finite_upper_eq_top K L i hu).mp hg, rfl⟩
  · exact ⟨u, hu,
      (apfSubgroup_fieldRange_eq_top_iff_finite_upper_eq_top K L i hu).mpr hg, rfl⟩

end FontaineWintenberger
