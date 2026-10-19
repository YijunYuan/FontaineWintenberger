/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.Ramification.Herbrand.Inverse
public import FontaineWintenberger.APF.RamificationBound

/-!
# APF functions of finite Galois extensions

## Finite Galois specialization of the APF functions

Ordinary restriction and its kernel identify the APF subgroup as the
preimage of the finite upper group. Relative indices and their integrals
therefore recover the proved finite Herbrand functions on their own rings.

## The finite Galois meaning of the APF ramification bound

Absolute restriction has the fixing subgroup as kernel, and its
upper image is the finite upper group. Thus the public supremum is
computed by the finite extension's own upper filtration.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField 𝓀[K]]

theorem apfSubgroup_eq_comap_upper
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K E.toIntermediateField u =
      (upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).comap
        (AlgEquiv.restrictNormalHom E) := by
  rw [← absolute_map_upperRamificationGroup K E u hu, Subgroup.comap_map_eq,
    IntermediateField.restrictNormalHom_ker E.toIntermediateField]
  exact sup_comm _ _

theorem apfInertiaIndex_eq_upperRelIndex
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) {u : ℝ} (hu : 0 ≤ u) :
    apfInertiaIndex K E.toIntermediateField u =
      (upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).relIndex
        (upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) 0) := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.inf_relIndex_right,
    apfSubgroup_eq_comap_upper K E (by linarith), Subgroup.relIndex_comap,
    absolute_map_upperRamificationGroup K E 0 (by norm_num)]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The intrinsic abstract-extension index equals the finite upper relative index. -/
theorem apfIndex_eq_upperRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K L u =
      (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).relIndex
        (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) 0) := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let : IsGalois K i.fieldRange := IsGalois.of_algEquiv i.equivFieldRange
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := ⟨i.fieldRange⟩
  rw [apfIndex_eq_embedding K L i]
  have h := apfInertiaIndex_eq_upperRelIndex K E hu
  change apfInertiaIndex K i.fieldRange u = _ at h
  rw [h, ← upperRamificationGroup_map_autCongr K i.equivFieldRange (by linarith : -1 ≤ u),
    ← upperRamificationGroup_map_autCongr K i.equivFieldRange (by norm_num : -1 ≤ (0 : ℝ))]
  exact Subgroup.relIndex_map_map_of_injective _ _ i.equivFieldRange.autCongr.injective

/-- The APF integral is the finite inverse Herbrand function. -/
theorem apfPsi_eq_inverseHerbrandFunction {u : ℝ} (hu : -1 ≤ u) :
    apfPsi K L u = inverseHerbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u := by
  by_cases hu' : u ≤ 0
  · rw [apfPsi_of_nonpos K L hu', inverseHerbrandFunction_of_nonpos _ hu hu']
  · rw [apfPsi_eq_integral_index K L (le_of_not_ge hu'),
      inverseHerbrandFunction_eq_integral_relIndex _ (le_of_not_ge hu')]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (le_of_not_ge hu')]
    intro v hv
    exact congrArg (fun n : ℕ ↦ (n : ℝ)) (apfIndex_eq_upperRelIndex K L hv.1)

/-- The inverse of the APF integral is the finite Herbrand function. -/
theorem apfPhi_eq_herbrandFunction [IsAPF K L] {u : ℝ} (hu : -1 ≤ u) :
    apfPhi K L u = herbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u := by
  apply (IsAPF.strictMono_apfPsi K L).injective
  rw [apfPsi_apfPhi, apfPsi_eq_inverseHerbrandFunction K L (herbrandFunction_mem_Ici _ hu),
    inverseHerbrandFunction_herbrandFunction _ hu]

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField 𝓀[K]]

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

/-- The full-group condition is intrinsic to the abstract finite
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
finite upper group is full. -/
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
