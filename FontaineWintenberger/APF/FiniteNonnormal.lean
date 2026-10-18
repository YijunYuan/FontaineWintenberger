/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Finite
public import FontaineWintenberger.Ramification.HerbrandSubgroup

/-!
# Finite non-Galois APF change of parameter

Ordinary restriction to a finite Galois overfield identifies the actual
fixing subgroup of an arbitrary intermediate field and its inertia coset index.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
variable (M : IntermediateField K E)

local notation "ρ" => AlgEquiv.restrictNormalHom E
local notation "H₀" => M.fixingSubgroup
local notation "U₀" => upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E)

/-- The actual APF product of a nonnormal finite intermediate field is a restriction preimage. -/
theorem apfSubgroup_map_eq_comap_sup_upper {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (M.map E.toIntermediateField.val) u =
      (H₀ ⊔ U₀ u).comap ρ := by
  have hfix : (M.map E.toIntermediateField.val).fixingSubgroup = (H₀).comap ρ := by
    exact IntermediateField.map_fixingSubgroup (F := K) (E := E)
      (E' := SeparableClosure K) (L := M)
  have hker : E.toIntermediateField.fixingSubgroup ≤ (H₀).comap ρ := by
    rw [← IntermediateField.restrictNormalHom_ker E.toIntermediateField]
    intro g hg
    change ρ g ∈ H₀
    rw [MonoidHom.mem_ker.mp hg]
    exact (H₀).one_mem
  unfold apfSubgroup
  rw [hfix]
  calc
    _ = (H₀).comap ρ ⊔
        (E.toIntermediateField.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u) := by
      rw [← sup_assoc, sup_eq_left.mpr hker]
    _ = (H₀).comap ρ ⊔ (U₀ u).comap ρ := by
      rw [← apfSubgroup, apfSubgroup_eq_comap_upper K E hu]
    _ = _ := Subgroup.comap_sup_eq ρ _ _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (SeparableClosure K))

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- Inertia intersection of the finite fixing-subgroup product. -/
theorem fixingSubgroup_sup_upper_inf_zero {u : ℝ} (hu : 0 ≤ u) :
    (H₀ ⊔ U₀ u) ⊓ U₀ 0 = (H₀ ⊓ U₀ 0) ⊔ U₀ u := by
  have hU : U₀ u ≤ U₀ 0 := upperRamificationGroup_antitoneOn
    (R := spectralIntegerRing K E) (E ≃ₐ[K] E) (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u)
        hu
  apply le_antisymm
  · rintro g ⟨hg, hg₀⟩
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hh₀ : h ∈ U₀ 0 := by
      have := (U₀ 0).mul_mem hg₀ ((U₀ 0).inv_mem (hU hn))
      simpa only [mul_inv_cancel_right] using this
    exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hh₀⟩, n, hn, rfl⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hU)

/-- The intrinsic APF inertia index of an arbitrary finite intermediate field. -/
theorem apfInertiaIndex_map_eq_subgroupRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfInertiaIndex K (M.map E.toIntermediateField.val) u =
      ((H₀ ⊓ U₀ 0) ⊔ U₀ u).relIndex (U₀ 0) := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.inf_relIndex_right,
    apfSubgroup_map_eq_comap_sup_upper K E M (by linarith), Subgroup.relIndex_comap,
    absolute_map_upperRamificationGroup K E 0 (by norm_num),
    ← Subgroup.inf_relIndex_right, fixingSubgroup_sup_upper_inf_zero K E M hu]

/-- The abstract finite field has the same index, without choosing a normality instance. -/
theorem apfIndex_eq_subgroupRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K M u = ((H₀ ⊓ U₀ 0) ⊔ U₀ u).relIndex (U₀ 0) := by
  let i := E.toIntermediateField.val.comp M.val
  rw [apfIndex_eq_embedding K M i]
  have hr : i.fieldRange = M.map E.toIntermediateField.val := by
    simpa only [IntermediateField.fieldRange_val] using
      (AlgHom.map_fieldRange M.val E.toIntermediateField.val).symm
  rw [hr]
  exact apfInertiaIndex_map_eq_subgroupRelIndex K E M hu

/-- The actual non-Galois finite APF integral is the subgroup change of parameter. -/
theorem apfPsi_eq_subgroup_herbrand_comp_inverse {u : ℝ} (hu : -1 ≤ u) :
    apfPsi K M u = herbrandFunction (R := spectralIntegerRing K E) H₀
      (inverseHerbrandFunction (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u) := by
  by_cases hu' : u ≤ 0
  · rw [apfPsi_of_nonpos K M hu',
      subgroup_herbrandFunction_comp_inverse_of_nonpos _ _ hu hu']
  · rw [apfPsi_eq_integral_index K M (le_of_not_ge hu'),
      subgroup_herbrandFunction_comp_inverse_eq_integral _ _ (le_of_not_ge hu')]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (le_of_not_ge hu')]
    intro v hv
    dsimp only
    rw [apfIndex_eq_subgroupRelIndex K E M hv.1, upperRamificationGroup_zero,
      lowerRamificationGroup_zero]

/-- The inverse change of parameter uses the same actual finite overfield and subgroup. -/
theorem apfPhi_eq_herbrand_comp_subgroup_inverse {v : ℝ} (hv : -1 ≤ v) :
    apfPhi K M v =
      herbrandFunction (R := spectralIntegerRing K E) (E ≃ₐ[K] E)
        (inverseHerbrandFunction (R := spectralIntegerRing K E) H₀ v) := by
  apply (IsAPF.strictMono_apfPsi K M).injective
  rw [apfPsi_apfPhi,
    apfPsi_eq_subgroup_herbrand_comp_inverse K E M
      (herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ v)),
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ v),
    herbrandFunction_inverseHerbrandFunction _ hv]

end FontaineWintenberger
