/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.Ramification.HerbrandInverse

/-!
# Finite Galois specialization of the APF functions

Ordinary restriction and its actual kernel identify the APF subgroup as the
preimage of the finite upper group. Relative indices and their integrals
therefore recover the proved finite Herbrand functions on their own rings.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

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

/-- The intrinsic abstract-extension index equals the actual finite upper relative index. -/
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

/-- The APF integral is the actual finite inverse Herbrand function. -/
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

/-- The actual inverse of the APF integral is the finite Herbrand function. -/
theorem apfPhi_eq_herbrandFunction (hL : IsAPF K L) {u : ℝ} (hu : -1 ≤ u) :
    apfPhi K L hL u = herbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u := by
  apply (IsAPF.strictMono_apfPsi K L hL).injective
  rw [apfPsi_apfPhi, apfPsi_eq_inverseHerbrandFunction K L (herbrandFunction_mem_Ici _ hu),
    inverseHerbrandFunction_herbrandFunction _ hu]

end FontaineWintenberger
