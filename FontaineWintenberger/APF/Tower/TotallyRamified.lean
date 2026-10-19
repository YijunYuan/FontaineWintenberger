/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Residue

/-!
# APF indices of totally ramified finite extensions

* For a finite Galois `Ω/K` and `M ⊆ Ω`, the index of `Gal(Ω/M) ⊔ Gal(Ω/K)_0` in `Gal(Ω/K)` is
  the residue degree of `M/K`.
* For a finite separable `L/K` with `e(L/K) = [L : K]`, the index of the APF subgroup of any
  embedding of `L` equals the APF index `apfIndex K L u`, for `u ≥ 0`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]

theorem fixingSubgroup_sup_lowerRamificationGroup_zero_index_eq_residueDegree
    (Ω : Type*) [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (M : IntermediateField K Ω) :
    (M.fixingSubgroup ⊔ lowerRamificationGroup (Ω ≃ₐ[K] Ω)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 0).index =
      Module.finrank 𝓀[K] (IsLocalRing.ResidueField (spectralIntegerRing K M)) := by
  let j : Ω →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have h := apfSubgroup_index_zero_eq_residueDegree_of_finiteGalois K Ω M j
  rw [apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index K Ω M j (by norm_num),
    upperRamificationGroup_zero, ← lowerRamificationGroup_zero] at h
  exact h

theorem apfSubgroup_fieldRange_index_eq_apfIndex_of_ramificationIdx_eq_finrank
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (j : L →ₐ[K] SeparableClosure K)
    (he : (IsLocalRing.maximalIdeal (spectralIntegerRing K L)).ramificationIdx 𝒪[K] =
      Module.finrank K L) {u : ℝ} (hu : 0 ≤ u) :
    (apfSubgroup K j.fieldRange u).index = apfIndex K L u := by
  let E := IntermediateField.normalClosure K L (SeparableClosure K)
  let i : L →ₐ[K] E :=
    j.codRestrict E.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let M := i.fieldRange
  let e : L ≃ₐ[K] M := i.equivFieldRange
  let : FiniteDimensional K M := Module.Finite.equiv e.toLinearEquiv
  let w := (spectralValuation K E).comap (algebraMap M E)
  have : (NormedField.valuation (K := K)).HasExtension w :=
    intermediate_spectral_hasExtension K E M
  have := intermediate_spectral_isDiscreteValuationRing K E M
  have : IsScalarTower 𝒪[K] K M :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := M) (NormedField.valuation (K := K))
  have : IsScalarTower 𝒪[K] w.valuationSubring M :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (NormedField.valuation (K := K)) w
  have : Module.Finite 𝒪[K] w.valuationSubring := extensionValuationSubring_moduleFinite K M w
  have hn : Module.finrank K M = Module.finrank K L := e.toLinearEquiv.finrank_eq.symm
  have heB : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[K] =
      Module.finrank K M := by
    rw [extensionValuationSubring_ramificationIdx_eq_spectral K M w,
      spectral_ramificationIdx_algEquiv K e, he, hn]
  have hf : Module.finrank 𝓀[K] (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
    have hd := local_ramificationIdx_mul_residueDegree_eq_finrank 𝒪[K] w.valuationSubring K M
    rw [heB] at hd
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos : 0 < Module.finrank K M)
      (by simpa only [mul_one] using hd)
  have hz : (M.fixingSubgroup ⊔ lowerRamificationGroup (E ≃ₐ[K] E)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) 0).index = 1 := by
    rw [intermediate_spectral_zeroOrbitIndex_eq_residueDegree K E M, hf]
  have hrange : (E.val.comp M.val).fieldRange = j.fieldRange := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨l, hl⟩ := a.property
      exact ⟨l, congrArg (fun y : E => (y : SeparableClosure K)) hl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨⟨i l, ⟨l, rfl⟩⟩, rfl⟩
  rw [← hrange, apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index
    K E M E.val (by linarith : -1 ≤ u),
    upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex (R := spectralIntegerRing K E)
      (E ≃ₐ[K] E) M.fixingSubgroup hu, hz, one_mul,
    apfIndex_algEquiv K L e u, apfIndex_eq_subgroupRelIndex_of_finiteGalois K E M hu,
    upperRamificationGroup_zero, lowerRamificationGroup_zero]

end FontaineWintenberger
