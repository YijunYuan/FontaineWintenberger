/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Galois

/-!
# APF subgroups of subextensions of a Galois subextension

For `E/K` Galois inside `K^sep` and `M ⊆ E`, the APF subgroup of `M` is the preimage under
restriction `Gal(K^sep/K) → Gal(E/K)` of `Gal(E/M) ⊔ Gal(E/K)^u`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]

theorem apfSubgroup_map_eq_comap_upperRamificationGroupInfinite
    (E : IntermediateField K (SeparableClosure K)) [IsGalois K E]
    (M : IntermediateField K E) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (M.map E.val) u =
      (M.fixingSubgroup ⊔ upperRamificationGroupInfinite K E u).comap
        (AlgEquiv.restrictNormalHom E) := by
  let ρ : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* (E ≃ₐ[K] E) :=
    AlgEquiv.restrictNormalHom E
  have hfix : (M.map E.val).fixingSubgroup = M.fixingSubgroup.comap ρ :=
    IntermediateField.map_fixingSubgroup (F := K) (E := E)
      (E' := SeparableClosure K) (L := M)
  have hker : E.fixingSubgroup ≤ M.fixingSubgroup.comap ρ := by
    rw [← IntermediateField.restrictNormalHom_ker E]
    intro g hg
    change ρ g ∈ M.fixingSubgroup
    rw [MonoidHom.mem_ker.mp hg]
    exact M.fixingSubgroup.one_mem
  unfold apfSubgroup
  rw [hfix]
  calc
    _ = M.fixingSubgroup.comap ρ ⊔
        (E.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u) := by
      rw [← sup_assoc, sup_eq_left.mpr hker]
    _ = M.fixingSubgroup.comap ρ ⊔
        (upperRamificationGroupInfinite K E u).comap ρ := by
      rw [← apfSubgroup, apfSubgroup_eq_comap_upperInfinite K E hu]
    _ = _ := Subgroup.comap_sup_eq ρ _ _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (SeparableClosure K))

end FontaineWintenberger
