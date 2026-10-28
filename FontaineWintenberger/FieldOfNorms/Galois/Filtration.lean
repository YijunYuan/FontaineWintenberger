/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Galois.UpperLimit
public import FontaineWintenberger.FieldOfNorms.Relative.Hom

/-!
# The ramification filtration under the field-of-norms correspondence

The finite norm-field actions define upper ramification independently of the original
ambient upper groups. Transport along `RelFieldOfNorms.autEquiv` places that filtration on
the Galois group of the actual relative field of norms.

`RelFieldOfNorms.map_normUpperRamificationGroup` is Wintenberger's Corollary 3.3.6:
under the norm-field correspondence and the inclusion into `Gal(M/K)`,
`H ^ (ψ_{L/K}(u)) = G ^ u ∩ H`. No normality assumption on `L/K` is needed.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Corollary 3.3.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable L M]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Upper ramification on the Galois group of the relative field of norms. Its finite
stage filtrations are computed from the intrinsic norm-field integer actions. -/
def RelFieldOfNorms.normUpperRamificationGroup (u : ℝ) :
    Subgroup (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] RelFieldOfNorms K L M) :=
  (RelFieldOfNorms.upperRamificationGroup K L M u).map
    (RelFieldOfNorms.autEquiv K L M).toMonoidHom

/-- The existing Galois correspondence identifies the finite-stage upper conditions with
membership in the upper group of the relative norm field. -/
@[simp]
theorem RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_iff
    (u : ℝ) (σ : M ≃ₐ[L] M) :
    RelFieldOfNorms.autEquiv K L M σ ∈ RelFieldOfNorms.normUpperRamificationGroup K L M u ↔
      σ ∈ RelFieldOfNorms.upperRamificationGroup K L M u := by
  rw [RelFieldOfNorms.normUpperRamificationGroup, Subgroup.mem_map_equiv,
    MulEquiv.symm_apply_apply]

/-- The canonical embedding of the norm-field Galois group into the original ambient
Galois group, through the inverse field-of-norms correspondence. -/
def RelFieldOfNorms.normGaloisEmbedding :
    (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] RelFieldOfNorms K L M) →* (M ≃ₐ[K] M) :=
  (AlgEquiv.restrictScalarsHom K).comp (RelFieldOfNorms.autEquiv K L M).symm.toMonoidHom

omit [Algebra.IsSeparable K M] in
/-- The canonical ambient homomorphism is an embedding. -/
theorem RelFieldOfNorms.normGaloisEmbedding_injective :
    Function.Injective (RelFieldOfNorms.normGaloisEmbedding K L M) :=
  (AlgEquiv.restrictScalars_injective K).comp (RelFieldOfNorms.autEquiv K L M).symm.injective

omit [Algebra.IsSeparable K M] in
/-- On a corresponding automorphism, the ambient embedding is ordinary scalar restriction. -/
@[simp]
theorem RelFieldOfNorms.normGaloisEmbedding_autEquiv (σ : M ≃ₐ[L] M) :
    RelFieldOfNorms.normGaloisEmbedding K L M (RelFieldOfNorms.autEquiv K L M σ) =
      σ.restrictScalars K := by
  change ((RelFieldOfNorms.autEquiv K L M).symm
    (RelFieldOfNorms.autEquiv K L M σ)).restrictScalars K = _
  rw [MulEquiv.symm_apply_apply]

omit [Algebra.IsSeparable K M] in
/-- The ambient image is precisely the subgroup fixing the original relative base. -/
theorem RelFieldOfNorms.normGaloisEmbedding_range :
    (RelFieldOfNorms.normGaloisEmbedding K L M).range =
      (AlgEquiv.restrictScalarsHom K (S := L) (A := M)).range := by
  rw [RelFieldOfNorms.normGaloisEmbedding, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (RelFieldOfNorms.autEquiv K L M).symm.surjective,
    Subgroup.map_top]

/-- Transporting the independently defined upper filtration commutes with the canonical
embedding into the ambient Galois group. -/
theorem RelFieldOfNorms.map_normUpperRamificationGroup_eq_map (u : ℝ) :
    (RelFieldOfNorms.normUpperRamificationGroup K L M u).map
        (RelFieldOfNorms.normGaloisEmbedding K L M) =
      (RelFieldOfNorms.upperRamificationGroup K L M u).map
        (AlgEquiv.restrictScalarsHom K) := by
  have hcomp : (RelFieldOfNorms.normGaloisEmbedding K L M).comp
      (RelFieldOfNorms.autEquiv K L M).toMonoidHom = AlgEquiv.restrictScalarsHom K := by
    apply MonoidHom.ext
    exact RelFieldOfNorms.normGaloisEmbedding_autEquiv K L M
  rw [RelFieldOfNorms.normUpperRamificationGroup, Subgroup.map_map, hcomp]

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable L M] [IsGalois K M] [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- **Wintenberger, Corollary 3.3.6.** The norm-field upper group at `ψ_{L/K}(u)` maps to
the intersection of the original upper group at `u` with the relative Galois group. -/
theorem RelFieldOfNorms.map_normUpperRamificationGroup {u : ℝ} (hu : -1 ≤ u) :
    (RelFieldOfNorms.normUpperRamificationGroup K L M (apfPsi K L u)).map
        (RelFieldOfNorms.normGaloisEmbedding K L M) =
      upperRamificationGroupInfinite K M u ⊓
        (RelFieldOfNorms.normGaloisEmbedding K L M).range := by
  rw [RelFieldOfNorms.map_normUpperRamificationGroup_eq_map,
    RelFieldOfNorms.normGaloisEmbedding_range]
  exact RelFieldOfNorms.map_upperRamificationGroup K L M hu

/-- The ramification comparison for an individual corresponding automorphism. -/
theorem RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_apfPsi_iff
    {u : ℝ} (hu : -1 ≤ u) (σ : M ≃ₐ[L] M) :
    RelFieldOfNorms.autEquiv K L M σ ∈
        RelFieldOfNorms.normUpperRamificationGroup K L M (apfPsi K L u) ↔
      σ.restrictScalars K ∈ upperRamificationGroupInfinite K M u := by
  rw [RelFieldOfNorms.autEquiv_mem_normUpperRamificationGroup_iff,
    RelFieldOfNorms.upperRamificationGroup_eq_comap K L M hu]
  rfl

end FontaineWintenberger
