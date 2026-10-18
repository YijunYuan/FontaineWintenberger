/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.FiniteFunctorLaws
public import FontaineWintenberger.FieldOfNorms.FunctorEquivariance

/-!
# Naturality of the original finite norm-family maps

The actual finite-embedding maps agree with the original isomorphism maps.
Commuting original isomorphisms and inclusions give their functor laws on
the same original norm families.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) {L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]

/-- The codomain is finite over the actual image of an isomorphism. -/
theorem moduleFinite_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
    Module.Finite e.toAlgHom.fieldRange M := by
  apply Module.Finite.of_surjective (Algebra.linearMap e.toAlgHom.fieldRange M)
  intro m
  exact ⟨⟨m, e.symm m, e.apply_symm_apply m⟩, rfl⟩

/-- The original image extension of an isomorphism is separable of degree one. -/
theorem isSeparable_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
    Algebra.IsSeparable e.toAlgHom.fieldRange M := by
  constructor
  intro m
  exact isSeparable_algebraMap (⟨m, e.symm m, e.apply_symm_apply m⟩ : e.toAlgHom.fieldRange)

/-- Pulling back through the actual image factorization gives exactly the
original inverse-isomorphism finite index. -/
theorem FiniteIntermediateField.pullback_algEquiv (e : L ≃ₐ[K] M) (D : FiniteIntermediateField K M)
    :
    FiniteIntermediateField.map e.toAlgHom.equivFieldRange.symm.toAlgHom
        (FiniteIntermediateField.pullbackLayer K e.toAlgHom.fieldRange D) =
      FiniteIntermediateField.map e.symm.toAlgHom D := by
  apply Subtype.ext
  rw [FiniteIntermediateField.pullback_fieldRange]
  ext x
  change e x ∈ D.val ↔ x ∈ D.val.map e.symm.toAlgHom
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change e (e.symm y) ∈ D.val
    change y ∈ D.val at hy
    rw [AlgEquiv.apply_symm_apply]
    exact hy

/-- The same actual finite-embedding map on an isomorphism is the already
constructed original isomorphism map, with no assumed comparison. -/
theorem FieldOfNorms.finiteEmbeddingMap_algEquiv [Algebra.IsAlgebraic K L]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    letI := moduleFinite_algEquiv_fieldRange K e
    letI := isSeparable_algEquiv_fieldRange K e
    FieldOfNorms.finiteEmbeddingMap K e.toAlgHom x = FieldOfNorms.map e x := by
  let := moduleFinite_algEquiv_fieldRange K e
  let := isSeparable_algEquiv_fieldRange K e
  let : Algebra.IsAlgebraic K e.toAlgHom.fieldRange := e.toAlgHom.equivFieldRange.isAlgebraic
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K e.toAlgHom.fieldRange)
    (goodFiniteLayers_cofinal K e.toAlgHom.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap K e.toAlgHom D hD,
    coe_fieldOfNormsEval_fieldOfNormsMap, FiniteIntermediateField.pullback_algEquiv K e D]
  rfl

section Naturality

variable {M' N' : Type*} [Field M'] [Field N'] [Algebra K M'] [Algebra K N']
    [Algebra M N] [Algebra M' N'] [IsScalarTower K M N] [IsScalarTower K M' N']

/-- The actual original pullback indices commute with the given isomorphisms. -/
theorem FiniteIntermediateField.pullbackLayer_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.map e.toAlgHom (FiniteIntermediateField.pullbackLayer K M D) =
      FiniteIntermediateField.pullbackLayer K M' (FiniteIntermediateField.map f.toAlgHom D) := by
  apply Subtype.ext
  exact FiniteIntermediateField.pullback_map K e f h D

variable [Algebra.IsAlgebraic K M] [Algebra.IsAlgebraic K M']
    [Module.Finite M N] [Module.Finite M' N']
    [Algebra.IsSeparable M N] [Algebra.IsSeparable M' N']

/-- Commuting actual isomorphisms and finite inclusions give the same original
map of norm families, by the proved cofinal original good-coordinate formulas. -/
theorem FieldOfNorms.finiteMap_naturality (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (x : FieldOfNorms K M) :
    FieldOfNorms.map f (FieldOfNorms.finiteMap K M N x) =
      FieldOfNorms.finiteMap K M' N' (FieldOfNorms.map e x) := by
  have hs (m' : M') :
      f.symm (algebraMap M' N' m') = algebraMap M N (e.symm m') := by
    apply f.injective
    rw [f.apply_symm_apply, h, e.apply_symm_apply]
  apply FieldOfNorms.ext_cofinal K N' (IsGoodFiniteLayer K M')
    (goodFiniteLayers_cofinal K M' N')
  intro D hD
  have hDb : IsGoodFiniteLayer K M (FiniteIntermediateField.map f.symm.toAlgHom D) :=
    (isGoodFiniteLayer_map_iff K e.symm f.symm hs D).mpr hD
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap,
    coe_fieldOfNormsEval_finiteFieldOfNormsMap K M N _ hDb,
    coe_fieldOfNormsEval_finiteFieldOfNormsMap K M' N' D hD,
    coe_fieldOfNormsEval_fieldOfNormsMap,
    h, FiniteIntermediateField.pullbackLayer_map K e.symm f.symm hs D]

end Naturality

section RangeScalars

variable (M N) [Algebra M N] [IsScalarTower K M N]

/-- Finiteness over the original coefficient field gives finiteness over
its actual image, through the original source-to-image isomorphism. -/
theorem moduleFinite_algebraMap_fieldRange [Module.Finite M N] :
    Module.Finite (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Module.Finite.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

/-- Separability over the original coefficient field gives separability over
the same actual image, with the original inclusion square. -/
theorem isSeparable_algebraMap_fieldRange [Algebra.IsSeparable M N] :
    Algebra.IsSeparable (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Algebra.IsSeparable.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

end RangeScalars

/-- The original image finiteness transports to the original embedding
as scalar map; it is proved rather than supplied for the new scalar structure. -/
theorem moduleFinite_fieldRange_scalars (τ : L →ₐ[K] M) [Module.Finite τ.fieldRange M] :
    letI := τ.toRingHom.toAlgebra
    Module.Finite L M := by
  let := τ.toRingHom.toAlgebra
  apply Module.Finite.of_equiv_equiv τ.equivFieldRange.symm.toRingEquiv (RingEquiv.refl M)
  ext r
  change τ (τ.equivFieldRange.symm r) = (r : M)
  exact congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply r)

/-- The original image separability transports along the same actual
coefficient isomorphism and the original identity on the ambient field. -/
theorem isSeparable_fieldRange_scalars (τ : L →ₐ[K] M)
    [Algebra.IsSeparable τ.fieldRange M] :
    letI := τ.toRingHom.toAlgebra
    Algebra.IsSeparable L M := by
  let := τ.toRingHom.toAlgebra
  apply Algebra.IsSeparable.of_equiv_equiv τ.equivFieldRange.symm.toRingEquiv (RingEquiv.refl M)
  ext r
  change τ (τ.equivFieldRange.symm r) = (r : M)
  exact congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply r)

/-- Algebraicity of the original source and finiteness over its actual image
give algebraicity of the original target. -/
theorem isAlgebraic_of_finite_fieldRange [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M) [Module.Finite τ.fieldRange M] : Algebra.IsAlgebraic K M := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact Algebra.IsAlgebraic.trans K τ.fieldRange M

section InclusionComparison

variable (M N) [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The actual finite-embedding map of an original algebra inclusion agrees
with the original inclusion map; actual range naturality proves the bridge. -/
theorem FieldOfNorms.finiteEmbeddingMap_algebraMap (x : FieldOfNorms K M) :
    letI := moduleFinite_algebraMap_fieldRange K M N
    letI := isSeparable_algebraMap_fieldRange K M N
    FieldOfNorms.finiteEmbeddingMap K (IsScalarTower.toAlgHom K M N) x =
      FieldOfNorms.finiteMap K M N x := by
  let := moduleFinite_algebraMap_fieldRange K M N
  let := isSeparable_algebraMap_fieldRange K M N
  let τ := IsScalarTower.toAlgHom K M N
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  change FieldOfNorms.finiteMap K τ.fieldRange N (FieldOfNorms.map τ.equivFieldRange x) = _
  simpa only [FieldOfNorms.map_refl] using
    (FieldOfNorms.finiteMap_naturality K τ.equivFieldRange (AlgEquiv.refl : N ≃ₐ[K] N)
      (fun _ => rfl) x).symm

end InclusionComparison

/-- Naturality for the same arbitrary original embedding maps, obtained
through their proved original inclusion comparisons. -/
theorem FieldOfNorms.finiteEmbeddingMap_naturality [Algebra.IsAlgebraic K L]
    {L' M' : Type*} [Field L'] [Field M'] [Algebra K L'] [Algebra K M']
    (τ : L →ₐ[K] M) (τ' : L' →ₐ[K] M')
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite τ'.fieldRange M'] [Algebra.IsSeparable τ'.fieldRange M']
    (e : L ≃ₐ[K] L') (f : M ≃ₐ[K] M')
    (h : ∀ l : L, f (τ l) = τ' (e l)) (x : FieldOfNorms K L) :
    letI : Algebra.IsAlgebraic K L' := e.isAlgebraic
    FieldOfNorms.map f (FieldOfNorms.finiteEmbeddingMap K τ x) =
      FieldOfNorms.finiteEmbeddingMap K τ' (FieldOfNorms.map e x) := by
  let : Algebra.IsAlgebraic K L' := e.isAlgebraic
  let := τ.toRingHom.toAlgebra
  let := τ'.toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower K L' M' := IsScalarTower.of_algebraMap_eq (fun k => (τ'.commutes k).symm)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite L' M' := moduleFinite_fieldRange_scalars K τ'
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable L' M' := isSeparable_fieldRange_scalars K τ'
  calc
    FieldOfNorms.map f (FieldOfNorms.finiteEmbeddingMap K τ x) =
        FieldOfNorms.map f (FieldOfNorms.finiteMap K L M x) :=
      congrArg (FieldOfNorms.map f) (FieldOfNorms.finiteEmbeddingMap_algebraMap K L M x)
    _ = FieldOfNorms.finiteMap K L' M' (FieldOfNorms.map e x) :=
      FieldOfNorms.finiteMap_naturality K e f h x
    _ = FieldOfNorms.finiteEmbeddingMap K τ' (FieldOfNorms.map e x) :=
      (FieldOfNorms.finiteEmbeddingMap_algebraMap K L' M' (FieldOfNorms.map e x)).symm

/-- The composite of the original finite embeddings is finite over its
actual image; the scalar structures are the original embedding maps. -/
theorem moduleFinite_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Module.Finite τ.fieldRange M] [Module.Finite σ.fieldRange N] :
    Module.Finite (σ.comp τ).fieldRange N := by
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite M N := moduleFinite_fieldRange_scalars K σ
  let : Module.Finite L N := Module.Finite.trans M N
  exact moduleFinite_algebraMap_fieldRange K L N

/-- Separability of the actual image extensions is preserved by the same
original composite embedding, without a new separability assumption. -/
theorem isSeparable_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Algebra.IsSeparable τ.fieldRange M] [Algebra.IsSeparable σ.fieldRange N] :
    Algebra.IsSeparable (σ.comp τ).fieldRange N := by
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable M N := isSeparable_fieldRange_scalars K σ
  let : Algebra.IsSeparable L N := Algebra.IsSeparable.trans L M N
  exact isSeparable_algebraMap_fieldRange K L N

/-- Equal original embeddings induce equal original norm-family maps,
including their proved finite-image instance transports. -/
theorem FieldOfNorms.finiteEmbeddingMap_congr [Algebra.IsAlgebraic K L]
    {τ σ : L →ₐ[K] M}
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange M] [Algebra.IsSeparable σ.fieldRange M]
    (h : τ = σ) (x : FieldOfNorms K L) :
    FieldOfNorms.finiteEmbeddingMap K τ x = FieldOfNorms.finiteEmbeddingMap K σ x := by
  subst σ
  rfl

/-- The same original arbitrary-embedding map preserves the actual identity. -/
theorem FieldOfNorms.finiteEmbeddingMap_refl [Algebra.IsAlgebraic K L]
    (x : FieldOfNorms K L) :
    letI : Module.Finite (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    letI : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    FieldOfNorms.finiteEmbeddingMap K (AlgHom.id K L) x = x := by
  let : Module.Finite (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let := moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let := isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
  exact (FieldOfNorms.finiteEmbeddingMap_congr K h x).symm.trans
    ((FieldOfNorms.finiteEmbeddingMap_algEquiv K (AlgEquiv.refl : L ≃ₐ[K] L) x).trans
      (FieldOfNorms.map_refl x))

/-- Arbitrary finite separable embeddings compose on the same original norm
families. The genuine scalar bridges reduce to the simultaneous-good-stage
composition theorem for the actual original inclusions. -/
theorem FieldOfNorms.finiteEmbeddingMap_trans [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange N] [Algebra.IsSeparable σ.fieldRange N]
    (x : FieldOfNorms K L) :
    letI := isAlgebraic_of_finite_fieldRange K τ
    letI := moduleFinite_comp_fieldRange K τ σ
    letI := isSeparable_comp_fieldRange K τ σ
    FieldOfNorms.finiteEmbeddingMap K σ (FieldOfNorms.finiteEmbeddingMap K τ x) =
      FieldOfNorms.finiteEmbeddingMap K (σ.comp τ) x := by
  let := isAlgebraic_of_finite_fieldRange K τ
  let := moduleFinite_comp_fieldRange K τ σ
  let := isSeparable_comp_fieldRange K τ σ
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => (σ.commutes k).symm)
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite M N := moduleFinite_fieldRange_scalars K σ
  let : Module.Finite L N := Module.Finite.trans M N
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable M N := isSeparable_fieldRange_scalars K σ
  let : Algebra.IsSeparable L N := Algebra.IsSeparable.trans L M N
  calc
    FieldOfNorms.finiteEmbeddingMap K σ (FieldOfNorms.finiteEmbeddingMap K τ x) =
        FieldOfNorms.finiteMap K M N (FieldOfNorms.finiteEmbeddingMap K τ x) :=
      FieldOfNorms.finiteEmbeddingMap_algebraMap K M N _
    _ = FieldOfNorms.finiteMap K M N (FieldOfNorms.finiteMap K L M x) :=
      congrArg (FieldOfNorms.finiteMap K M N) (FieldOfNorms.finiteEmbeddingMap_algebraMap K L M x)
    _ = FieldOfNorms.finiteMap K L N x := FieldOfNorms.finiteMap_trans K L M N x
    _ = FieldOfNorms.finiteEmbeddingMap K (σ.comp τ) x :=
      (FieldOfNorms.finiteEmbeddingMap_algebraMap K L N x).symm

/-- The prescribed original good coordinates uniquely determine the same
arbitrary finite-embedding map, even among all functions of norm families. -/
theorem FieldOfNorms.finiteEmbeddingMap_unique [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (g : FieldOfNorms K L → FieldOfNorms K M)
    (hg : ∀ (D : FiniteIntermediateField K M), IsGoodFiniteLayer K τ.fieldRange D →
      ∀ x, (FieldOfNorms.coord K M D (g x) : M) =
        τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
          (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L)) :
    g = FieldOfNorms.finiteEmbeddingMap K τ := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  funext x
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K τ.fieldRange)
    (goodFiniteLayers_cofinal K τ.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [hg D hD x, coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap K τ D hD]

end FontaineWintenberger
