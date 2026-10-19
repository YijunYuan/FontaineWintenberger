/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Functor.Separable
public import FontaineWintenberger.Mathlib.FieldTheory.SeparableEmbeddings

/-!
# Full faithfulness of the field of norms functor

## Full faithfulness for finite separable norm-field maps

The relative Galois equivalences and their original-family formulas
reflect stabilizers. Extending embeddings to a common finite Galois
overfield then gives the full finite Hom correspondence.

## Full faithfulness of the finite separable norm-field functor

Finite relative embeddings commute with composition. Inside a common
finite Galois overfield, the proved Galois Hom correspondence and
fixed fields reflect factorization through each intermediate field.

## Main definitions

* `FieldOfNorms.mapAlgHom`: The map on relative finite embeddings is an algebra homomorphism for the
  norm field, by the embedding composition law.
* `FieldOfNorms.algHomEquiv`: **Theorem 3.1.2.** For finite separable extensions `M`, `N` of the APF
  extension `L/K`, the field of norms is fully faithful: `Hom_L(M, N) ≃ Hom_{X_K(L)}(X_K(M),
  X_K(N))`.

## Main results

* `moduleFinite_relativeEmbedding_fieldRange`: Finiteness of the target over the common base
  produces finiteness over the image of every relative embedding.
* `isSeparable_relativeEmbedding_fieldRange`: Separability of the target produces separability over
  the same image of every relative embedding.
* `FieldOfNorms.mapEquiv_fixes_inclusion_iff`: The action reflects the intermediate-field
  stabilizer.
* `FieldOfNorms.mapEquiv_eq_on_inclusion_iff`: Equality of the norm-field restrictions reflects
  equality of restrictions on the intermediate field.
* `FieldOfNorms.mapAlgHom_eq_of_extend`: Extending an embedding to a Galois automorphism gives
  exactly the map on norm families, rather than a separate Hom map.
* `FieldOfNorms.mapAlgHom_injective_of_isGalois`: The finite Hom map is faithful inside a common
  finite Galois overfield.
* `FieldOfNorms.mapAlgHom_surjective_of_isGalois`: Every norm-field embedding into the Galois norm
  field comes from an embedding, by extending to a norm-field automorphism.
* `FieldOfNorms.mapAlgHom_postcomp_aut`: Automorphisms act on the finite Hom map by composition.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section RelativeEmbeddings

variable (K L : Type*) {M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L M] [Algebra L N]
    [IsScalarTower K L M] [IsScalarTower K L N] [Module.Finite L N]

/-- Finiteness of the target over the common base produces
finiteness over the image of every relative embedding. -/
theorem moduleFinite_relativeEmbedding_fieldRange (φ : M →ₐ[L] N) :
    Module.Finite (φ.restrictScalars K).fieldRange N := by
  let τ := φ.restrictScalars K
  let : Algebra M N := τ.toRingHom.toAlgebra
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun l => (φ.commutes l).symm)
  let : Module.Finite M N := Module.Finite.right L M N
  have hτ : τ = IsScalarTower.toAlgHom K M N := by ext m; rfl
  change Module.Finite τ.fieldRange N
  rw [hτ]
  exact moduleFinite_algebraMap_fieldRange K M N

omit [Module.Finite L N] in
/-- Separability of the target produces separability over the
same image of every relative embedding. -/
theorem isSeparable_relativeEmbedding_fieldRange [Algebra.IsSeparable K N]
    (φ : M →ₐ[L] N) : Algebra.IsSeparable (φ.restrictScalars K).fieldRange N := by
  let τ := φ.restrictScalars K
  let : Algebra M N := τ.toRingHom.toAlgebra
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
  have hτ : τ = IsScalarTower.toAlgHom K M N := by ext m; rfl
  change Algebra.IsSeparable τ.fieldRange N
  rw [hτ]
  exact isSeparable_algebraMap_fieldRange K M N

end RelativeEmbeddings

variable (K L M N : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field L] [Field M] [Field N] [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N] [IsScalarTower K M N]
    [IsScalarTower L M N] [Algebra.IsSeparable K M] [Algebra.IsSeparable K N]
    [Module.Finite L N] [IsGalois L N]

local notation "p" => residueChar K

omit [IsScalarTower K L M] in
/-- The action reflects the intermediate-field stabilizer.
The reverse inclusion uses the full proved relative Galois equivalence. -/
theorem FieldOfNorms.mapEquiv_fixes_inclusion_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : FieldOfNorms K M,
      FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x) =
        FieldOfNorms.inclusion K M N x) ↔
      ∀ m : M, σ (algebraMap M N m) = algebraMap M N m := by
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  constructor
  · intro hσ
    let := (FieldOfNorms.inclusion K M N).toAlgebra
    let σX : FieldOfNorms K N ≃ₐ[FieldOfNorms K M] FieldOfNorms K N :=
      { FieldOfNorms.aut K N (σ.restrictScalars K) with
        commutes' := hσ }
    let τ := (FieldOfNorms.autEquiv K M N).symm σX
    have hτ := (FieldOfNorms.autEquiv K M N
).apply_symm_apply σX
    have hστ : σ.restrictScalars K = τ.restrictScalars K := by
      apply FieldOfNorms.aut_injective K N
      apply RingEquiv.ext
      intro x
      exact (congrArg (fun f => f x) hτ).symm
    intro m
    exact (congrArg (fun f : N ≃ₐ[K] N => f (algebraMap M N m)) hστ).trans
      (τ.commutes m)
  · intro hσ
    let τ : N ≃ₐ[M] N := { σ.toRingEquiv with commutes' := hσ }
    exact FieldOfNorms.mapEquiv_restrictScalars_inclusion K M N τ

omit [IsScalarTower K L M] in
/-- Equality of the norm-field restrictions reflects equality of
restrictions on the intermediate field. -/
theorem FieldOfNorms.mapEquiv_eq_on_inclusion_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ τ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : FieldOfNorms K M,
      FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x) =
        FieldOfNorms.mapEquiv (τ.restrictScalars K) (FieldOfNorms.inclusion K M N x)) ↔
      ∀ m : M, σ (algebraMap M N m) = τ (algebraMap M N m) := by
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  have he : ((σ.trans τ.symm).restrictScalars K) =
      (σ.restrictScalars K).trans (τ.restrictScalars K).symm := rfl
  have hfield : (∀ m : M, σ (algebraMap M N m) = τ (algebraMap M N m)) ↔
      ∀ m : M, (σ.trans τ.symm) (algebraMap M N m) = algebraMap M N m := by
    constructor
    · intro h m
      simpa only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using
        congrArg τ.symm (h m)
    · intro h m
      apply τ.symm.injective
      simpa only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using h m
  rw [hfield, ← FieldOfNorms.mapEquiv_fixes_inclusion_iff K L M N
    (σ.trans τ.symm)]
  constructor
  · intro h x
    rw [he, ← FieldOfNorms.mapEquiv_trans, h x, FieldOfNorms.mapEquiv_symm_apply]
  · intro h x
    apply (FieldOfNorms.mapEquiv (τ.restrictScalars K).symm).injective
    change FieldOfNorms.mapEquiv (τ.restrictScalars K).symm
        (FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x)) =
      FieldOfNorms.mapEquiv (τ.restrictScalars K).symm
        (FieldOfNorms.mapEquiv (τ.restrictScalars K) (FieldOfNorms.inclusion K M N x))
    rw [FieldOfNorms.mapEquiv_trans, ← he, h x, FieldOfNorms.mapEquiv_symm_apply]

/-- The map on relative finite embeddings is an algebra homomorphism
for the norm field, by the embedding composition law. -/
def FieldOfNorms.mapAlgHom [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    FieldOfNorms K M →ₐ[FieldOfNorms K L] FieldOfNorms K N := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let τ := φ.restrictScalars K
  let : Module.Finite τ.fieldRange N := moduleFinite_relativeEmbedding_fieldRange K L φ
  let : Algebra.IsSeparable τ.fieldRange N := isSeparable_relativeEmbedding_fieldRange K L φ
  refine { FieldOfNorms.map τ with
    commutes' := ?_ }
  intro x
  let ι := IsScalarTower.toAlgHom K L M
  let := moduleFinite_algebraMap_fieldRange K L M
  let := isSeparable_algebraMap_fieldRange K L M
  let := moduleFinite_algebraMap_fieldRange K L N
  let := isSeparable_algebraMap_fieldRange K L N
  have hc : τ.comp ι = IsScalarTower.toAlgHom K L N := by
    ext l
    exact φ.commutes l
  let := moduleFinite_comp_fieldRange K ι τ
  let := isSeparable_comp_fieldRange K ι τ
  change FieldOfNorms.map τ (FieldOfNorms.inclusion K L M x) =
    FieldOfNorms.inclusion K L N x
  calc
    _ = FieldOfNorms.map τ (FieldOfNorms.map ι x) :=
      congrArg (FieldOfNorms.map τ)
        (FieldOfNorms.map_toAlgHom L M x).symm
    _ = FieldOfNorms.map (τ.comp ι) x :=
      FieldOfNorms.map_map ι τ x
    _ = FieldOfNorms.map (IsScalarTower.toAlgHom K L N) x :=
      FieldOfNorms.map_congr hc x
    _ = FieldOfNorms.inclusion K L N x := FieldOfNorms.map_toAlgHom L N x

/-- Extending an embedding to a Galois automorphism gives
exactly the map on norm families, rather than a separate Hom map. -/
theorem FieldOfNorms.mapAlgHom_eq_of_extend [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (hσ : ∀ m : M, σ (algebraMap M N m) = φ m) (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    FieldOfNorms.mapAlgHom K L M N φ x =
      FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  let τ := φ.restrictScalars K
  let s := σ.restrictScalars K
  let ι := IsScalarTower.toAlgHom K M N
  let := moduleFinite_relativeEmbedding_fieldRange K L φ
  let := isSeparable_relativeEmbedding_fieldRange K L φ
  let := moduleFinite_algebraMap_fieldRange K M N
  let := isSeparable_algebraMap_fieldRange K M N
  let := moduleFinite_algEquiv_fieldRange K s
  let := isSeparable_algEquiv_fieldRange K s
  let := moduleFinite_comp_fieldRange K ι s.toAlgHom
  let := isSeparable_comp_fieldRange K ι s.toAlgHom
  have hc : s.toAlgHom.comp ι = τ := by ext m; exact hσ m
  change FieldOfNorms.map τ x = _
  calc
    _ = FieldOfNorms.map (s.toAlgHom.comp ι) x :=
      FieldOfNorms.map_congr hc.symm x
    _ = FieldOfNorms.map s.toAlgHom (FieldOfNorms.map ι x) :=
      (FieldOfNorms.map_map ι s.toAlgHom x).symm
    _ = FieldOfNorms.mapEquiv s (FieldOfNorms.inclusion K M N x) := by
      rw [FieldOfNorms.map_algEquiv, FieldOfNorms.map_toAlgHom]

/-- The finite Hom map is faithful inside a common finite Galois overfield. -/
theorem FieldOfNorms.mapAlgHom_injective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Injective
      (FieldOfNorms.mapAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  intro φ ψ hφψ
  let σ : N ≃ₐ[L] N := AlgEquiv.ofBijective (φ.liftNormal N)
    (AlgHom.normal_bijective L N N _)
  let τ : N ≃ₐ[L] N := AlgEquiv.ofBijective (ψ.liftNormal N)
    (AlgHom.normal_bijective L N N _)
  have hσ (m : M) : σ (algebraMap M N m) = φ m := by
    simpa only [σ, AlgEquiv.coe_ofBijective, Algebra.algebraMap_self, RingHom.id_apply] using
      φ.liftNormal_commutes N m
  have hτ (m : M) : τ (algebraMap M N m) = ψ m := by
    simpa only [τ, AlgEquiv.coe_ofBijective, Algebra.algebraMap_self, RingHom.id_apply] using
      ψ.liftNormal_commutes N m
  have hnorm (x : FieldOfNorms K M) :
      FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x) =
        FieldOfNorms.mapEquiv (τ.restrictScalars K) (FieldOfNorms.inclusion K M N x) :=
    (FieldOfNorms.mapAlgHom_eq_of_extend K L M N
      φ σ hσ x).symm.trans ((AlgHom.congr_fun hφψ x).trans
        (FieldOfNorms.mapAlgHom_eq_of_extend K L M N
          ψ τ hτ x))
  have horig := (FieldOfNorms.mapEquiv_eq_on_inclusion_iff K L M N
    σ τ).mp hnorm
  exact AlgHom.ext (fun m => (hσ m).symm.trans ((horig m).trans (hτ m)))

/-- Every norm-field embedding into the Galois norm field comes
from an embedding, by extending to a norm-field automorphism. -/
theorem FieldOfNorms.mapAlgHom_surjective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Surjective
      (FieldOfNorms.mapAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  let := (FieldOfNorms.inclusion K M N).toAlgebra
  let : IsScalarTower (FieldOfNorms K L) (FieldOfNorms K M) (FieldOfNorms K N) :=
    FieldOfNorms.inclusion_isScalarTower K L M N
  let : IsGalois (FieldOfNorms K L) (FieldOfNorms K N) :=
    FieldOfNorms.isGalois K L N
  intro f
  let g : FieldOfNorms K N ≃ₐ[FieldOfNorms K L] FieldOfNorms K N :=
    AlgEquiv.ofBijective (f.liftNormal (FieldOfNorms K N))
      (AlgHom.normal_bijective (FieldOfNorms K L) (FieldOfNorms K N) (FieldOfNorms K N) _)
  let σ := (FieldOfNorms.autEquiv K L N).symm g
  let φ : M →ₐ[L] N := σ.toAlgHom.comp (IsScalarTower.toAlgHom L M N)
  refine ⟨φ, AlgHom.ext (fun x => ?_)⟩
  rw [FieldOfNorms.mapAlgHom_eq_of_extend K L M N
    φ σ (fun _ => rfl)]
  have hσg := (FieldOfNorms.autEquiv K L N
).apply_symm_apply g
  have hg : FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K M N x) =
      g (FieldOfNorms.inclusion K M N x) :=
    congrArg (fun e => e (FieldOfNorms.inclusion K M N x)) hσg
  rw [hg]
  change f.liftNormal (FieldOfNorms K N)
    (algebraMap (FieldOfNorms K M) (FieldOfNorms K N) x) = f x
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    f.liftNormal_commutes (FieldOfNorms K N) x

omit [Algebra M N] [IsScalarTower K M N] [IsScalarTower L M N] [IsGalois L N] in
/-- Automorphisms act on the finite Hom map by composition. -/
theorem FieldOfNorms.mapAlgHom_postcomp_aut [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    FieldOfNorms.mapAlgHom K L M N
        (σ.toAlgHom.comp φ) x =
      FieldOfNorms.mapEquiv (σ.restrictScalars K)
        (FieldOfNorms.mapAlgHom K L M N φ x) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let τ := φ.restrictScalars K
  let s := σ.restrictScalars K
  let ψ := σ.toAlgHom.comp φ
  let := moduleFinite_relativeEmbedding_fieldRange K L φ
  let := isSeparable_relativeEmbedding_fieldRange K L φ
  let := moduleFinite_relativeEmbedding_fieldRange K L ψ
  let := isSeparable_relativeEmbedding_fieldRange K L ψ
  let := moduleFinite_algEquiv_fieldRange K s
  let := isSeparable_algEquiv_fieldRange K s
  let := moduleFinite_comp_fieldRange K τ s.toAlgHom
  let := isSeparable_comp_fieldRange K τ s.toAlgHom
  have hc : s.toAlgHom.comp τ = ψ.restrictScalars K := rfl
  change FieldOfNorms.map (ψ.restrictScalars K) x =
    FieldOfNorms.mapEquiv s (FieldOfNorms.map τ x)
  calc
    _ = FieldOfNorms.map (s.toAlgHom.comp τ) x :=
      FieldOfNorms.map_congr hc.symm x
    _ = FieldOfNorms.map s.toAlgHom (FieldOfNorms.map τ x) :=
      (FieldOfNorms.map_map τ s.toAlgHom x).symm
    _ = FieldOfNorms.mapEquiv s (FieldOfNorms.map τ x) :=
      FieldOfNorms.map_algEquiv s _

/-- The finite Hom correspondence inside a common finite Galois
overfield is bijective. -/
theorem FieldOfNorms.mapAlgHom_bijective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Bijective
      (FieldOfNorms.mapAlgHom K L M N) :=
  ⟨FieldOfNorms.mapAlgHom_injective_of_isGalois K L M N
,
    FieldOfNorms.mapAlgHom_surjective_of_isGalois K L M N
⟩

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

/-- Original Galois fixed fields factor an embedding through the
intermediate field, using its canonical image equivalence. -/
theorem exists_algHom_factor_of_fixed
    {F A B C : Type*} [Field F] [Field A] [Field B] [Field C]
    [Algebra F A] [Algebra F B] [Algebra F C] [Algebra B C]
    [IsScalarTower F B C] [FiniteDimensional B C] [IsGalois B C] (φ : A →ₐ[F] C)
    (hfixed : ∀ σ : C ≃ₐ[B] C, ∀ a : A, σ (φ a) = φ a) :
    ∃ ψ : A →ₐ[F] B, (IsScalarTower.toAlgHom F B C).comp ψ = φ := by
  let ι := IsScalarTower.toAlgHom F B C
  have hmem (a : A) : φ a ∈ ι.fieldRange :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := B) (φ a)).mpr
      (fun σ => hfixed σ a)
  let φ' : A →ₐ[F] ι.fieldRange := φ.codRestrict ι.fieldRange.toSubalgebra hmem
  let ψ := ι.equivFieldRange.symm.toAlgHom.comp φ'
  refine ⟨ψ, AlgHom.ext (fun a => ?_)⟩
  exact congrArg Subtype.val (ι.equivFieldRange.apply_symm_apply (φ' a))

/-- Two finite separable fields embed in one finite Galois
subfield of their common canonical separable closure. -/
theorem exists_common_finiteGalois_embeddings
    (F A B : Type*) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]
    [FiniteDimensional F A] [FiniteDimensional F B]
    [Algebra.IsSeparable F A] [Algebra.IsSeparable F B] :
    ∃ P : FiniteGaloisIntermediateField F (SeparableClosure F),
      Nonempty (A →ₐ[F] P) ∧ Nonempty (B →ₐ[F] P) := by
  let i : A →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let j : B →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let D := i.fieldRange ⊔ j.fieldRange
  let : FiniteDimensional F i.fieldRange := i.toLinearMap.finiteDimensional_range
  let : FiniteDimensional F j.fieldRange := j.toLinearMap.finiteDimensional_range
  let : FiniteDimensional F D := inferInstance
  let P := finiteGaloisNormalClosure F D
  have hi (a : A) : i a ∈ P.toIntermediateField :=
    le_finiteGaloisNormalClosure F D ((show i.fieldRange ≤ D from le_sup_left) (⟨a, rfl⟩ : i a ∈
        i.fieldRange))
  have hj (b : B) : j b ∈ P.toIntermediateField :=
    le_finiteGaloisNormalClosure F D ((show j.fieldRange ≤ D from le_sup_right) (⟨b, rfl⟩ : j b ∈
        j.fieldRange))
  exact ⟨P, ⟨i.codRestrict P.toIntermediateField.toSubalgebra hi⟩,
    ⟨j.codRestrict P.toIntermediateField.toSubalgebra hj⟩⟩

variable (K L M N P : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field L] [Field M] [Field N] [Field P]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra L M] [Algebra L N] [Algebra L P]
    [IsScalarTower K L M] [IsScalarTower K L N] [IsScalarTower K L P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Algebra.IsSeparable K P]
    [Module.Finite L M] [Module.Finite L N] [Module.Finite L P]

local notation "p" => residueChar K

/-- Composition on relative finite Hom sets is the norm-family
composition theorem with its image-field scalar structures. -/
theorem FieldOfNorms.mapAlgHom_comp
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)]
    (φ : M →ₐ[L] N) (ψ : N →ₐ[L] P) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    letI := (FieldOfNorms.inclusion K L P).toAlgebra
    FieldOfNorms.mapAlgHom K L M P (ψ.comp φ) =
      (FieldOfNorms.mapAlgHom K L N P ψ).comp
        (FieldOfNorms.mapAlgHom K L M N φ) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let := (FieldOfNorms.inclusion K L P).toAlgebra
  let τ := φ.restrictScalars K
  let σ := ψ.restrictScalars K
  let ξ := (ψ.comp φ).restrictScalars K
  let := moduleFinite_relativeEmbedding_fieldRange K L φ
  let := isSeparable_relativeEmbedding_fieldRange K L φ
  let := moduleFinite_relativeEmbedding_fieldRange K L ψ
  let := isSeparable_relativeEmbedding_fieldRange K L ψ
  let := moduleFinite_relativeEmbedding_fieldRange K L (ψ.comp φ)
  let := isSeparable_relativeEmbedding_fieldRange K L (ψ.comp φ)
  let := moduleFinite_comp_fieldRange K τ σ
  let := isSeparable_comp_fieldRange K τ σ
  have hc : σ.comp τ = ξ := rfl
  apply AlgHom.ext
  intro x
  change FieldOfNorms.map ξ x =
    FieldOfNorms.map σ (FieldOfNorms.map τ x)
  exact (FieldOfNorms.map_congr hc.symm x).trans
    (FieldOfNorms.map_map τ σ x).symm

/-- On inclusions the relative Hom map is the same
finite-inclusion norm-family map. -/
theorem FieldOfNorms.mapAlgHom_algebraMap
    [Algebra M N] [IsScalarTower K M N] [IsScalarTower L M N]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    FieldOfNorms.mapAlgHom K L M N
      (IsScalarTower.toAlgHom L M N) x = FieldOfNorms.inclusion K M N x := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
  let := moduleFinite_algebraMap_fieldRange K M N
  let := isSeparable_algebraMap_fieldRange K M N
  change FieldOfNorms.map (IsScalarTower.toAlgHom K M N) x = _
  exact FieldOfNorms.map_toAlgHom M N x

/-- The finite Hom map is injective for two subextensions
of one finite Galois overfield. -/
theorem FieldOfNorms.mapAlgHom_injective_of_isGalois_top
    [Algebra M P] [Algebra N P] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower L M P] [IsScalarTower L N P] [IsGalois L P]
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Injective
      (FieldOfNorms.mapAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let := (FieldOfNorms.inclusion K L P).toAlgebra
  intro φ ψ hφψ
  let ι := IsScalarTower.toAlgHom L N P
  have hcomp :
      FieldOfNorms.mapAlgHom K L M P (ι.comp φ) =
        FieldOfNorms.mapAlgHom K L M P (ι.comp ψ) := by
    rw [FieldOfNorms.mapAlgHom_comp K L M N P
      φ ι,
      FieldOfNorms.mapAlgHom_comp K L M N P
        ψ ι, hφψ]
  have h := FieldOfNorms.mapAlgHom_injective_of_isGalois K L M P
    hcomp
  apply AlgHom.ext
  intro m
  exact (algebraMap N P).injective (AlgHom.congr_fun h m)

/-- Galois fixed-field factorization gives fullness for two
subextensions of the same finite Galois overfield. -/
theorem FieldOfNorms.mapAlgHom_surjective_of_isGalois_top
    [Algebra M P] [Algebra N P] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower L M P] [IsScalarTower L N P] [IsGalois L P]
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Surjective
      (FieldOfNorms.mapAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  let := (FieldOfNorms.inclusion K L P).toAlgebra
  let : Module.Finite N P := Module.Finite.right L N P
  let : IsGalois N P := IsGalois.tower_top_of_isGalois L N P
  intro f
  let ι := IsScalarTower.toAlgHom L N P
  let ιX := FieldOfNorms.mapAlgHom K L N P
    ι
  obtain ⟨φ, hφ⟩ := FieldOfNorms.mapAlgHom_surjective_of_isGalois K L M P
    (ιX.comp f)
  have hfixed (σ : P ≃ₐ[N] P) (m : M) : σ (φ m) = φ m := by
    let τ := σ.restrictScalars L
    have hnorm :
        FieldOfNorms.mapAlgHom K L M P
          (τ.toAlgHom.comp φ) =
        FieldOfNorms.mapAlgHom K L M P φ := by
      apply AlgHom.ext
      intro x
      rw [FieldOfNorms.mapAlgHom_postcomp_aut K L M P
        φ τ x]
      calc
        _ = FieldOfNorms.mapEquiv (σ.restrictScalars K) (ιX (f x)) :=
          congrArg (FieldOfNorms.mapEquiv (σ.restrictScalars K)) (AlgHom.congr_fun hφ x)
        _ = FieldOfNorms.mapEquiv (σ.restrictScalars K) (FieldOfNorms.inclusion K N P (f x)) :=
          congrArg (FieldOfNorms.mapEquiv (σ.restrictScalars K))
            (FieldOfNorms.mapAlgHom_algebraMap K L N P
              (f x))
        _ = FieldOfNorms.inclusion K N P (f x) :=
          FieldOfNorms.mapEquiv_restrictScalars_inclusion K N P σ (f x)
        _ = ιX (f x) := (FieldOfNorms.mapAlgHom_algebraMap K L N P
          (f x)).symm
        _ = _ := (AlgHom.congr_fun hφ x).symm
    have h := FieldOfNorms.mapAlgHom_injective_of_isGalois K L M P
      hnorm
    exact AlgHom.congr_fun h m
  obtain ⟨ψ, hψ⟩ := exists_algHom_factor_of_fixed φ hfixed
  refine ⟨ψ, AlgHom.ext (fun x => ?_)⟩
  apply ιX.injective
  have hc := AlgHom.congr_fun (FieldOfNorms.mapAlgHom_comp K L M N P
    ψ ι) x
  exact hc.symm.trans ((congrArg (fun g =>
    FieldOfNorms.mapAlgHom K L M P g x)
      hψ).trans (AlgHom.congr_fun hφ x))

/-- Full faithfulness of the finite Hom map for arbitrary finite
separable extensions, with no normality assumption on either field. -/
theorem FieldOfNorms.mapAlgHom_bijective
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    Function.Bijective
      (FieldOfNorms.mapAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  obtain ⟨P, ⟨ιM⟩, ⟨ιN⟩⟩ := exists_common_finiteGalois_embeddings L M N
  let : Algebra K P := ((algebraMap L P).comp (algebraMap K L)).toAlgebra
  let : Module K P := Algebra.toModule
  let : IsScalarTower K L P := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra M P := ιM.toRingHom.toAlgebra
  let : Algebra N P := ιN.toRingHom.toAlgebra
  let : IsScalarTower L M P := IsScalarTower.of_algebraMap_eq (fun l => (ιM.commutes l).symm)
  let : IsScalarTower L N P := IsScalarTower.of_algebraMap_eq (fun l => (ιN.commutes l).symm)
  let : IsScalarTower K M P := IsScalarTower.of_algebraMap_eq
    (fun k => ((ιM.restrictScalars K).commutes k).symm)
  let : IsScalarTower K N P := IsScalarTower.of_algebraMap_eq
    (fun k => ((ιN.restrictScalars K).commutes k).symm)
  let : Algebra.IsSeparable K P := Algebra.IsSeparable.trans K L P
  have hP : IsAPF K P := (isAPF_finite_extension_iff K P L).mpr ‹_›
  have hInfiniteP : ¬ Module.Finite K P := by
    intro h
    let : Module.Finite K P := h
    exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom K L P).toLinearMap (algebraMap L P).injective)
  have : Fact (¬ Module.Finite K P) := ⟨hInfiniteP⟩
  exact ⟨FieldOfNorms.mapAlgHom_injective_of_isGalois_top K L M N P
,
    FieldOfNorms.mapAlgHom_surjective_of_isGalois_top K L M N P
⟩

/-- **Theorem 3.1.2.** For finite separable extensions `M`, `N` of the APF extension `L/K`, the
field of norms is fully faithful: `Hom_L(M, N) ≃ Hom_{X_K(L)}(X_K(M), X_K(N))`. -/
def FieldOfNorms.algHomEquiv [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    let hM : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    let hN : IsAPF K N := (isAPF_finite_extension_iff K N L).mpr ‹_›
    have hInfiniteM : ¬ Module.Finite K M := by
      intro h
      let : Module.Finite K M := h
      exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
        (IsScalarTower.toAlgHom K L M).toLinearMap (algebraMap L M).injective)
    haveI : Fact (¬ Module.Finite K M) := ⟨hInfiniteM⟩
    have hInfiniteN : ¬ Module.Finite K N := by
      intro h
      let : Module.Finite K N := h
      exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
        (IsScalarTower.toAlgHom K L N).toLinearMap (algebraMap L N).injective)
    haveI : Fact (¬ Module.Finite K N) := ⟨hInfiniteN⟩
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.inclusion K L M).toAlgebra
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    (M →ₐ[L] N) ≃ (FieldOfNorms K M →ₐ[FieldOfNorms K L] FieldOfNorms K N) := by
  haveI hM : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  haveI hN : IsAPF K N := (isAPF_finite_extension_iff K N L).mpr ‹_›
  have hInfiniteM : ¬ Module.Finite K M := by
    intro h
    let : Module.Finite K M := h
    exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom K L M).toLinearMap (algebraMap L M).injective)
  haveI : Fact (¬ Module.Finite K M) := ⟨hInfiniteM⟩
  have hInfiniteN : ¬ Module.Finite K N := by
    intro h
    let : Module.Finite K N := h
    exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom K L N).toLinearMap (algebraMap L N).injective)
  haveI : Fact (¬ Module.Finite K N) := ⟨hInfiniteN⟩
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.inclusion K L M).toAlgebra
  let := (FieldOfNorms.inclusion K L N).toAlgebra
  exact Equiv.ofBijective
    (FieldOfNorms.mapAlgHom K L M N)
    (FieldOfNorms.mapAlgHom_bijective K L M N)

end FontaineWintenberger
