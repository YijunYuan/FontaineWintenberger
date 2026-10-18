/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteEmbeddingGalois
public import FontaineWintenberger.Algebra.SeparableEmbeddings

/-!
# Full faithfulness for original finite separable norm-field maps

The actual relative Galois equivalences and their original-family formulas
reflect stabilizers. Extending actual embeddings to a common finite Galois
overfield then gives the full finite Hom correspondence.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section RelativeEmbeddings

variable (K L : Type*) {M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L M] [Algebra L N]
    [IsScalarTower K L M] [IsScalarTower K L N] [Module.Finite L N]

/-- Finiteness of the original target over the common base produces
finiteness over the actual image of every relative embedding. -/
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
/-- Separability of the original target produces separability over the
same actual image of every relative embedding. -/
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
/-- The original action reflects the actual intermediate-field stabilizer.
The reverse inclusion uses the full proved relative Galois equivalence. -/
theorem FieldOfNorms.map_fixes_finiteFieldOfNormsMap_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : FieldOfNorms K M,
      FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) =
        FieldOfNorms.finiteMap K M N x) ↔
      ∀ m : M, σ (algebraMap M N m) = algebraMap M N m := by
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  constructor
  · intro hσ
    let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    let σX : FieldOfNorms K N ≃ₐ[FieldOfNorms K M] FieldOfNorms K N :=
      { FieldOfNorms.aut K N (σ.restrictScalars K) with
        commutes' := hσ }
    let τ := (FieldOfNorms.finiteGaloisEquiv K M N).symm σX
    have hτ := (FieldOfNorms.finiteGaloisEquiv K M N
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
    exact FieldOfNorms.map_finiteFieldOfNormsMap_relative K M N τ

omit [IsScalarTower K L M] in
/-- Equality of the original norm-field restrictions reflects equality of
restrictions on the original intermediate field. -/
theorem FieldOfNorms.map_eq_on_finiteFieldOfNormsMap_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ τ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : FieldOfNorms K M,
      FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) =
        FieldOfNorms.map (τ.restrictScalars K) (FieldOfNorms.finiteMap K M N x)) ↔
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
  rw [hfield, ← FieldOfNorms.map_fixes_finiteFieldOfNormsMap_iff K L M N
    (σ.trans τ.symm)]
  constructor
  · intro h x
    rw [he, ← FieldOfNorms.map_trans, h x, FieldOfNorms.map_symm_apply]
  · intro h x
    apply (FieldOfNorms.mulEquiv (τ.restrictScalars K).symm).injective
    change FieldOfNorms.map (τ.restrictScalars K).symm
        (FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x)) =
      FieldOfNorms.map (τ.restrictScalars K).symm
        (FieldOfNorms.map (τ.restrictScalars K) (FieldOfNorms.finiteMap K M N x))
    rw [FieldOfNorms.map_trans, ← he, h x, FieldOfNorms.map_symm_apply]

/-- The actual map on relative finite embeddings is an algebra homomorphism
for the original source norm field, by the original embedding composition law. -/
def FieldOfNorms.finiteAlgHom [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    FieldOfNorms K M →ₐ[FieldOfNorms K L] FieldOfNorms K N := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let τ := φ.restrictScalars K
  let : Module.Finite τ.fieldRange N := moduleFinite_relativeEmbedding_fieldRange K L φ
  let : Algebra.IsSeparable τ.fieldRange N := isSeparable_relativeEmbedding_fieldRange K L φ
  refine { FieldOfNorms.finiteEmbeddingRingHom K τ with
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
  change FieldOfNorms.finiteEmbeddingMap K τ (FieldOfNorms.finiteMap K L M x) =
    FieldOfNorms.finiteMap K L N x
  calc
    _ = FieldOfNorms.finiteEmbeddingMap K τ (FieldOfNorms.finiteEmbeddingMap K ι x) :=
      congrArg (FieldOfNorms.finiteEmbeddingMap K τ)
        (FieldOfNorms.finiteEmbeddingMap_algebraMap K L M x).symm
    _ = FieldOfNorms.finiteEmbeddingMap K (τ.comp ι) x :=
      FieldOfNorms.finiteEmbeddingMap_trans K ι τ x
    _ = FieldOfNorms.finiteEmbeddingMap K (IsScalarTower.toAlgHom K L N) x :=
      FieldOfNorms.finiteEmbeddingMap_congr K hc x
    _ = FieldOfNorms.finiteMap K L N x := FieldOfNorms.finiteEmbeddingMap_algebraMap K L N x

/-- Extending a genuine original embedding to a Galois automorphism gives
exactly the original map on norm families, rather than a separate Hom map. -/
theorem FieldOfNorms.finiteAlgHom_eq_of_extend [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (hσ : ∀ m : M, σ (algebraMap M N m) = φ m) (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    FieldOfNorms.finiteAlgHom K L M N φ x =
      FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
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
  change FieldOfNorms.finiteEmbeddingMap K τ x = _
  calc
    _ = FieldOfNorms.finiteEmbeddingMap K (s.toAlgHom.comp ι) x :=
      FieldOfNorms.finiteEmbeddingMap_congr K hc.symm x
    _ = FieldOfNorms.finiteEmbeddingMap K s.toAlgHom (FieldOfNorms.finiteEmbeddingMap K ι x) :=
      (FieldOfNorms.finiteEmbeddingMap_trans K ι s.toAlgHom x).symm
    _ = FieldOfNorms.map s (FieldOfNorms.finiteMap K M N x) := by
      rw [FieldOfNorms.finiteEmbeddingMap_algEquiv, FieldOfNorms.finiteEmbeddingMap_algebraMap]

/-- The original finite Hom map is faithful inside a common finite Galois overfield. -/
theorem FieldOfNorms.finiteAlgHom_injective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Injective
      (FieldOfNorms.finiteAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
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
      FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) =
        FieldOfNorms.map (τ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) :=
    (FieldOfNorms.finiteAlgHom_eq_of_extend K L M N
      φ σ hσ x).symm.trans ((AlgHom.congr_fun hφψ x).trans
        (FieldOfNorms.finiteAlgHom_eq_of_extend K L M N
          ψ τ hτ x))
  have horig := (FieldOfNorms.map_eq_on_finiteFieldOfNormsMap_iff K L M N
    σ τ).mp hnorm
  exact AlgHom.ext (fun m => (hσ m).symm.trans ((horig m).trans (hτ m)))

/-- Every norm-field embedding into the original Galois norm field comes
from an original embedding, by extending to an actual norm-field automorphism. -/
theorem FieldOfNorms.finiteAlgHom_surjective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Surjective
      (FieldOfNorms.finiteAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let : IsScalarTower (FieldOfNorms K L) (FieldOfNorms K M) (FieldOfNorms K N) :=
    FieldOfNorms.finiteRingHom_isScalarTower K L M N
  let : IsGalois (FieldOfNorms K L) (FieldOfNorms K N) :=
    isGalois_finiteFieldOfNorms K L N
  intro f
  let g : FieldOfNorms K N ≃ₐ[FieldOfNorms K L] FieldOfNorms K N :=
    AlgEquiv.ofBijective (f.liftNormal (FieldOfNorms K N))
      (AlgHom.normal_bijective (FieldOfNorms K L) (FieldOfNorms K N) (FieldOfNorms K N) _)
  let σ := (FieldOfNorms.finiteGaloisEquiv K L N).symm g
  let φ : M →ₐ[L] N := σ.toAlgHom.comp (IsScalarTower.toAlgHom L M N)
  refine ⟨φ, AlgHom.ext (fun x => ?_)⟩
  rw [FieldOfNorms.finiteAlgHom_eq_of_extend K L M N
    φ σ (fun _ => rfl)]
  have hσg := (FieldOfNorms.finiteGaloisEquiv K L N
).apply_symm_apply g
  have hg : FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N x) =
      g (FieldOfNorms.finiteMap K M N x) :=
    congrArg (fun e => e (FieldOfNorms.finiteMap K M N x)) hσg
  rw [hg]
  change f.liftNormal (FieldOfNorms K N)
    (algebraMap (FieldOfNorms K M) (FieldOfNorms K N) x) = f x
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    f.liftNormal_commutes (FieldOfNorms K N) x

omit [Algebra M N] [IsScalarTower K M N] [IsScalarTower L M N] [IsGalois L N] in
/-- Original automorphisms act on the actual finite Hom map by composition. -/
theorem FieldOfNorms.finiteAlgHom_postcomp_aut [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    FieldOfNorms.finiteAlgHom K L M N
        (σ.toAlgHom.comp φ) x =
      FieldOfNorms.map (σ.restrictScalars K)
        (FieldOfNorms.finiteAlgHom K L M N φ x) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
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
  change FieldOfNorms.finiteEmbeddingMap K (ψ.restrictScalars K) x =
    FieldOfNorms.map s (FieldOfNorms.finiteEmbeddingMap K τ x)
  calc
    _ = FieldOfNorms.finiteEmbeddingMap K (s.toAlgHom.comp τ) x :=
      FieldOfNorms.finiteEmbeddingMap_congr K hc.symm x
    _ = FieldOfNorms.finiteEmbeddingMap K s.toAlgHom (FieldOfNorms.finiteEmbeddingMap K τ x) :=
      (FieldOfNorms.finiteEmbeddingMap_trans K τ s.toAlgHom x).symm
    _ = FieldOfNorms.map s (FieldOfNorms.finiteEmbeddingMap K τ x) :=
      FieldOfNorms.finiteEmbeddingMap_algEquiv K s _

/-- The actual finite Hom correspondence inside a common finite Galois
overfield is bijective. -/
theorem FieldOfNorms.finiteAlgHom_bijective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Bijective
      (FieldOfNorms.finiteAlgHom K L M N) :=
  ⟨FieldOfNorms.finiteAlgHom_injective_of_isGalois K L M N
,
    FieldOfNorms.finiteAlgHom_surjective_of_isGalois K L M N
⟩

end FontaineWintenberger
