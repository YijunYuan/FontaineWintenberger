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
theorem normLimitMap_fixes_finiteNormLimitMap_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : NormLimit K M,
      normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x) =
        finiteNormLimitMap K M N x) ↔
      ∀ m : M, σ (algebraMap M N m) = algebraMap M N m := by
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  constructor
  · intro hσ
    let := normLimitField K M
    let := normLimitField K N
    let := (finiteNormLimitRingHom K M N).toAlgebra
    let σX : NormLimit K N ≃ₐ[NormLimit K M] NormLimit K N :=
      { normLimitAut K N (σ.restrictScalars K) with
        commutes' := hσ }
    let τ := (finiteNormLimitGaloisEquiv K M N).symm σX
    have hτ := (finiteNormLimitGaloisEquiv K M N
).apply_symm_apply σX
    have hστ : σ.restrictScalars K = τ.restrictScalars K := by
      apply normLimitAut_injective K N
      apply RingEquiv.ext
      intro x
      exact (congrArg (fun f => f x) hτ).symm
    intro m
    exact (congrArg (fun f : N ≃ₐ[K] N => f (algebraMap M N m)) hστ).trans
      (τ.commutes m)
  · intro hσ
    let τ : N ≃ₐ[M] N := { σ.toRingEquiv with commutes' := hσ }
    exact normLimitMap_finiteNormLimitMap_relative K M N τ

omit [IsScalarTower K L M] in
/-- Equality of the original norm-field restrictions reflects equality of
restrictions on the original intermediate field. -/
theorem normLimitMap_eq_on_finiteNormLimitMap_iff
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ τ : N ≃ₐ[L] N) :
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    (∀ x : NormLimit K M,
      normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x) =
        normLimitMap (τ.restrictScalars K) (finiteNormLimitMap K M N x)) ↔
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
  rw [hfield, ← normLimitMap_fixes_finiteNormLimitMap_iff K L M N
    (σ.trans τ.symm)]
  constructor
  · intro h x
    rw [he, ← normLimitMap_trans, h x, normLimitMap_symm_apply]
  · intro h x
    apply (normLimitMulEquiv (τ.restrictScalars K).symm).injective
    change normLimitMap (τ.restrictScalars K).symm
        (normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x)) =
      normLimitMap (τ.restrictScalars K).symm
        (normLimitMap (τ.restrictScalars K) (finiteNormLimitMap K M N x))
    rw [normLimitMap_trans, ← he, h x, normLimitMap_symm_apply]

/-- The actual map on relative finite embeddings is an algebra homomorphism
for the original source norm field, by the original embedding composition law. -/
def finiteNormLimitAlgHom [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    NormLimit K M →ₐ[NormLimit K L] NormLimit K N := by
  let := normLimitField K L
  let := normLimitField K M
  let := normLimitField K N
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (finiteNormLimitRingHom K L M).toAlgebra
  let := (finiteNormLimitRingHom K L N).toAlgebra
  let τ := φ.restrictScalars K
  let : Module.Finite τ.fieldRange N := moduleFinite_relativeEmbedding_fieldRange K L φ
  let : Algebra.IsSeparable τ.fieldRange N := isSeparable_relativeEmbedding_fieldRange K L φ
  refine { finiteNormLimitEmbeddingRingHom K τ with
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
  change finiteNormLimitEmbeddingMap K τ (finiteNormLimitMap K L M x) =
    finiteNormLimitMap K L N x
  calc
    _ = finiteNormLimitEmbeddingMap K τ (finiteNormLimitEmbeddingMap K ι x) :=
      congrArg (finiteNormLimitEmbeddingMap K τ)
        (finiteNormLimitEmbeddingMap_algebraMap K L M x).symm
    _ = finiteNormLimitEmbeddingMap K (τ.comp ι) x :=
      finiteNormLimitEmbeddingMap_trans K ι τ x
    _ = finiteNormLimitEmbeddingMap K (IsScalarTower.toAlgHom K L N) x :=
      finiteNormLimitEmbeddingMap_congr K hc x
    _ = finiteNormLimitMap K L N x := finiteNormLimitEmbeddingMap_algebraMap K L N x

/-- Extending a genuine original embedding to a Galois automorphism gives
exactly the original map on norm families, rather than a separate Hom map. -/
theorem finiteNormLimitAlgHom_eq_of_extend [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (hσ : ∀ m : M, σ (algebraMap M N m) = φ m) (x : NormLimit K M) :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
    finiteNormLimitAlgHom K L M N φ x =
      normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x) := by
  let := normLimitField K L
  let := normLimitField K M
  let := normLimitField K N
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (finiteNormLimitRingHom K L M).toAlgebra
  let := (finiteNormLimitRingHom K L N).toAlgebra
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
  change finiteNormLimitEmbeddingMap K τ x = _
  calc
    _ = finiteNormLimitEmbeddingMap K (s.toAlgHom.comp ι) x :=
      finiteNormLimitEmbeddingMap_congr K hc.symm x
    _ = finiteNormLimitEmbeddingMap K s.toAlgHom (finiteNormLimitEmbeddingMap K ι x) :=
      (finiteNormLimitEmbeddingMap_trans K ι s.toAlgHom x).symm
    _ = normLimitMap s (finiteNormLimitMap K M N x) := by
      rw [finiteNormLimitEmbeddingMap_algEquiv, finiteNormLimitEmbeddingMap_algebraMap]

/-- The original finite Hom map is faithful inside a common finite Galois overfield. -/
theorem finiteNormLimitAlgHom_injective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    Function.Injective
      (finiteNormLimitAlgHom K L M N) := by
  let := normLimitField K L
  let := normLimitField K M
  let := normLimitField K N
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (finiteNormLimitRingHom K L M).toAlgebra
  let := (finiteNormLimitRingHom K L N).toAlgebra
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
  have hnorm (x : NormLimit K M) :
      normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x) =
        normLimitMap (τ.restrictScalars K) (finiteNormLimitMap K M N x) :=
    (finiteNormLimitAlgHom_eq_of_extend K L M N
      φ σ hσ x).symm.trans ((AlgHom.congr_fun hφψ x).trans
        (finiteNormLimitAlgHom_eq_of_extend K L M N
          ψ τ hτ x))
  have horig := (normLimitMap_eq_on_finiteNormLimitMap_iff K L M N
    σ τ).mp hnorm
  exact AlgHom.ext (fun m => (hσ m).symm.trans ((horig m).trans (hτ m)))

/-- Every norm-field embedding into the original Galois norm field comes
from an original embedding, by extending to an actual norm-field automorphism. -/
theorem finiteNormLimitAlgHom_surjective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    Function.Surjective
      (finiteNormLimitAlgHom K L M N) := by
  let := normLimitField K L
  let := normLimitField K M
  let := normLimitField K N
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (finiteNormLimitRingHom K L M).toAlgebra
  let := (finiteNormLimitRingHom K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : IsGalois M N := IsGalois.tower_top_of_isGalois L M N
  let := (finiteNormLimitRingHom K M N).toAlgebra
  let : IsScalarTower (NormLimit K L) (NormLimit K M) (NormLimit K N) :=
    finiteNormLimitRingHom_isScalarTower K L M N
  let : IsGalois (NormLimit K L) (NormLimit K N) :=
    isGalois_finiteNormLimit K L N
  intro f
  let g : NormLimit K N ≃ₐ[NormLimit K L] NormLimit K N :=
    AlgEquiv.ofBijective (f.liftNormal (NormLimit K N))
      (AlgHom.normal_bijective (NormLimit K L) (NormLimit K N) (NormLimit K N) _)
  let σ := (finiteNormLimitGaloisEquiv K L N).symm g
  let φ : M →ₐ[L] N := σ.toAlgHom.comp (IsScalarTower.toAlgHom L M N)
  refine ⟨φ, AlgHom.ext (fun x => ?_)⟩
  rw [finiteNormLimitAlgHom_eq_of_extend K L M N
    φ σ (fun _ => rfl)]
  have hσg := (finiteNormLimitGaloisEquiv K L N
).apply_symm_apply g
  have hg : normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N x) =
      g (finiteNormLimitMap K M N x) :=
    congrArg (fun e => e (finiteNormLimitMap K M N x)) hσg
  rw [hg]
  change f.liftNormal (NormLimit K N)
    (algebraMap (NormLimit K M) (NormLimit K N) x) = f x
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    f.liftNormal_commutes (NormLimit K N) x

omit [Algebra M N] [IsScalarTower K M N] [IsScalarTower L M N] [IsGalois L N] in
/-- Original automorphisms act on the actual finite Hom map by composition. -/
theorem finiteNormLimitAlgHom_postcomp_aut [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (φ : M →ₐ[L] N) (σ : N ≃ₐ[L] N)
    (x : NormLimit K M) :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    finiteNormLimitAlgHom K L M N
        (σ.toAlgHom.comp φ) x =
      normLimitMap (σ.restrictScalars K)
        (finiteNormLimitAlgHom K L M N φ x) := by
  let := normLimitField K L
  let := normLimitField K M
  let := normLimitField K N
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (finiteNormLimitRingHom K L M).toAlgebra
  let := (finiteNormLimitRingHom K L N).toAlgebra
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
  change finiteNormLimitEmbeddingMap K (ψ.restrictScalars K) x =
    normLimitMap s (finiteNormLimitEmbeddingMap K τ x)
  calc
    _ = finiteNormLimitEmbeddingMap K (s.toAlgHom.comp τ) x :=
      finiteNormLimitEmbeddingMap_congr K hc.symm x
    _ = finiteNormLimitEmbeddingMap K s.toAlgHom (finiteNormLimitEmbeddingMap K τ x) :=
      (finiteNormLimitEmbeddingMap_trans K τ s.toAlgHom x).symm
    _ = normLimitMap s (finiteNormLimitEmbeddingMap K τ x) :=
      finiteNormLimitEmbeddingMap_algEquiv K s _

/-- The actual finite Hom correspondence inside a common finite Galois
overfield is bijective. -/
theorem finiteNormLimitAlgHom_bijective_of_isGalois
    [Algebra.IsSeparable K L] [Module.Finite L M]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI := normLimitField K L
    letI := normLimitField K M
    letI := normLimitField K N
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (finiteNormLimitRingHom K L M).toAlgebra
    letI := (finiteNormLimitRingHom K L N).toAlgebra
    Function.Bijective
      (finiteNormLimitAlgHom K L M N) :=
  ⟨finiteNormLimitAlgHom_injective_of_isGalois K L M N
,
    finiteNormLimitAlgHom_surjective_of_isGalois K L M N
⟩

end FontaineWintenberger
