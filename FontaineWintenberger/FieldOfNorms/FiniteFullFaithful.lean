/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.SeparableFullFaithful

/-!
# Full faithfulness of the original finite separable norm-field functor

Finite relative embeddings commute with composition. Inside an actual common
finite Galois overfield, the proved Galois Hom correspondence and original
fixed fields reflect factorization through each intermediate field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- Original Galois fixed fields factor an embedding through the actual
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

/-- Two actual finite separable fields embed in one actual finite Galois
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

/-- Composition on relative finite Hom sets is the original norm-family
composition theorem with its actual image-field scalar structures. -/
theorem FieldOfNorms.finiteAlgHom_comp
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)]
    (φ : M →ₐ[L] N) (ψ : N →ₐ[L] P) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L P).toAlgebra
    FieldOfNorms.finiteAlgHom K L M P (ψ.comp φ) =
      (FieldOfNorms.finiteAlgHom K L N P ψ).comp
        (FieldOfNorms.finiteAlgHom K L M N φ) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L P).toAlgebra
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
  change FieldOfNorms.finiteEmbeddingMap K ξ x =
    FieldOfNorms.finiteEmbeddingMap K σ (FieldOfNorms.finiteEmbeddingMap K τ x)
  exact (FieldOfNorms.finiteEmbeddingMap_congr K hc.symm x).trans
    (FieldOfNorms.finiteEmbeddingMap_trans K τ σ x).symm

/-- On original inclusions the relative Hom map is the same original
finite-inclusion norm-family map. -/
theorem FieldOfNorms.finiteAlgHom_algebraMap
    [Algebra M N] [IsScalarTower K M N] [IsScalarTower L M N]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] (x : FieldOfNorms K M) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    letI : Module.Finite M N := Module.Finite.right L M N
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    FieldOfNorms.finiteAlgHom K L M N
      (IsScalarTower.toAlgHom L M N) x = FieldOfNorms.finiteMap K M N x := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let : Module.Finite M N := Module.Finite.right L M N
  let : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
  let := moduleFinite_algebraMap_fieldRange K M N
  let := isSeparable_algebraMap_fieldRange K M N
  change FieldOfNorms.finiteEmbeddingMap K (IsScalarTower.toAlgHom K M N) x = _
  exact FieldOfNorms.finiteEmbeddingMap_algebraMap K M N x

/-- The actual finite Hom map is injective for two original subextensions
of one genuine finite Galois overfield. -/
theorem FieldOfNorms.finiteAlgHom_injective_in_galoisOverfield
    [Algebra M P] [Algebra N P] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower L M P] [IsScalarTower L N P] [IsGalois L P]
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Injective
      (FieldOfNorms.finiteAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L P).toAlgebra
  intro φ ψ hφψ
  let ι := IsScalarTower.toAlgHom L N P
  have hcomp :
      FieldOfNorms.finiteAlgHom K L M P (ι.comp φ) =
        FieldOfNorms.finiteAlgHom K L M P (ι.comp ψ) := by
    rw [FieldOfNorms.finiteAlgHom_comp K L M N P
      φ ι,
      FieldOfNorms.finiteAlgHom_comp K L M N P
        ψ ι, hφψ]
  have h := FieldOfNorms.finiteAlgHom_injective_of_isGalois K L M P
    hcomp
  apply AlgHom.ext
  intro m
  exact (algebraMap N P).injective (AlgHom.congr_fun h m)

/-- Galois fixed-field factorization gives fullness for two original
subextensions of the same genuine finite Galois overfield. -/
theorem FieldOfNorms.finiteAlgHom_surjective_in_galoisOverfield
    [Algebra M P] [Algebra N P] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower L M P] [IsScalarTower L N P] [IsGalois L P]
    [IsAPF K L] [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Surjective
      (FieldOfNorms.finiteAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let : Algebra.IsSeparable L P := Algebra.isSeparable_tower_top_of_isSeparable K L P
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L P).toAlgebra
  let : Module.Finite N P := Module.Finite.right L N P
  let : IsGalois N P := IsGalois.tower_top_of_isGalois L N P
  intro f
  let ι := IsScalarTower.toAlgHom L N P
  let ιX := FieldOfNorms.finiteAlgHom K L N P
    ι
  obtain ⟨φ, hφ⟩ := FieldOfNorms.finiteAlgHom_surjective_of_isGalois K L M P
    (ιX.comp f)
  have hfixed (σ : P ≃ₐ[N] P) (m : M) : σ (φ m) = φ m := by
    let τ := σ.restrictScalars L
    have hnorm :
        FieldOfNorms.finiteAlgHom K L M P
          (τ.toAlgHom.comp φ) =
        FieldOfNorms.finiteAlgHom K L M P φ := by
      apply AlgHom.ext
      intro x
      rw [FieldOfNorms.finiteAlgHom_postcomp_aut K L M P
        φ τ x]
      calc
        _ = FieldOfNorms.map (σ.restrictScalars K) (ιX (f x)) :=
          congrArg (FieldOfNorms.map (σ.restrictScalars K)) (AlgHom.congr_fun hφ x)
        _ = FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K N P (f x)) :=
          congrArg (FieldOfNorms.map (σ.restrictScalars K))
            (FieldOfNorms.finiteAlgHom_algebraMap K L N P
              (f x))
        _ = FieldOfNorms.finiteMap K N P (f x) :=
          FieldOfNorms.map_finiteFieldOfNormsMap_relative K N P σ (f x)
        _ = ιX (f x) := (FieldOfNorms.finiteAlgHom_algebraMap K L N P
          (f x)).symm
        _ = _ := (AlgHom.congr_fun hφ x).symm
    have h := FieldOfNorms.finiteAlgHom_injective_of_isGalois K L M P
      hnorm
    exact AlgHom.congr_fun h m
  obtain ⟨ψ, hψ⟩ := exists_algHom_factor_of_fixed φ hfixed
  refine ⟨ψ, AlgHom.ext (fun x => ?_)⟩
  apply ιX.injective
  have hc := AlgHom.congr_fun (FieldOfNorms.finiteAlgHom_comp K L M N P
    ψ ι) x
  exact hc.symm.trans ((congrArg (fun g =>
    FieldOfNorms.finiteAlgHom K L M P g x)
      hψ).trans (AlgHom.congr_fun hφ x))

/-- Full faithfulness of the actual finite Hom map for arbitrary finite
separable original extensions, with no normality assumption on either field. -/
theorem FieldOfNorms.finiteAlgHom_bijective
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    Function.Bijective
      (FieldOfNorms.finiteAlgHom K L M N) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
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
  exact ⟨FieldOfNorms.finiteAlgHom_injective_in_galoisOverfield K L M N P
,
    FieldOfNorms.finiteAlgHom_surjective_in_galoisOverfield K L M N P
⟩

/-- The canonical full finite Hom equivalence needs only the original
infinite APF base; all finite-extension APF and infinitude facts are produced. -/
def FieldOfNorms.finiteHomEquiv [IsAPF K L] [Fact (¬ Module.Finite K L)] :
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
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
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
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  let := (FieldOfNorms.finiteRingHom K L N).toAlgebra
  exact Equiv.ofBijective
    (FieldOfNorms.finiteAlgHom K L M N)
    (FieldOfNorms.finiteAlgHom_bijective K L M N)

end FontaineWintenberger
