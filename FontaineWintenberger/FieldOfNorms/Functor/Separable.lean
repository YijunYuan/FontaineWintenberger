/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Functor.Galois
public import FontaineWintenberger.FieldOfNorms.Functor.RingHom
public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite separable extensions of the field of norms

## Finite separable extensions of the original norm fields

Actual finite normal closures and the original inclusion maps give degree
preservation and separability without normality over the original base.

## Galois groups for arbitrary finite embeddings

The original range factorization transports the actual relative Galois
extension and its actual action to every finite embedding.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section ScalarTower

variable (K M N P : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field M] [Field N] [Field P] [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower M N P] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Algebra.IsSeparable K P]
    [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]

local notation "p" => residueChar K

/-- The three original finite-inclusion field homomorphisms form a genuine
scalar tower, by composition on the original norm-compatible families. -/
theorem FieldOfNorms.finiteRingHom_isScalarTower
    [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    [Fact (¬ Module.Finite K P)] :
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K M P).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K N P).toAlgebra
    IsScalarTower (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P) := by
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := (FieldOfNorms.finiteRingHom K M P).toAlgebra
  let := (FieldOfNorms.finiteRingHom K N P).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (FieldOfNorms.finiteMap_trans K M N P x).symm

end ScalarTower

section FiniteSeparable

variable (K M N : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable K N] [Module.Finite M N]

local notation "p" => residueChar K

/-- A genuine finite normal closure proves finiteness, separability and
preservation of the full original degree for the actual inclusion field map. -/
theorem FieldOfNorms.finite_finite_separable_degree
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) ∧
      Algebra.IsSeparable (FieldOfNorms K M) (FieldOfNorms K N) ∧
      Module.finrank (FieldOfNorms K M) (FieldOfNorms K N) = Module.finrank M N := by
  let : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
  let P := IntermediateField.normalClosure M N (AlgebraicClosure N)
  let : Algebra K P := inferInstance
  let : IsScalarTower K M P := inferInstance
  let : IsScalarTower K N P := IsScalarTower.to₁₃₄ K M N P
  let : Module.Finite M P := inferInstance
  let : Module.Finite N P := Module.Finite.right M N P
  let : IsGalois M P := inferInstance
  let : IsGalois N P := IsGalois.tower_top_of_isGalois M N P
  let : Algebra.IsSeparable K P := Algebra.IsSeparable.trans K M P
  have hP : IsAPF K P := (isAPF_finite_extension_iff K P M).mpr ‹_›
  have hInfiniteP : ¬ Module.Finite K P := by
    intro h
    let : Module.Finite K P := h
    exact (Fact.out : ¬ Module.Finite K M) (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom K M P).toLinearMap (algebraMap M P).injective)
  have : Fact (¬ Module.Finite K P) := ⟨hInfiniteP⟩
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := (FieldOfNorms.finiteRingHom K M P).toAlgebra
  let := (FieldOfNorms.finiteRingHom K N P).toAlgebra
  let : IsScalarTower (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P) :=
    FieldOfNorms.finiteRingHom_isScalarTower K M N P
  let : FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K P) :=
    finiteDimensional_finiteFieldOfNorms_of_isGalois K M P
  let : FiniteDimensional (FieldOfNorms K N) (FieldOfNorms K P) :=
    finiteDimensional_finiteFieldOfNorms_of_isGalois K N P
  let : FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) :=
    FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P)).toLinearMap
      (algebraMap (FieldOfNorms K N) (FieldOfNorms K P)).injective
  let : IsGalois (FieldOfNorms K M) (FieldOfNorms K P) :=
    isGalois_finiteFieldOfNorms K M P
  refine ⟨inferInstance, Algebra.isSeparable_tower_bot_of_isSeparable
    (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P), ?_⟩
  have hmul := Module.finrank_mul_finrank (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P)
  rw [finrank_finiteFieldOfNorms_of_isGalois K N P,
    finrank_finiteFieldOfNorms_of_isGalois K M P,
    ← Module.finrank_mul_finrank M N P] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := N) (M := P)) hmul

/-- The actual finite-inclusion norm-field extension is finite-dimensional. -/
theorem finiteDimensional_finiteFieldOfNorms
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) :=
  (FieldOfNorms.finite_finite_separable_degree K M N).1

/-- The actual finite-inclusion norm-field extension is separable. -/
theorem isSeparable_finiteFieldOfNorms
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    Algebra.IsSeparable (FieldOfNorms K M) (FieldOfNorms K N) :=
  (FieldOfNorms.finite_finite_separable_degree K M N).2.1

/-- The actual finite-inclusion norm-field extension has the full original degree. -/
theorem finrank_finiteFieldOfNorms
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    Module.finrank (FieldOfNorms K M) (FieldOfNorms K N) = Module.finrank M N :=
  (FieldOfNorms.finite_finite_separable_degree K M N).2.2

end FiniteSeparable

section ArbitraryEmbeddings

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- The actual range factorization transports finite dimension, separability
and the full degree to every original finite separable algebra embedding. -/
theorem FieldOfNorms.finiteEmbedding_finite_separable_degree (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
    FiniteDimensional (FieldOfNorms K L) (FieldOfNorms K M) ∧
      Algebra.IsSeparable (FieldOfNorms K L) (FieldOfNorms K M) ∧
      Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) = Module.finrank τ.fieldRange M := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
  let := (FieldOfNorms.finiteRingHom K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.ringEquiv K τ.equivFieldRange
  have he : (algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M)).comp e.toRingHom =
      (RingEquiv.refl (FieldOfNorms K M)).toRingHom.comp
        (algebraMap (FieldOfNorms K L) (FieldOfNorms K M)) := rfl
  have hdeg : Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) =
      Module.finrank τ.fieldRange M :=
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl _) he).trans
      (finrank_finiteFieldOfNorms K τ.fieldRange M)
  have hpos : 0 < Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) := by
    rw [hdeg]
    exact Module.finrank_pos
  let : FiniteDimensional (FieldOfNorms K L) (FieldOfNorms K M) :=
    FiniteDimensional.of_finrank_pos hpos
  refine ⟨inferInstance, ?_, hdeg⟩
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e (RingEquiv.refl _) he).mpr
    (isSeparable_finiteFieldOfNorms K τ.fieldRange M)

end ArbitraryEmbeddings

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- A finite Galois original range extension gives a Galois extension for
exactly the original arbitrary-embedding norm-field homomorphism. -/
theorem isGalois_finiteFieldOfNormsEmbedding (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
    IsGalois (FieldOfNorms K L) (FieldOfNorms K M) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
  let := (FieldOfNorms.finiteRingHom K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.ringEquiv K τ.equivFieldRange
  let : IsGalois (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M) :=
    isGalois_finiteFieldOfNorms K τ.fieldRange M
  apply IsGalois.of_equiv_equiv (f := e.symm) (g := RingEquiv.refl _)
  apply RingHom.ext
  intro x
  change FieldOfNorms.finiteRingHom K τ.fieldRange M
    (e (e.symm x)) = FieldOfNorms.finiteRingHom K τ.fieldRange M
      x
  rw [e.apply_symm_apply]

/-- The actual original relative action identifies the Galois groups for
an arbitrary finite embedding, by its original source-to-range isomorphism. -/
def FieldOfNorms.finiteEmbeddingGaloisEquiv (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
    (M ≃ₐ[τ.fieldRange] M) ≃*
      (FieldOfNorms K M ≃ₐ[FieldOfNorms K L] FieldOfNorms K M) := by
  haveI hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  haveI : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
  let := (FieldOfNorms.finiteRingHom K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.ringEquiv K τ.equivFieldRange
  let θ : (FieldOfNorms K M ≃ₐ[FieldOfNorms K τ.fieldRange] FieldOfNorms K M) ≃*
      (FieldOfNorms K M ≃ₐ[FieldOfNorms K L] FieldOfNorms K M) :=
    { toFun := fun (σ : FieldOfNorms K M ≃ₐ[FieldOfNorms K τ.fieldRange] FieldOfNorms K M) =>
        { σ.toRingEquiv with
          commutes' := fun a => by
            change σ (algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M) (e a)) = _
            exact σ.commutes (e a) }
      invFun := fun (σ : FieldOfNorms K M ≃ₐ[FieldOfNorms K L] FieldOfNorms K M) =>
        { σ.toRingEquiv with
          commutes' := fun a => by
            change σ (algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M) a) = _
            have h := σ.commutes (e.symm a)
            change σ (algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M)
              (e (e.symm a))) = algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M)
                (e (e.symm a)) at h
            simpa only [e.apply_symm_apply] using h }
      left_inv := fun σ => by apply AlgEquiv.ext; intro x; rfl
      right_inv := fun σ => by apply AlgEquiv.ext; intro x; rfl
      map_mul' := fun σ ρ => by apply AlgEquiv.ext; intro x; rfl }
  exact (FieldOfNorms.finiteGaloisEquiv K τ.fieldRange M).trans θ

@[simp]
theorem FieldOfNorms.finiteEmbeddingGaloisEquiv_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (σ : M ≃ₐ[τ.fieldRange] M) (x : FieldOfNorms K M) :
    letI := (FieldOfNorms.finiteEmbeddingRingHom K τ).toAlgebra
    FieldOfNorms.finiteEmbeddingGaloisEquiv K τ σ x =
      FieldOfNorms.map (σ.restrictScalars K) x := rfl

end FontaineWintenberger
