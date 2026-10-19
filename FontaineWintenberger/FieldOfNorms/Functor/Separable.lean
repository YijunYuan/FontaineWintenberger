/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Functor.Galois
public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite separable extensions of the field of norms

## Finite separable extensions of the norm fields

Finite normal closures and the inclusion maps give degree
preservation and separability without normality over the base.

## Galois groups for arbitrary finite embeddings

The range factorization transports the relative Galois
extension and its action to every finite embedding.
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

/-- The three finite-inclusion field homomorphisms form a
scalar tower, by composition on the norm-compatible families. -/
theorem FieldOfNorms.inclusion_isScalarTower
    [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    [Fact (¬ Module.Finite K P)] :
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    letI := (FieldOfNorms.inclusion K M N).toAlgebra
    letI := (FieldOfNorms.inclusion K M P).toAlgebra
    letI := (FieldOfNorms.inclusion K N P).toAlgebra
    IsScalarTower (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P) := by
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let := (FieldOfNorms.inclusion K M N).toAlgebra
  let := (FieldOfNorms.inclusion K M P).toAlgebra
  let := (FieldOfNorms.inclusion K N P).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (FieldOfNorms.inclusion_inclusion K M N P x).symm

end ScalarTower

section FiniteSeparable

variable (K M N : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable K N] [Module.Finite M N]

local notation "p" => residueChar K

/-- A finite normal closure proves finiteness, separability and
preservation of the full degree for the inclusion field map. -/
theorem FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.inclusion K M N).toAlgebra
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
  let := (FieldOfNorms.inclusion K M N).toAlgebra
  let := (FieldOfNorms.inclusion K M P).toAlgebra
  let := (FieldOfNorms.inclusion K N P).toAlgebra
  let : IsScalarTower (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P) :=
    FieldOfNorms.inclusion_isScalarTower K M N P
  let : FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K P) :=
    FieldOfNorms.finiteDimensional_of_isGalois K M P
  let : FiniteDimensional (FieldOfNorms K N) (FieldOfNorms K P) :=
    FieldOfNorms.finiteDimensional_of_isGalois K N P
  let : FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) :=
    FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P)).toLinearMap
      (algebraMap (FieldOfNorms K N) (FieldOfNorms K P)).injective
  let : IsGalois (FieldOfNorms K M) (FieldOfNorms K P) :=
    FieldOfNorms.isGalois K M P
  refine ⟨inferInstance, Algebra.isSeparable_tower_bot_of_isSeparable
    (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P), ?_⟩
  have hmul := Module.finrank_mul_finrank (FieldOfNorms K M) (FieldOfNorms K N) (FieldOfNorms K P)
  rw [FieldOfNorms.finrank_of_isGalois K N P,
    FieldOfNorms.finrank_of_isGalois K M P,
    ← Module.finrank_mul_finrank M N P] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := N) (M := P)) hmul

/-- The finite-inclusion norm-field extension is finite-dimensional. -/
theorem FieldOfNorms.finiteDimensional
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.inclusion K M N).toAlgebra
    FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) :=
  (FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion K M N).1

/-- The finite-inclusion norm-field extension is separable. -/
theorem FieldOfNorms.isSeparable
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.inclusion K M N).toAlgebra
    Algebra.IsSeparable (FieldOfNorms K M) (FieldOfNorms K N) :=
  (FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion K M N).2.1

/-- The finite-inclusion norm-field extension has the full degree. -/
theorem FieldOfNorms.finrank
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := (FieldOfNorms.inclusion K M N).toAlgebra
    Module.finrank (FieldOfNorms K M) (FieldOfNorms K N) = Module.finrank M N :=
  (FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion K M N).2.2

end FiniteSeparable

section ArbitraryEmbeddings

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- The range factorization transports finite dimension, separability
and the full degree to every finite separable algebra embedding. -/
theorem FieldOfNorms.finiteDimensional_isSeparable_finrank_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.map τ).toAlgebra
    FiniteDimensional (FieldOfNorms K L) (FieldOfNorms K M) ∧
      Algebra.IsSeparable (FieldOfNorms K L) (FieldOfNorms K M) ∧
      Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) = Module.finrank τ.fieldRange M := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.map τ).toAlgebra
  let := (FieldOfNorms.inclusion K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.mapEquiv τ.equivFieldRange
  have he : (algebraMap (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M)).comp e.toRingHom =
      (RingEquiv.refl (FieldOfNorms K M)).toRingHom.comp
        (algebraMap (FieldOfNorms K L) (FieldOfNorms K M)) := rfl
  have hdeg : Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) =
      Module.finrank τ.fieldRange M :=
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl _) he).trans
      (FieldOfNorms.finrank K τ.fieldRange M)
  have hpos : 0 < Module.finrank (FieldOfNorms K L) (FieldOfNorms K M) := by
    rw [hdeg]
    exact Module.finrank_pos
  let : FiniteDimensional (FieldOfNorms K L) (FieldOfNorms K M) :=
    FiniteDimensional.of_finrank_pos hpos
  refine ⟨inferInstance, ?_, hdeg⟩
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e (RingEquiv.refl _) he).mpr
    (FieldOfNorms.isSeparable K τ.fieldRange M)

end ArbitraryEmbeddings

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- A finite Galois range extension gives a Galois extension for
exactly the arbitrary-embedding norm-field homomorphism. -/
theorem FieldOfNorms.isGalois_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.map τ).toAlgebra
    IsGalois (FieldOfNorms K L) (FieldOfNorms K M) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.map τ).toAlgebra
  let := (FieldOfNorms.inclusion K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.mapEquiv τ.equivFieldRange
  let : IsGalois (FieldOfNorms K τ.fieldRange) (FieldOfNorms K M) :=
    FieldOfNorms.isGalois K τ.fieldRange M
  apply IsGalois.of_equiv_equiv (f := e.symm) (g := RingEquiv.refl _)
  apply RingHom.ext
  intro x
  change FieldOfNorms.inclusion K τ.fieldRange M
    (e (e.symm x)) = FieldOfNorms.inclusion K τ.fieldRange M
      x
  rw [e.apply_symm_apply]

/-- The relative action identifies the Galois groups for
an arbitrary finite embedding, by its source-to-range isomorphism. -/
def FieldOfNorms.autEquivOfMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := (FieldOfNorms.map τ).toAlgebra
    (M ≃ₐ[τ.fieldRange] M) ≃*
      (FieldOfNorms K M ≃ₐ[FieldOfNorms K L] FieldOfNorms K M) := by
  haveI hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  haveI : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := (FieldOfNorms.map τ).toAlgebra
  let := (FieldOfNorms.inclusion K τ.fieldRange M).toAlgebra
  let e := FieldOfNorms.mapEquiv τ.equivFieldRange
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
  exact (FieldOfNorms.autEquiv K τ.fieldRange M).trans θ

@[simp]
theorem FieldOfNorms.autEquivOfMap_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (σ : M ≃ₐ[τ.fieldRange] M) (x : FieldOfNorms K M) :
    letI := (FieldOfNorms.map τ).toAlgebra
    FieldOfNorms.autEquivOfMap K τ σ x =
      FieldOfNorms.mapEquiv (σ.restrictScalars K) x := rfl

end FontaineWintenberger
