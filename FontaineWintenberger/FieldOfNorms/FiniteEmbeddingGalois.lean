/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteSeparable
public import FontaineWintenberger.FieldOfNorms.FiniteNaturality

/-!
# Galois groups for arbitrary finite embeddings

The original range factorization transports the actual relative Galois
extension and its actual action to every finite embedding.
-/

@[expose] public section

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
