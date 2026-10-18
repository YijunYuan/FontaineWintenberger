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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- A finite Galois original range extension gives a Galois extension for
exactly the original arbitrary-embedding norm-field homomorphism. -/
theorem isGalois_finiteNormLimitEmbedding (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).toAlgebra
    IsGalois (NormLimit K L) (NormLimit K M) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp hL
  have hInfiniteR := not_finite_fieldRange τ hInfiniteL
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K τ.fieldRange p hR hInfiniteR
  let := (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).toAlgebra
  let := (finiteNormLimitRingHom K τ.fieldRange M p hR hM hInfiniteR hInfiniteM).toAlgebra
  let e := normLimitRingEquiv K p hL hR hInfiniteL hInfiniteR τ.equivFieldRange
  let : IsGalois (NormLimit K τ.fieldRange) (NormLimit K M) :=
    isGalois_finiteNormLimit K τ.fieldRange M p hR hM hInfiniteR hInfiniteM
  apply IsGalois.of_equiv_equiv (f := e.symm) (g := RingEquiv.refl _)
  apply RingHom.ext
  intro x
  change finiteNormLimitRingHom K τ.fieldRange M p hR hM hInfiniteR hInfiniteM
    (e (e.symm x)) = finiteNormLimitRingHom K τ.fieldRange M p hR hM
      hInfiniteR hInfiniteM x
  rw [e.apply_symm_apply]

/-- The actual original relative action identifies the Galois groups for
an arbitrary finite embedding, by its original source-to-range isomorphism. -/
def finiteNormLimitEmbeddingGaloisEquiv (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).toAlgebra
    (M ≃ₐ[τ.fieldRange] M) ≃*
      (NormLimit K M ≃ₐ[NormLimit K L] NormLimit K M) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp hL
  have hInfiniteR := not_finite_fieldRange τ hInfiniteL
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K τ.fieldRange p hR hInfiniteR
  let := (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).toAlgebra
  let := (finiteNormLimitRingHom K τ.fieldRange M p hR hM hInfiniteR hInfiniteM).toAlgebra
  let e := normLimitRingEquiv K p hL hR hInfiniteL hInfiniteR τ.equivFieldRange
  let θ : (NormLimit K M ≃ₐ[NormLimit K τ.fieldRange] NormLimit K M) ≃*
      (NormLimit K M ≃ₐ[NormLimit K L] NormLimit K M) :=
    { toFun := fun (σ : NormLimit K M ≃ₐ[NormLimit K τ.fieldRange] NormLimit K M) =>
        { σ.toRingEquiv with
          commutes' := fun a => by
            change σ (algebraMap (NormLimit K τ.fieldRange) (NormLimit K M) (e a)) = _
            exact σ.commutes (e a) }
      invFun := fun (σ : NormLimit K M ≃ₐ[NormLimit K L] NormLimit K M) =>
        { σ.toRingEquiv with
          commutes' := fun a => by
            change σ (algebraMap (NormLimit K τ.fieldRange) (NormLimit K M) a) = _
            have h := σ.commutes (e.symm a)
            change σ (algebraMap (NormLimit K τ.fieldRange) (NormLimit K M)
              (e (e.symm a))) = algebraMap (NormLimit K τ.fieldRange) (NormLimit K M)
                (e (e.symm a)) at h
            simpa only [e.apply_symm_apply] using h }
      left_inv := fun σ => by apply AlgEquiv.ext; intro x; rfl
      right_inv := fun σ => by apply AlgEquiv.ext; intro x; rfl
      map_mul' := fun σ ρ => by apply AlgEquiv.ext; intro x; rfl }
  exact (finiteNormLimitGaloisEquiv K τ.fieldRange M p hR hM hInfiniteR hInfiniteM).trans θ

@[simp]
theorem finiteNormLimitEmbeddingGaloisEquiv_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [IsGalois τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (σ : M ≃ₐ[τ.fieldRange] M) (x : NormLimit K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).toAlgebra
    finiteNormLimitEmbeddingGaloisEquiv K p τ hL hM hInfiniteL hInfiniteM σ x =
      normLimitMap (σ.restrictScalars K) x := rfl

end FontaineWintenberger
