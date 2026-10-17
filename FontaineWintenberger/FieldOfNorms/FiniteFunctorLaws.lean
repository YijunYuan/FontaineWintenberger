/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.FiniteFunctor
public import FontaineWintenberger.Algebra.GoodFiniteTowers
public import FontaineWintenberger.FieldOfNorms.Isomorphism

/-!
# Functor laws for finite maps on the original norm families

Identity and composition are tested on genuinely cofinal original good
finite fields. All comparisons retain the actual original inclusions.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Identity

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

/-- For the actual identity inclusion the canonical pullback is the same
original finite index. -/
theorem finiteLayerPullbackLayer_self (D : FiniteLayer K M) :
    finiteLayerPullbackLayer K M D = D := by
  apply Subtype.ext
  ext x
  rfl

/-- The original pullback coordinate for the identity is the original
coordinate itself. -/
@[simp]
theorem finiteNormLimitCoordinate_self (D : FiniteLayer K M) (x : NormLimit K M) :
    finiteNormLimitCoordinate K M M D x = normLimitEval K M D x := by
  apply Subtype.ext
  change (normLimitEval K M (finiteLayerPullbackLayer K M D) x : M) =
    (normLimitEval K M D x : M)
  rw [finiteLayerPullbackLayer_self]

variable [Algebra.IsAlgebraic K M]

/-- The covariant finite-inclusion map preserves the actual identity. -/
@[simp]
theorem finiteNormLimitMap_refl (x : NormLimit K M) : finiteNormLimitMap K M M x = x := by
  apply NormLimit.ext_cofinal K M (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M M)
  intro D hD
  exact (normLimitEval_finiteNormLimitMap K M M D hD x).trans
    (finiteNormLimitCoordinate_self K M D x)

end Identity

section Composition

variable (K M N P : Type*) [Field K] [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower M N P] [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]

/-- Composition on the same original norm families, tested on the proved
cofinal simultaneous good stages of the actual finite separable tower. -/
theorem finiteNormLimitMap_trans (x : NormLimit K M) :
    letI : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    finiteNormLimitMap K N P (finiteNormLimitMap K M N x) = finiteNormLimitMap K M P x := by
  let : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let Q (D : FiniteLayer K P) := IsGoodFiniteLayer K N D ∧ IsGoodFiniteLayer K M D ∧
    IsGoodFiniteLayer K M (finiteLayerPullbackLayer K N D)
  have hQ (E : FiniteLayer K P) : ∃ D, Q D ∧ E ≤ D := by
    obtain ⟨D, hED, hN, hM, hMN⟩ := exists_goodFiniteLayer_tower_ge K M N E
    exact ⟨D, ⟨hN, hM, hMN⟩, hED⟩
  apply NormLimit.ext_cofinal K P Q hQ
  intro D ⟨hN, hM, hMN⟩
  rw [normLimitEval_finiteNormLimitMap K N P D hN,
    normLimitEval_finiteNormLimitMap K M P D hM]
  change finiteLayerPullbackTo K N D
      (normLimitEval K N (finiteLayerPullbackLayer K N D) (finiteNormLimitMap K M N x)) = _
  rw [normLimitEval_finiteNormLimitMap K M N (finiteLayerPullbackLayer K N D) hMN]
  apply Subtype.ext
  change algebraMap N P (algebraMap M N
      (normLimitEval K M (finiteLayerPullbackLayer K M (finiteLayerPullbackLayer K N D)) x : M)) =
    algebraMap M P (normLimitEval K M (finiteLayerPullbackLayer K M D) x : M)
  rw [← IsScalarTower.algebraMap_apply, finiteLayerPullbackLayer_tower K M N D]

end Composition

section Embeddings

variable (K : Type*) {L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]

/-- The actual preimage index can equivalently be computed by pulling back
to the actual image and then through the original range isomorphism. -/
theorem finiteLayer_pullback_fieldRange (τ : L →ₐ[K] M) (D : FiniteLayer K M) :
    (FiniteLayer.map τ.equivFieldRange.symm.toAlgHom
      (finiteLayerPullbackLayer K τ.fieldRange D)).val = D.val.comap τ := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change τ (τ.equivFieldRange.symm a) ∈ D.val
    change (a : M) ∈ D.val at ha
    have he : τ (τ.equivFieldRange.symm a) = (a : M) :=
      congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply a)
    rw [he]
    exact ha
  · intro hx
    refine ⟨τ.equivFieldRange x, hx, ?_⟩
    exact τ.equivFieldRange.symm_apply_apply x

variable [Algebra.IsAlgebraic K L]

/-- The actual multiplicative norm-family map for any finite separable
embedding, factored through its original image with the proved isomorphism API. -/
def finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M] :
    NormLimit K L →*₀ NormLimit K M := by
  letI : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact (finiteNormLimitMap K τ.fieldRange M).comp
    (normLimitMulEquiv τ.equivFieldRange).toMonoidWithZeroHom

/-- The actual range factorization gives precisely the prescribed good
coordinates on the original norm families. -/
theorem normLimitEval_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : NormLimit K L) :
    normLimitEval K M D (finiteNormLimitEmbeddingMap K τ x) =
      finiteNormLimitCoordinate K τ.fieldRange M D (normLimitMap τ.equivFieldRange x) := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact normLimitEval_finiteNormLimitMap K τ.fieldRange M D hD _

/-- In the actual ambient field, the prescribed coordinate is the original
embedding applied to the original preimage coordinate. -/
theorem coe_normLimitEval_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : NormLimit K L) :
    (normLimitEval K M D (finiteNormLimitEmbeddingMap K τ x) : M) =
      τ (normLimitEval K L (FiniteLayer.map τ.equivFieldRange.symm.toAlgHom
        (finiteLayerPullbackLayer K τ.fieldRange D)) x : L) := by
  rw [normLimitEval_finiteNormLimitEmbeddingMap K τ D hD]
  change algebraMap τ.fieldRange M
      (normLimitEval K τ.fieldRange (finiteLayerPullbackLayer K τ.fieldRange D)
        (normLimitMap τ.equivFieldRange x) : τ.fieldRange) = _
  rw [coe_normLimitEval_normLimitMap]
  rfl

end Embeddings

end FontaineWintenberger
