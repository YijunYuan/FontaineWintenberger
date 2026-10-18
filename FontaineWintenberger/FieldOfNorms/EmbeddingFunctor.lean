/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteFunctorLaws
public import FontaineWintenberger.FieldOfNorms.FiniteEmbedding

/-!
# Arbitrary finite embeddings of the original norm fields

A finite separable embedding factors through its actual field range.
The original range isomorphism and finite-inclusion maps give the same
norm-family map, now as an injective continuous field homomorphism.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Infinity

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- The original range of an infinite algebra embedding has the same
infinite dimension; no infinity hypothesis on the range is supplied. -/
theorem not_finite_fieldRange (τ : L →ₐ[K] M) [Fact (¬ Module.Finite K L)] :
    ¬ Module.Finite K τ.fieldRange := by
  intro h
  let : Module.Finite K τ.fieldRange := h
  exact (Fact.out : ¬ Module.Finite K L) (Module.Finite.equiv τ.equivFieldRange.symm.toLinearEquiv)

end Infinity

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- The arbitrary original finite-embedding map is a ring homomorphism
between the already constructed original norm fields. -/
def finiteNormLimitEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    NormLimit K L →+* NormLimit K M := by
  haveI hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  haveI : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  exact (finiteNormLimitRingHom K τ.fieldRange M).comp
    (normLimitRingEquiv K τ.equivFieldRange).toRingHom

/-- Its underlying map is literally the previously constructed original
multiplicative finite-embedding map. -/
@[simp]
theorem finiteNormLimitEmbeddingRingHom_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (x : NormLimit K L) :
    finiteNormLimitEmbeddingRingHom K τ x =
      finiteNormLimitEmbeddingMap K τ x := rfl

/-- Unitality on the actual original norm fields gives injectivity of the
same original finite-embedding map. -/
theorem finiteNormLimitEmbeddingMap_injective (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    Function.Injective (finiteNormLimitEmbeddingMap K τ) := by
  exact (finiteNormLimitEmbeddingRingHom K τ).injective

/-- The ring-homomorphism coordinates are precisely the original embedding
applied to the original preimage coordinates at every good target field. -/
theorem coe_normLimitEval_finiteNormLimitEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : NormLimit K L) :
    (normLimitEval K M D (finiteNormLimitEmbeddingRingHom K τ x) : M)
        =
      τ (normLimitEval K L (FiniteLayer.map τ.equivFieldRange.symm.toAlgHom
        (finiteLayerPullbackLayer K τ.fieldRange D)) x : L) := by
  exact coe_normLimitEval_finiteNormLimitEmbeddingMap K τ D hD x

/-- One actual good target field gives the positive finite ramification
exponent for every original source norm family, including zero. -/
theorem exists_goodFiniteLayer_finiteNormLimitEmbeddingMap_valuation (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M] :
    ∃ D : FiniteLayer K M, IsGoodFiniteLayer K τ.fieldRange D ∧
      0 < embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D) ∧
      ∀ x : NormLimit K L,
        normLimitValuation K M (finiteNormLimitEmbeddingMap K τ x) =
          normLimitValuation K L x ^
            embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  obtain ⟨D, hD, he, hv⟩ :=
    exists_goodFiniteLayer_finiteNormLimitMap_valuation K τ.fieldRange M
  refine ⟨D, hD, he, fun x => ?_⟩
  change normLimitValuation K M
    (finiteNormLimitMap K τ.fieldRange M (normLimitMap τ.equivFieldRange x)) = _
  rw [hv, normLimitValuation_normLimitMap K τ.equivFieldRange]

/-- The original map has a proved fixed positive integral valuation exponent. -/
theorem exists_finiteNormLimitEmbeddingMap_valuation_scaling (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M] :
    ∃ e : ℕ, 0 < e ∧ ∀ x : NormLimit K L,
      normLimitValuation K M (finiteNormLimitEmbeddingMap K τ x) =
        normLimitValuation K L x ^ e := by
  obtain ⟨D, _, he, hv⟩ :=
    exists_goodFiniteLayer_finiteNormLimitEmbeddingMap_valuation K τ
  exact ⟨embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D), he, hv⟩

/-- The arbitrary original embedding is uniformly continuous for the same
already constructed valuation uniformities on the original norm fields. -/
theorem uniformContinuous_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    UniformContinuous (finiteNormLimitEmbeddingMap K τ) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  exact (uniformContinuous_finiteNormLimitMap K τ.fieldRange M).comp
    (normLimitUniformEquiv K
        τ.equivFieldRange).uniformContinuous_toFun

/-- Continuity is for the original valuation topologies on the original fields. -/
theorem continuous_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    Continuous (finiteNormLimitEmbeddingMap K τ) := by
  exact (uniformContinuous_finiteNormLimitEmbeddingMap K τ).continuous

end FontaineWintenberger
