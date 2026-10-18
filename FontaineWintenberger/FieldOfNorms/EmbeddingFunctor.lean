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
def FieldOfNorms.finiteEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    FieldOfNorms K L →+* FieldOfNorms K M := by
  haveI hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  haveI : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  exact (FieldOfNorms.finiteRingHom K τ.fieldRange M).comp
    (FieldOfNorms.ringEquiv K τ.equivFieldRange).toRingHom

/-- Its underlying map is literally the previously constructed original
multiplicative finite-embedding map. -/
@[simp]
theorem FieldOfNorms.finiteEmbeddingRingHom_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (x : FieldOfNorms K L) :
    FieldOfNorms.finiteEmbeddingRingHom K τ x =
      FieldOfNorms.finiteEmbeddingMap K τ x := rfl

/-- Unitality on the actual original norm fields gives injectivity of the
same original finite-embedding map. -/
theorem FieldOfNorms.finiteEmbeddingMap_injective (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    Function.Injective (FieldOfNorms.finiteEmbeddingMap K τ) := by
  exact (FieldOfNorms.finiteEmbeddingRingHom K τ).injective

/-- The ring-homomorphism coordinates are precisely the original embedding
applied to the original preimage coordinates at every good target field. -/
theorem coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (D : FiniteIntermediateField K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : FieldOfNorms K
        L) :
    (FieldOfNorms.coord K M D (FieldOfNorms.finiteEmbeddingRingHom K τ x) : M)
        =
      τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
        (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L) := by
  exact coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap K τ D hD x

/-- One actual good target field gives the positive finite ramification
exponent for every original source norm family, including zero. -/
theorem exists_goodFiniteLayer_finiteFieldOfNormsEmbeddingMap_valuation (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M] :
    ∃ D : FiniteIntermediateField K M, IsGoodFiniteLayer K τ.fieldRange D ∧
      0 < embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D) ∧
      ∀ x : FieldOfNorms K L,
        FieldOfNorms.valuation K M (FieldOfNorms.finiteEmbeddingMap K τ x) =
          FieldOfNorms.valuation K L x ^
            embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  obtain ⟨D, hD, he, hv⟩ :=
    exists_goodFiniteLayer_finiteFieldOfNormsMap_valuation K τ.fieldRange M
  refine ⟨D, hD, he, fun x => ?_⟩
  change FieldOfNorms.valuation K M
    (FieldOfNorms.finiteMap K τ.fieldRange M (FieldOfNorms.map τ.equivFieldRange x)) = _
  rw [hv, FieldOfNorms.valuation_fieldOfNormsMap K τ.equivFieldRange]

/-- The original map has a proved fixed positive integral valuation exponent. -/
theorem exists_finiteFieldOfNormsEmbeddingMap_valuation_scaling (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M] :
    ∃ e : ℕ, 0 < e ∧ ∀ x : FieldOfNorms K L,
      FieldOfNorms.valuation K M (FieldOfNorms.finiteEmbeddingMap K τ x) =
        FieldOfNorms.valuation K L x ^ e := by
  obtain ⟨D, _, he, hv⟩ :=
    exists_goodFiniteLayer_finiteFieldOfNormsEmbeddingMap_valuation K τ
  exact ⟨embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D), he, hv⟩

/-- The arbitrary original embedding is uniformly continuous for the same
already constructed valuation uniformities on the original norm fields. -/
theorem uniformContinuous_finiteFieldOfNormsEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    UniformContinuous (FieldOfNorms.finiteEmbeddingMap K τ) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  exact (uniformContinuous_finiteFieldOfNormsMap K τ.fieldRange M).comp
    (FieldOfNorms.uniformEquiv K
        τ.equivFieldRange).uniformContinuous_toFun

/-- Continuity is for the original valuation topologies on the original fields. -/
theorem continuous_finiteFieldOfNormsEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    Continuous (FieldOfNorms.finiteEmbeddingMap K τ) := by
  exact (uniformContinuous_finiteFieldOfNormsEmbeddingMap K τ).continuous

end FontaineWintenberger
