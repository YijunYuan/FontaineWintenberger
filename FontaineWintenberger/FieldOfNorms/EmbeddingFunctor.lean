module

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
theorem not_finite_fieldRange (τ : L →ₐ[K] M) (hInfinite : ¬ Module.Finite K L) :
    ¬ Module.Finite K τ.fieldRange := by
  intro h
  let : Module.Finite K τ.fieldRange := h
  exact hInfinite (Module.Finite.equiv τ.equivFieldRange.symm.toLinearEquiv)

end Infinity

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The arbitrary original finite-embedding map is a ring homomorphism
between the already constructed original norm fields. -/
def finiteNormLimitEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    NormLimit K L →+* NormLimit K M := by
  letI := normLimitField K L p hL hInfiniteL
  letI := normLimitField K M p hM hInfiniteM
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp hL
  have hInfiniteR := not_finite_fieldRange τ hInfiniteL
  letI := normLimitField K τ.fieldRange p hR hInfiniteR
  exact (finiteNormLimitRingHom K τ.fieldRange M p hR hM hInfiniteR hInfiniteM).comp
    (normLimitRingEquiv K p hL hR hInfiniteL hInfiniteR τ.equivFieldRange).toRingHom

/-- Its underlying map is literally the previously constructed original
multiplicative finite-embedding map. -/
@[simp]
theorem finiteNormLimitEmbeddingRingHom_apply (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM x =
      finiteNormLimitEmbeddingMap K τ x := rfl

include p in
/-- Unitality on the actual original norm fields gives injectivity of the
same original finite-embedding map. -/
theorem finiteNormLimitEmbeddingMap_injective (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    Function.Injective (finiteNormLimitEmbeddingMap K τ) := by
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  exact (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM).injective

/-- The ring-homomorphism coordinates are precisely the original embedding
applied to the original preimage coordinates at every good target field. -/
theorem coe_normLimitEval_finiteNormLimitEmbeddingRingHom (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    (normLimitEval K M D (finiteNormLimitEmbeddingRingHom K p τ hL hM hInfiniteL hInfiniteM x) : M) =
      τ (normLimitEval K L (FiniteLayer.map τ.equivFieldRange.symm.toAlgHom
        (finiteLayerPullbackLayer K τ.fieldRange D)) x : L) := by
  exact coe_normLimitEval_finiteNormLimitEmbeddingMap K τ D hD x

/-- One actual good target field gives the positive finite ramification
exponent for every original source norm family, including zero. -/
theorem exists_goodFiniteLayer_finiteNormLimitEmbeddingMap_valuation (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M) :
    ∃ D : FiniteLayer K M, IsGoodFiniteLayer K τ.fieldRange D ∧
      0 < embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D) ∧
      ∀ x : NormLimit K L,
        normLimitValuation K M hM (finiteNormLimitEmbeddingMap K τ x) =
          normLimitValuation K L hL x ^
            embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D) := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp hL
  obtain ⟨D, hD, he, hv⟩ :=
    exists_goodFiniteLayer_finiteNormLimitMap_valuation K τ.fieldRange M hR hM
  refine ⟨D, hD, he, fun x => ?_⟩
  change normLimitValuation K M hM
    (finiteNormLimitMap K τ.fieldRange M (normLimitMap τ.equivFieldRange x)) = _
  rw [hv, normLimitValuation_normLimitMap K hL hR τ.equivFieldRange]

/-- The original map has a proved fixed positive integral valuation exponent. -/
theorem exists_finiteNormLimitEmbeddingMap_valuation_scaling (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : NormLimit K L,
      normLimitValuation K M hM (finiteNormLimitEmbeddingMap K τ x) =
        normLimitValuation K L hL x ^ e := by
  obtain ⟨D, _, he, hv⟩ :=
    exists_goodFiniteLayer_finiteNormLimitEmbeddingMap_valuation K τ hL hM
  exact ⟨embeddingRamificationIdx K (finiteLayerPullbackTo K τ.fieldRange D), he, hv⟩

/-- The arbitrary original embedding is uniformly continuous for the same
already constructed valuation uniformities on the original norm fields. -/
theorem uniformContinuous_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitValued K L p hL hInfiniteL
    letI := normLimitValued K M p hM hInfiniteM
    UniformContinuous (finiteNormLimitEmbeddingMap K τ) := by
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  let := normLimitValued K L p hL hInfiniteL
  let := normLimitValued K M p hM hInfiniteM
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp hL
  have hInfiniteR := not_finite_fieldRange τ hInfiniteL
  let := normLimitField K τ.fieldRange p hR hInfiniteR
  let := normLimitValued K τ.fieldRange p hR hInfiniteR
  exact (uniformContinuous_finiteNormLimitMap K τ.fieldRange M p hR hM hInfiniteR hInfiniteM).comp
    (normLimitUniformEquiv K p hL hR hInfiniteL hInfiniteR τ.equivFieldRange).uniformContinuous_toFun

/-- Continuity is for the original valuation topologies on the original fields. -/
theorem continuous_finiteNormLimitEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitValued K L p hL hInfiniteL
    letI := normLimitValued K M p hM hInfiniteM
    Continuous (finiteNormLimitEmbeddingMap K τ) := by
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  let := normLimitValued K L p hL hInfiniteL
  let := normLimitValued K M p hM hInfiniteM
  exact (uniformContinuous_finiteNormLimitEmbeddingMap K p τ hL hM hInfiniteL hInfiniteM).continuous

end FontaineWintenberger
