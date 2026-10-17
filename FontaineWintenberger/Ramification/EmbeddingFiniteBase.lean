module

public import FontaineWintenberger.Ramification.EmbeddingComparison
public import FontaineWintenberger.Algebra.SeparableEmbeddings

/-!
# Embedding comparisons over original abstract finite bases

The actual compatible norm on each original finite base supplies its
intrinsic relative first bound. Restricting scalars preserves normalized
embedding numbers without assuming a valuation transport certificate.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

section AbstractFiniteBaseEmbedding

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M] [FiniteDimensional K M]
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
    [Algebra M F] [Algebra M Ω] [IsScalarTower K M F] [IsScalarTower K M Ω]
    [FiniteDimensional K F] [FiniteDimensional K Ω]
    [Algebra.IsSeparable K F] [Algebra.IsSeparable K Ω]

/-- Forgetting an actual compatible finite base leaves the intrinsic
embedding number unchanged. The original abstract base retains its original
norm; both source and ambient integer rings are identified through their
proved actual unit balls, and both local indices are genuinely transported. -/
theorem embeddingNumber_restrictScalars_of_normedAlgebra :
    letI := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M Ω
    letI : FiniteDimensional M F := Module.Finite.right K M F
    letI : FiniteDimensional M Ω := Module.Finite.right K M Ω
    ∀ σ τ : F →ₐ[M] Ω,
      embeddingRamificationNumber K (σ.restrictScalars K) (τ.restrictScalars K) =
        embeddingRamificationNumber M σ τ := by
  let := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let := Algebra.isSeparable_tower_top_of_isSeparable K M Ω
  let : FiniteDimensional M F := Module.Finite.right K M F
  let : FiniteDimensional M Ω := Module.Finite.right K M Ω
  intro σ τ
  let := spectralNorm.nontriviallyNormedField K F
  let := spectralNorm.normedAlgebra K F
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := F))
  let := spectralNorm.normedAlgebra' K M F
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let := spectralNorm.normedAlgebra' K M Ω
  let A := spectralIntegerRing K F
  let B := spectralIntegerRing K Ω
  let A' := spectralIntegerRing M F
  let B' := spectralIntegerRing M Ω
  let rF : A ≃+* A' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    ((spectralIntegerRing_eq_normedUnitBall K F).trans
      (spectralIntegerRing_eq_normedUnitBall M F).symm))
  let rΩ : B ≃+* B' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    ((spectralIntegerRing_eq_normedUnitBall K Ω).trans
      (spectralIntegerRing_eq_normedUnitBall M Ω).symm))
  let : Algebra A B := (spectralIntegerInclusion K (σ.restrictScalars K)).toRingHom.toAlgebra
  let : Algebra A' B' := (spectralIntegerInclusion M σ).toRingHom.toAlgebra
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (by
    intro a b hab
    apply Subtype.ext
    exact σ.injective (congrArg (fun z : B => (z : Ω)) hab))
  let : FaithfulSMul A' B' := (faithfulSMul_iff_algebraMap_injective A' B').mpr (by
    intro a b hab
    apply Subtype.ext
    exact σ.injective (congrArg (fun z : B' => (z : Ω)) hab))
  let : IsLocalHom (algebraMap A B) :=
    ⟨(spectralIntegerInclusion_isLocalHom K (σ.restrictScalars K)).map_nonunit⟩
  let : IsLocalHom (algebraMap A' B') :=
    ⟨(spectralIntegerInclusion_isLocalHom M σ).map_nonunit⟩
  have hidx : embeddingRamificationIdx M σ =
      embeddingRamificationIdx K (σ.restrictScalars K) :=
    local_ramificationIdx_ringEquiv rF rΩ (fun _ => Subtype.ext rfl)
  have hraw : embeddingIntegralOrder K (σ.restrictScalars K) (τ.restrictScalars K) =
      embeddingIntegralOrder M σ τ := by
    unfold embeddingIntegralOrder integralEmbeddingOrder
    apply rF.toEquiv.iInf_congr
    intro x
    have he : rΩ
        (spectralIntegerInclusion K (σ.restrictScalars K) x -
          spectralIntegerInclusion K (τ.restrictScalars K) x) =
        spectralIntegerInclusion M σ (rF x) - spectralIntegerInclusion M τ (rF x) :=
      Subtype.ext rfl
    change IsDiscreteValuationRing.addVal B'
      (spectralIntegerInclusion M σ (rF x) - spectralIntegerInclusion M τ (rF x)) =
      IsDiscreteValuationRing.addVal B
        (spectralIntegerInclusion K (σ.restrictScalars K) x -
          spectralIntegerInclusion K (τ.restrictScalars K) x)
    rw [← he, addVal_ringEquiv]
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingRamificationOrder, embeddingRamificationOrder, hraw, hidx]

end AbstractFiniteBaseEmbedding

section AmbientExtension

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- An actual embedding of an actual intermediate field extends to an
automorphism of an ordinary normal ambient field, by Mathlib's genuine lift. -/
theorem exists_aut_comp_intermediate (F : IntermediateField K Ω) (σ : F →ₐ[K] Ω) :
    ∃ s : Ω ≃ₐ[K] Ω, s.toAlgHom.comp F.val = σ := by
  obtain ⟨s, hs⟩ := exists_aut_extends_intermediate_embedding K Ω F σ
  exact ⟨s, AlgHom.ext hs⟩

end AmbientExtension

section ArbitraryEmbeddingFirstBound

variable (K Ω : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
variable {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F]

/-- The first bound controls every actual pair of embeddings of an
original finite field, without assuming that either image is stable. -/
theorem apfRamificationBound_le_embeddingPairNumber (σ τ : F →ₐ[K] Ω) :
    apfRamificationBound K F ≤ embeddingRamificationNumber K σ τ := by
  let e := τ.equivFieldRange
  let : FiniteDimensional K τ.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let σ' := σ.comp e.symm.toAlgHom
  obtain ⟨s, hs⟩ := exists_aut_comp_intermediate K Ω τ.fieldRange σ'
  have h := apfRamificationBound_le_embeddingNumber K Ω τ.fieldRange s
  rw [hs] at h
  have he := embeddingNumber_precomp_algEquiv K e σ' τ.fieldRange.val
  have hσ : σ'.comp e.toAlgHom = σ := by
    ext x
    exact congrArg σ (e.symm_apply_apply x)
  have hτ : τ.fieldRange.val.comp e.toAlgHom = τ := rfl
  rw [hσ, hτ] at he
  rw [← he, ← apfRamificationBound_algEquiv K F e] at h
  exact h

end ArbitraryEmbeddingFirstBound

section OriginalRelativePairBound

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M] [FiniteDimensional K M]
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
    [Algebra M F] [Algebra M Ω] [IsScalarTower K M F] [IsScalarTower K M Ω]
    [FiniteDimensional K F] [FiniteDimensional K Ω]
    [Algebra.IsSeparable K F] [IsGalois K Ω]

/-- The actual relative first bound over the original abstract normed base
controls the same pair number over the original old base. Every base norm,
integer ring, separability and perfect-residue prerequisite is produced. -/
theorem apfRelativeBound_le_embeddingPairNumber_of_normedAlgebra :
    letI := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M Ω
    letI : FiniteDimensional M F := Module.Finite.right K M F
    letI : FiniteDimensional M Ω := Module.Finite.right K M Ω
    ∀ σ τ : F →ₐ[M] Ω,
      apfRamificationBound M F ≤
        embeddingRamificationNumber K (σ.restrictScalars K) (τ.restrictScalars K) := by
  let := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let := Algebra.isSeparable_tower_top_of_isSeparable K M Ω
  let : FiniteDimensional M F := Module.Finite.right K M F
  let : FiniteDimensional M Ω := Module.Finite.right K M Ω
  let : IsGalois M Ω := IsGalois.tower_top_of_isGalois K M Ω
  let : PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring) :=
    normedAlgebra_residueField_perfectField K M
  intro σ τ
  rw [embeddingNumber_restrictScalars_of_normedAlgebra K M σ τ]
  exact apfRamificationBound_le_embeddingPairNumber M Ω σ τ

omit [Algebra M Ω] [IsScalarTower K M Ω] in
/-- Actual ambient embeddings agreeing on the original normed finite base
are separated by its actual relative first bound, even when that base image
is moved by either ambient automorphism. -/
theorem apfRelativeBound_le_pairNumber_of_normedAlgebra
    (i : F →ₐ[K] Ω) (s t : Ω ≃ₐ[K] Ω)
    (hst : (s.toAlgHom.comp i).comp (IsScalarTower.toAlgHom K M F) =
      (t.toAlgHom.comp i).comp (IsScalarTower.toAlgHom K M F)) :
    letI := Algebra.isSeparable_tower_bot_of_isSeparable K M F
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    letI : FiniteDimensional M F := Module.Finite.right K M F
    apfRamificationBound M F ≤
      embeddingRamificationNumber K (s.toAlgHom.comp i) (t.toAlgHom.comp i) := by
  let := Algebra.isSeparable_tower_bot_of_isSeparable K M F
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let : FiniteDimensional M F := Module.Finite.right K M F
  let j : M →ₐ[K] Ω := (t.toAlgHom.comp i).comp (IsScalarTower.toAlgHom K M F)
  let : Algebra M Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K M Ω := IsScalarTower.of_algHom j
  let f : F →ₐ[M] Ω := {
    (s.toAlgHom.comp i).toRingHom with
    commutes' := fun m => congrArg (fun u : M →ₐ[K] Ω => u m) hst }
  let g : F →ₐ[M] Ω := { (t.toAlgHom.comp i).toRingHom with commutes' := fun _ => rfl }
  exact apfRelativeBound_le_embeddingPairNumber_of_normedAlgebra K M f g

omit [Algebra M Ω] [IsScalarTower K M Ω] in
/-- Ordinary total ramification and the actual relative first bound of an
original finite base force rigidity of every extension embedding. The image
of that base need not be preserved by the original ambient automorphism. -/
theorem embeddingNumber_eq_restriction_of_lt_originalBound
    (E D : IntermediateField K Ω) (hED : E ≤ D)
    (e : F ≃ₐ[K] D) (hM : ∀ m : M, (e (algebraMap M F m) : Ω) ∈ E)
    (htotal : embeddingRamificationIdx K (IntermediateField.inclusion hED) =
      Module.finrank E (IntermediateField.extendScalars hED))
    (s : Ω ≃ₐ[K] Ω) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    letI := Algebra.isSeparable_tower_bot_of_isSeparable K M F
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    letI : FiniteDimensional M F := Module.Finite.right K M F
    embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val <
      apfRamificationBound M F →
      embeddingRamificationNumber K (s.toAlgHom.comp D.val) D.val =
        embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val := by
  classical
  let := Algebra.isSeparable_tower_bot_of_isSeparable K M F
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let : FiniteDimensional M F := Module.Finite.right K M F
  intro hsmall
  let H := E.fixingSubgroup
  let := Fintype.ofFinite H
  obtain ⟨d₀, hd₀⟩ :=
    exists_embedding_extension_number_le_of_totallyRamified K Ω E D hED htotal s hs
  have hrestr (d : H) : (s * d.1).toAlgHom.comp E.val = s.toAlgHom.comp E.val := by
    have h := mul_subgroup_fixedField_comp K Ω H s d
    rw [IsGalois.fixedField_fixingSubgroup E] at h
    exact h
  have hseparate (d : H) : apfRamificationBound M F ≤
      embeddingRamificationNumber K ((s * d₀.1).toAlgHom.comp D.val)
        ((s * d.1).toAlgHom.comp D.val) := by
    have hagree : (((s * d₀.1).toAlgHom.comp (D.val.comp e.toAlgHom)).comp
        (IsScalarTower.toAlgHom K M F)) =
      (((s * d.1).toAlgHom.comp (D.val.comp e.toAlgHom)).comp
        (IsScalarTower.toAlgHom K M F)) := by
      ext m
      exact congrArg (fun f : E →ₐ[K] Ω => f ⟨(e (algebraMap M F m) : Ω), hM m⟩)
        ((hrestr d₀).trans (hrestr d).symm)
    have h := apfRelativeBound_le_pairNumber_of_normedAlgebra K M
      (D.val.comp e.toAlgHom) (s * d₀.1) (s * d.1) hagree
    exact h.trans_eq (embeddingNumber_precomp_algEquiv K e
      ((s * d₀.1).toAlgHom.comp D.val) ((s * d.1).toAlgHom.comp D.val))
  have hconst (d : H) :
      embeddingRamificationNumber K ((s * d.1).toAlgHom.comp D.val) D.val =
        embeddingRamificationNumber K ((s * d₀.1).toAlgHom.comp D.val) D.val := by
    apply embeddingNumber_eq_of_lt_pair
    exact (hd₀.trans_lt hsmall).trans_le (hseparate d)
  have hJ (d : H) :
      embeddingRamificationOrder K ((s * d.1).toAlgHom.comp D.val) D.val =
        embeddingRamificationOrder K ((s * d₀.1).toAlgHom.comp D.val) D.val := by
    apply EReal.coe_ennreal_injective
    have h := congrArg (fun a : EReal => a + 1) (hconst d)
    simpa only [embeddingRamificationNumber_add_one] using h
  have hsum := sum_embedding_extension_order_of_totallyRamified K Ω E D hED htotal s hs
  simp_rw [hJ] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have heq :
      (embeddingRamificationOrder K ((s * d₀.1).toAlgHom.comp D.val) D.val).toReal =
        (embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val).toReal := by
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero) :
      (Fintype.card H : ℝ) ≠ 0)) hsum
  have hsD : s.toAlgHom.comp D.val ≠ D.val := by
    intro hf
    exact hs (congrArg (fun f : D →ₐ[K] Ω =>
      f.comp (IntermediateField.inclusion hED)) hf)
  have hj : embeddingRamificationOrder K (s.toAlgHom.comp D.val) D.val =
      embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val := by
    apply (ENNReal.toReal_eq_toReal_iff' (embeddingRamificationOrder_lt_top K hsD).ne
      (embeddingRamificationOrder_lt_top K hs).ne).mp
    have h := congrArg ENNReal.toReal (hJ (1 : H))
    simpa only [Subgroup.coe_one, mul_one] using h.trans heq
  exact congrArg (fun j : ℝ≥0∞ => ((j : EReal) - 1)) hj

end OriginalRelativePairBound

end FontaineWintenberger
