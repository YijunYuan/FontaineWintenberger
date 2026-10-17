/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.FiniteFunctor
public import FontaineWintenberger.FieldOfNorms.Isomorphism
public import FontaineWintenberger.FieldOfNorms.Completeness
public import FontaineWintenberger.Ramification.Embedding

/-!
# Finite embeddings of the original norm fields

Good finite target fields and their original pullbacks preserve the actual
norm-sum limits. The resulting map is an injective field map, with positive
integral scaling of the same stable valuation and its original topology.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FiniteLayers

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- Good target fields can simultaneously dominate a target field and the
actual image of any prescribed finite source field. -/
theorem exists_goodFiniteLayer_ge_pullback (D : FiniteLayer K N)
    (C : FiniteLayer K M) :
    ∃ F : FiniteLayer K N, D ≤ F ∧ IsGoodFiniteLayer K M F ∧
      C ≤ finiteLayerPullbackLayer K M F := by
  let i := IsScalarTower.toAlgHom K M N
  obtain ⟨F, hF, hg⟩ := exists_goodFiniteLayer_ge K M (FiniteLayer.sup D (FiniteLayer.map i C))
  refine ⟨F, (FiniteLayer.le_sup_left D _).trans hF, hg, ?_⟩
  intro x hx
  exact hF (FiniteLayer.le_sup_right D _ ⟨x, hx, rfl⟩)

/-- On an actual good pair, the target norm-sum term is literally the image
of the corresponding original source term. -/
theorem normSumNet_finiteNormLimitMap (D F : FiniteLayer K N) (hDF : D ≤ F)
    (hD : IsGoodFiniteLayer K M D) (hF : IsGoodFiniteLayer K M F)
    (x y : NormLimit K M) :
    normSumNet K N D (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y)
        ⟨F, hDF⟩ =
      finiteLayerPullbackTo K M D
        (normSumNet K M (finiteLayerPullbackLayer K M D) x y
          ⟨finiteLayerPullbackLayer K M F, finiteLayerPullback_mono K M hDF⟩) := by
  change FiniteLayer.norm D F hDF
      (normLimitEval K N F (finiteNormLimitMap K M N x) +
        normLimitEval K N F (finiteNormLimitMap K M N y)) = _
  rw [normLimitEval_finiteNormLimitMap K M N F hF,
    normLimitEval_finiteNormLimitMap K M N F hF]
  exact (congrArg (FiniteLayer.norm D F hDF)
    (map_add (finiteLayerPullbackTo K M F)
      (normLimitEval K M (finiteLayerPullbackLayer K M F) x)
      (normLimitEval K M (finiteLayerPullbackLayer K M F) y)).symm).trans
    (goodFinitePair_norm K M D F hDF hD hF
      (normLimitEval K M (finiteLayerPullbackLayer K M F) x +
        normLimitEval K M (finiteLayerPullbackLayer K M F) y))

end FiniteLayers

section NormalizedValuation

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] [FiniteDimensional K F]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K F]

/-- The actual finite-field embedding scales normalized valuations by its
actual positive local ramification index, for every field element. -/
theorem spectral_normalizedValuation_algHom (i : E →ₐ[K] F) (x : E) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F)).valuation F (i x) =
      ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E)).valuation E x) ^
        embeddingRamificationIdx K i := by
  let R := spectralIntegerRing K E
  let S := spectralIntegerRing K F
  let : Algebra E F := i.toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun r => (i.commutes r).symm)
  let : Algebra R S := (spectralIntegerInclusion K i).toRingHom.toAlgebra
  let : Algebra R F := (i.toRingHom.comp (algebraMap R E)).toAlgebra
  let : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro a b hab
    apply Subtype.ext
    exact i.injective (congrArg (fun z : S => (z : F)) hab))
  let : IsLocalHom (algebraMap R S) :=
    ⟨(spectralIntegerInclusion_isLocalHom K i).map_nonunit⟩
  exact normalizedValuation_algebraMap R S E F x

end NormalizedValuation

section ValuedFields

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Module.Finite M N] [Algebra.IsSeparable M N]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The two original sum limits agree at every good finite target coordinate,
by comparison on the same genuinely directed cofinal set. -/
theorem finiteNormLimitMap_add_coordinate (hM : IsAPF K M) (hN : IsAPF K N)
    (D : FiniteLayer K N) (hD : IsGoodFiniteLayer K M D) (x y : NormLimit K M) :
    normLimitEval K N D (finiteNormLimitMap K M N (normLimitAdd K M p hM x y)) =
      normLimitEval K N D (normLimitAdd K N p hN
        (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y)) := by
  let C := finiteLayerPullbackLayer K M D
  let S := {F : FiniteLayer K N // D ≤ F ∧ IsGoodFiniteLayer K M F}
  let : Nonempty S := ⟨⟨D, le_rfl, hD⟩⟩
  let : IsDirectedOrder S := ⟨fun F G => by
    obtain ⟨H, hFH, hGH, hH⟩ := exists_goodFiniteLayer_ge_pair K M F.val G.val
    exact ⟨⟨H, F.property.1.trans hFH, hH⟩, hFH, hGH⟩⟩
  let u (F : S) : Set.Ici D := ⟨F.val, F.property.1⟩
  let v (F : S) : Set.Ici C :=
    ⟨finiteLayerPullbackLayer K M F.val, finiteLayerPullback_mono K M F.property.1⟩
  have hu : Tendsto u atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hF, hAF⟩ := goodFiniteLayers_cofinal K M N A.val
    exact ⟨⟨F, A.property.trans hAF, hF⟩, fun G hFG => hAF.trans hFG⟩
  have hv : Tendsto v atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hDF, hF, hAF⟩ := exists_goodFiniteLayer_ge_pullback K M N D A.val
    exact ⟨⟨F, hDF, hF⟩, fun G hFG => hAF.trans (finiteLayerPullback_mono K M hFG)⟩
  let := spectralNorm.nontriviallyNormedField K (finiteLayerPullback K M D)
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K (finiteLayerPullback K M D)
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (finiteLayerPullbackTo K M D) :=
    (finiteLayerPullbackTo K M D).toLinearMap.continuous_of_finiteDimensional
  have hsource := hc.continuousAt.tendsto.comp
    ((tendsto_normSumNet_normLimitAdd K M p hM x y C).comp hv)
  have htarget := (tendsto_normSumNet_normLimitAdd K N p hN
    (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y) D).comp hu
  have heq : (fun F : S => normSumNet K N D
      (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y) (u F)) =
      fun F : S => finiteLayerPullbackTo K M D (normSumNet K M C x y (v F)) := by
    funext F
    exact normSumNet_finiteNormLimitMap K M N D F.val F.property.1 hD F.property.2 x y
  change Tendsto (fun F : S => normSumNet K N D
    (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y) (u F)) _ _ at htarget
  rw [heq] at htarget
  exact (normLimitEval_finiteNormLimitMap K M N D hD _).trans
    (tendsto_nhds_unique hsource htarget)

/-- The literal finite-inclusion map preserves the actual norm-limit addition. -/
theorem finiteNormLimitMap_add (hM : IsAPF K M) (hN : IsAPF K N)
    (x y : NormLimit K M) :
    finiteNormLimitMap K M N (normLimitAdd K M p hM x y) =
      normLimitAdd K N p hN (finiteNormLimitMap K M N x) (finiteNormLimitMap K M N y) := by
  apply NormLimit.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  exact finiteNormLimitMap_add_coordinate K M N p hM hN D hD x y

/-- The actual finite-inclusion map is a field homomorphism on the original
norm-limit carriers and their already constructed field structures. -/
def finiteNormLimitRingHom (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    NormLimit K M →+* NormLimit K N := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  exact { finiteNormLimitMap K M N with
    map_add' := finiteNormLimitMap_add K M N p hM hN }

@[simp]
theorem finiteNormLimitRingHom_apply (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N)
    (x : NormLimit K M) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN x =
      finiteNormLimitMap K M N x := rfl

include p in
/-- Unitality and the actual original field structures give injectivity. -/
theorem finiteNormLimitMap_injective (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    Function.Injective (finiteNormLimitMap K M N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  exact (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).injective

/-- An actual good field on both stable tails computes one fixed positive
finite valuation exponent for every original norm family, including zero. -/
theorem exists_goodFiniteLayer_finiteNormLimitMap_valuation
    (hM : IsAPF K M) (hN : IsAPF K N) :
    ∃ D : FiniteLayer K N, IsGoodFiniteLayer K M D ∧
      0 < embeddingRamificationIdx K (finiteLayerPullbackTo K M D) ∧
      ∀ x : NormLimit K M,
        normLimitValuation K N hN (finiteNormLimitMap K M N x) =
          normLimitValuation K M hM x ^
            embeddingRamificationIdx K (finiteLayerPullbackTo K M D) := by
  obtain ⟨C₀, hC₀⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K M hM
  obtain ⟨D₀, hD₀⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K N hN
  obtain ⟨D, hD₀D, hD, hC₀D⟩ := exists_goodFiniteLayer_ge_pullback K M N D₀ C₀
  let C := finiteLayerPullbackLayer K M D
  refine ⟨D, hD, embeddingRamificationIdx_pos K (finiteLayerPullbackTo K M D), fun x => ?_⟩
  calc
    normLimitValuation K N hN (finiteNormLimitMap K M N x) =
        normLimitCoordinateValuation K N D (finiteNormLimitMap K M N x) :=
      hD₀ D hD₀D _
    _ = (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
        D.val (finiteLayerPullbackTo K M D (normLimitEval K M C x)) :=
      congrArg ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
          D.val)
        (normLimitEval_finiteNormLimitMap K M N D hD x)
    _ = normLimitCoordinateValuation K M C x ^
        embeddingRamificationIdx K (finiteLayerPullbackTo K M D) :=
      spectral_normalizedValuation_algHom K (finiteLayerPullbackTo K M D)
        (normLimitEval K M C x)
    _ = normLimitValuation K M hM x ^
        embeddingRamificationIdx K (finiteLayerPullbackTo K M D) :=
      congrArg (fun z => z ^ embeddingRamificationIdx K (finiteLayerPullbackTo K M D))
        (hC₀ C hC₀D x).symm

/-- Positive integral scaling is produced from an actual original finite
integer-ring inclusion, rather than supplied as an additional hypothesis. -/
theorem exists_finiteNormLimitMap_valuation_scaling (hM : IsAPF K M) (hN : IsAPF K N) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : NormLimit K M,
      normLimitValuation K N hN (finiteNormLimitMap K M N x) =
        normLimitValuation K M hM x ^ e := by
  obtain ⟨D, _, he, hv⟩ := exists_goodFiniteLayer_finiteNormLimitMap_valuation K M N hM hN
  exact ⟨embeddingRamificationIdx K (finiteLayerPullbackTo K M D), he, hv⟩

/-- The actual finite-inclusion map is uniformly continuous for the existing
valuation uniformities, by its proved positive integral scaling. -/
theorem uniformContinuous_finiteNormLimitMap (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := normLimitValued K M p hM hInfiniteM
    letI := normLimitValued K N p hN hInfiniteN
    UniformContinuous (finiteNormLimitMap K M N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := normLimitValued K M p hM hInfiniteM
  let := normLimitValued K N p hN hInfiniteN
  obtain ⟨e, he, hv⟩ := exists_finiteNormLimitMap_valuation_scaling K M N hM hN
  have hbM := Valued.nhds_zero_hasBasis_integer_closedBall (NormLimit K M)
    (normLimitUniformizer K M p hM hInfiniteM)
    (normLimitValuation_normLimitUniformizer K M p hM hInfiniteM)
  have hbN := Valued.nhds_zero_hasBasis_integer_closedBall (NormLimit K N)
    (normLimitUniformizer K N p hN hInfiniteN)
    (normLimitValuation_normLimitUniformizer K N p hN hInfiniteN)
  change UniformContinuous (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN)
  apply uniformContinuous_of_continuousAt_zero
    (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAddMonoidHom
  simp only [ContinuousAt, map_zero, hbM.tendsto_iff hbN, true_and, forall_const]
  intro n
  refine ⟨n, fun x hx => ?_⟩
  change normLimitValuation K N hN (finiteNormLimitMap K M N x) ≤
    WithZero.exp (-((n + 2 : ℕ) : ℤ))
  rw [hv x]
  have hpow : WithZero.exp (-((n + 2 : ℕ) : ℤ)) ^ e ≤
      WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
    have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
    simp only [nsmul_eq_mul]
    nlinarith
  exact (pow_le_pow_left₀ zero_le hx e).trans hpow

/-- Continuity uses the original valuation topology on each original norm field. -/
theorem continuous_finiteNormLimitMap (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := normLimitValued K M p hM hInfiniteM
    letI := normLimitValued K N p hN hInfiniteN
    Continuous (finiteNormLimitMap K M N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := normLimitValued K M p hM hInfiniteM
  let := normLimitValued K N p hN hInfiniteN
  exact (uniformContinuous_finiteNormLimitMap K M N p hM hN hInfiniteM hInfiniteN).continuous

end ValuedFields

end FontaineWintenberger
