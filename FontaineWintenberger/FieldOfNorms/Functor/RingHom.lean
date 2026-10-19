/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.Ramification.Embedding.Basic

/-!
# Finite embeddings of fields of norms

## Finite embeddings of the original norm fields

Good finite target fields and their original pullbacks preserve the actual
norm-sum limits. The resulting map is an injective field map, with positive
integral scaling of the same stable valuation and its original topology.

## Arbitrary finite embeddings of the original norm fields

A finite separable embedding factors through its actual field range.
The original range isomorphism and finite-inclusion maps give the same
norm-family map, now as an injective continuous field homomorphism.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FiniteIntermediateFields

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- Good target fields can simultaneously dominate a target field and the
actual image of any prescribed finite source field. -/
theorem exists_goodFiniteLayer_ge_pullback (D : FiniteIntermediateField K N)
    (C : FiniteIntermediateField K M) :
    ∃ F : FiniteIntermediateField K N, D ≤ F ∧ IsGoodFiniteLayer K M F ∧
      C ≤ FiniteIntermediateField.pullbackLayer K M F := by
  let i := IsScalarTower.toAlgHom K M N
  obtain ⟨F, hF, hg⟩ := exists_goodFiniteLayer_ge K M (FiniteIntermediateField.sup D
      (FiniteIntermediateField.map i C))
  refine ⟨F, (FiniteIntermediateField.le_sup_left D _).trans hF, hg, ?_⟩
  intro x hx
  exact hF (FiniteIntermediateField.le_sup_right D _ ⟨x, hx, rfl⟩)

/-- On an actual good pair, the target norm-sum term is literally the image
of the corresponding original source term. -/
theorem normSumNet_finiteFieldOfNormsMap (D F : FiniteIntermediateField K N) (hDF : D ≤ F)
    (hD : IsGoodFiniteLayer K M D) (hF : IsGoodFiniteLayer K M F)
    (x y : FieldOfNorms K M) :
    normSumNet K N D (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y)
        ⟨F, hDF⟩ =
      FiniteIntermediateField.pullbackTo K M D
        (normSumNet K M (FiniteIntermediateField.pullbackLayer K M D) x y
          ⟨FiniteIntermediateField.pullbackLayer K M F, FiniteIntermediateField.pullback_mono K M
              hDF⟩) := by
  change FiniteIntermediateField.norm D F hDF
      (FieldOfNorms.coord K N F (FieldOfNorms.finiteMap K M N x) +
        FieldOfNorms.coord K N F (FieldOfNorms.finiteMap K M N y)) = _
  rw [FieldOfNorms.coord_finiteFieldOfNormsMap K M N F hF,
    FieldOfNorms.coord_finiteFieldOfNormsMap K M N F hF]
  exact (congrArg (FiniteIntermediateField.norm D F hDF)
    (map_add (FiniteIntermediateField.pullbackTo K M F)
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) x)
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) y)).symm).trans
    (goodFinitePair_norm K M D F hDF hD hF
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) x +
        FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) y))

end FiniteIntermediateFields

section NormalizedValuation

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K

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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The two original sum limits agree at every good finite target coordinate,
by comparison on the same genuinely directed cofinal set. -/
theorem FieldOfNorms.finiteMap_add_coordinate [IsAPF K M] [IsAPF K N]
    (D : FiniteIntermediateField K N) (hD : IsGoodFiniteLayer K M D) (x y : FieldOfNorms K M) :
    FieldOfNorms.coord K N D (FieldOfNorms.finiteMap K M N (FieldOfNorms.add K M x y)) =
      FieldOfNorms.coord K N D (FieldOfNorms.add K N
        (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y)) := by
  let C := FiniteIntermediateField.pullbackLayer K M D
  let S := {F : FiniteIntermediateField K N // D ≤ F ∧ IsGoodFiniteLayer K M F}
  let : Nonempty S := ⟨⟨D, le_rfl, hD⟩⟩
  let : IsDirectedOrder S := ⟨fun F G => by
    obtain ⟨H, hFH, hGH, hH⟩ := exists_goodFiniteLayer_ge_pair K M F.val G.val
    exact ⟨⟨H, F.property.1.trans hFH, hH⟩, hFH, hGH⟩⟩
  let u (F : S) : Set.Ici D := ⟨F.val, F.property.1⟩
  let v (F : S) : Set.Ici C :=
    ⟨FiniteIntermediateField.pullbackLayer K M F.val, FiniteIntermediateField.pullback_mono K M
        F.property.1⟩
  have hu : Tendsto u atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hF, hAF⟩ := goodFiniteLayers_cofinal K M N A.val
    exact ⟨⟨F, A.property.trans hAF, hF⟩, fun G hFG => hAF.trans hFG⟩
  have hv : Tendsto v atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hDF, hF, hAF⟩ := exists_goodFiniteLayer_ge_pullback K M N D A.val
    exact ⟨⟨F, hDF, hF⟩, fun G hFG => hAF.trans (FiniteIntermediateField.pullback_mono K M hFG)⟩
  let := spectralNorm.nontriviallyNormedField K (FiniteIntermediateField.pullback K M D)
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K (FiniteIntermediateField.pullback K M D)
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteIntermediateField.pullbackTo K M D) :=
    (FiniteIntermediateField.pullbackTo K M D).toLinearMap.continuous_of_finiteDimensional
  have hsource := hc.continuousAt.tendsto.comp
    ((tendsto_normSumNet_fieldOfNormsAdd K M x y C).comp hv)
  have htarget := (tendsto_normSumNet_fieldOfNormsAdd K N
    (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y) D).comp hu
  have heq : (fun F : S => normSumNet K N D
      (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y) (u F)) =
      fun F : S => FiniteIntermediateField.pullbackTo K M D (normSumNet K M C x y (v F)) := by
    funext F
    exact normSumNet_finiteFieldOfNormsMap K M N D F.val F.property.1 hD F.property.2 x y
  change Tendsto (fun F : S => normSumNet K N D
    (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y) (u F)) _ _ at htarget
  rw [heq] at htarget
  exact (FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD _).trans
    (tendsto_nhds_unique hsource htarget)

/-- The literal finite-inclusion map preserves the actual field of norms addition. -/
theorem FieldOfNorms.finiteMap_add [IsAPF K M] [IsAPF K N]
    (x y : FieldOfNorms K M) :
    FieldOfNorms.finiteMap K M N (FieldOfNorms.add K M x y) =
      FieldOfNorms.add K N (FieldOfNorms.finiteMap K M N x) (FieldOfNorms.finiteMap K M N y) := by
  apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  exact FieldOfNorms.finiteMap_add_coordinate K M N D hD x y

/-- The actual finite-inclusion map is a field homomorphism on the original
field of norms carriers and their already constructed field structures. -/
def FieldOfNorms.finiteRingHom [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    FieldOfNorms K M →+* FieldOfNorms K N := by
  exact { FieldOfNorms.finiteMap K M N with
    map_add' := FieldOfNorms.finiteMap_add K M N }

@[simp]
theorem FieldOfNorms.finiteRingHom_apply [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (x : FieldOfNorms K M) :
    FieldOfNorms.finiteRingHom K M N x =
      FieldOfNorms.finiteMap K M N x := rfl

/-- Unitality and the actual original field structures give injectivity. -/
theorem FieldOfNorms.finiteMap_injective [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    Function.Injective (FieldOfNorms.finiteMap K M N) := by
  exact (FieldOfNorms.finiteRingHom K M N).injective

/-- An actual good field on both stable tails computes one fixed positive
finite valuation exponent for every original norm family, including zero. -/
theorem exists_goodFiniteLayer_finiteFieldOfNormsMap_valuation
    [IsAPF K M] [IsAPF K N] :
    ∃ D : FiniteIntermediateField K N, IsGoodFiniteLayer K M D ∧
      0 < embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) ∧
      ∀ x : FieldOfNorms K M,
        FieldOfNorms.valuation K N (FieldOfNorms.finiteMap K M N x) =
          FieldOfNorms.valuation K M x ^
            embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) := by
  obtain ⟨C₀, hC₀⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K M
  obtain ⟨D₀, hD₀⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K N
  obtain ⟨D, hD₀D, hD, hC₀D⟩ := exists_goodFiniteLayer_ge_pullback K M N D₀ C₀
  let C := FiniteIntermediateField.pullbackLayer K M D
  refine ⟨D, hD, embeddingRamificationIdx_pos K (FiniteIntermediateField.pullbackTo K M D), fun x
      => ?_⟩
  calc
    FieldOfNorms.valuation K N (FieldOfNorms.finiteMap K M N x) =
        FieldOfNorms.coordinateValuation K N D (FieldOfNorms.finiteMap K M N x) :=
      hD₀ D hD₀D _
    _ = (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
        D.val (FiniteIntermediateField.pullbackTo K M D (FieldOfNorms.coord K M C x)) :=
      congrArg ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
          D.val)
        (FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD x)
    _ = FieldOfNorms.coordinateValuation K M C x ^
        embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) :=
      spectral_normalizedValuation_algHom K (FiniteIntermediateField.pullbackTo K M D)
        (FieldOfNorms.coord K M C x)
    _ = FieldOfNorms.valuation K M x ^
        embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) :=
      congrArg (fun z => z ^ embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D))
        (hC₀ C hC₀D x).symm

/-- Positive integral scaling is produced from an actual original finite
integer-ring inclusion, rather than supplied as an additional hypothesis. -/
theorem exists_finiteFieldOfNormsMap_valuation_scaling [IsAPF K M] [IsAPF K N] :
    ∃ e : ℕ, 0 < e ∧ ∀ x : FieldOfNorms K M,
      FieldOfNorms.valuation K N (FieldOfNorms.finiteMap K M N x) =
        FieldOfNorms.valuation K M x ^ e := by
  obtain ⟨D, _, he, hv⟩ := exists_goodFiniteLayer_finiteFieldOfNormsMap_valuation K M N
  exact ⟨embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D), he, hv⟩

/-- The actual finite-inclusion map is uniformly continuous for the existing
valuation uniformities, by its proved positive integral scaling. -/
theorem uniformContinuous_finiteFieldOfNormsMap [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    UniformContinuous (FieldOfNorms.finiteMap K M N) := by
  obtain ⟨e, he, hv⟩ := exists_finiteFieldOfNormsMap_valuation_scaling K M N
  have hbM := Valued.nhds_zero_hasBasis_integer_closedBall (FieldOfNorms K M)
    (FieldOfNorms.uniformizer K M)
    (FieldOfNorms.valuation_fieldOfNormsUniformizer K M)
  have hbN := Valued.nhds_zero_hasBasis_integer_closedBall (FieldOfNorms K N)
    (FieldOfNorms.uniformizer K N)
    (FieldOfNorms.valuation_fieldOfNormsUniformizer K N)
  change UniformContinuous (FieldOfNorms.finiteRingHom K M N)
  apply uniformContinuous_of_continuousAt_zero
    (FieldOfNorms.finiteRingHom K M N).toAddMonoidHom
  simp only [ContinuousAt, map_zero, hbM.tendsto_iff hbN, true_and, forall_const]
  intro n
  refine ⟨n, fun x hx => ?_⟩
  change FieldOfNorms.valuation K N (FieldOfNorms.finiteMap K M N x) ≤
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
theorem continuous_finiteFieldOfNormsMap [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    Continuous (FieldOfNorms.finiteMap K M N) := by
  exact (uniformContinuous_finiteFieldOfNormsMap K M N).continuous

end ValuedFields

end FontaineWintenberger

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
