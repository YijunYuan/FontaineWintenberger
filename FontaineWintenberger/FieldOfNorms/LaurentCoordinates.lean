/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Constants
public import FontaineWintenberger.FieldOfNorms.Completeness
public import FontaineWintenberger.LocalField.LaurentCoordinates

/-!
# Laurent coordinates in the original field of norms

The source coefficient embedding and its induced actual residue isomorphism
identify the same original norm-limit field with Laurent series, for every
normalized original uniformizer.
-/

@[expose] public section

noncomputable section

open WithZero
open scoped Topology PowerSeries.WithPiTopology LaurentSeries

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L)

variable (u : NormLimit K L) (hu : normLimitValuation K L u = exp (-1 : ℤ))

/-- Evaluation in the actual original integer ring, using the constructed
source constants and precisely the residue isomorphism induced by them.
It is available for every original normalized uniformizer. -/
def normLimitPowerSeriesEquiv :
    PowerSeries κL ≃+* (normLimitFieldValuation K L).valuationSubring := by
  letI := normLimit_completeSpace K L
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuedPowerSeriesEquiv (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π hu

/-- The canonical Laurent-coordinate field isomorphism on the same original
norm-limit field, for every chosen original normalized uniformizer. -/
def normLimitLaurentEquiv :
    LaurentSeries κL ≃+* NormLimit K L := by
  letI := normLimit_completeSpace K L
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π hu

/-- Integral constants are exactly the original source coefficient section. -/
@[simp]
theorem normLimitPowerSeriesEquiv_C (a : κL) :
    normLimitPowerSeriesEquiv K L u hu (PowerSeries.C a) =
      sourceResidueConstantsIntegerHom K L a := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact valuedPowerSeriesEquiv_C (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    ⟨u, hu.le.trans (by simp)⟩ hu a

/-- The integral parameter represents precisely the chosen original uniformizer. -/
@[simp]
theorem normLimitPowerSeriesEquiv_X :
    (normLimitPowerSeriesEquiv K L u hu PowerSeries.X : NormLimit K L) = u := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact congrArg (fun z : (normLimitFieldValuation K L).valuationSubring =>
    (z : NormLimit K L)) (valuedPowerSeriesEquiv_X (NormLimit K L)
      (sourceResidueConstantsIntegerHom K L)
      (sourceResidueConstantsResidueEquiv K L)
      (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
      ⟨u, hu.le.trans (by simp)⟩ hu)

/-- The Laurent isomorphism extends the actual integral evaluation. -/
theorem normLimitLaurentEquiv_powerSeries (A : PowerSeries κL) :
    normLimitLaurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) A) =
        (normLimitPowerSeriesEquiv K L u hu A : NormLimit K L) := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_powerSeries (NormLimit K L) _ _ _ _ _ A

/-- The field constants are the actual source field embedding, including
its original inverse-Frobenius normalization. -/
@[simp]
theorem normLimitLaurentEquiv_C (a : κL) :
    normLimitLaurentEquiv K L u hu (algebraMap κL (LaurentSeries κL) a) =
      sourceResidueConstantsFieldEmbedding K L a := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_C (NormLimit K L) _ _ _ _ _ a

/-- The original Laurent parameter is exactly the chosen original norm family. -/
@[simp]
theorem normLimitLaurentEquiv_X :
    normLimitLaurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u := by
  rw [normLimitLaurentEquiv_powerSeries, normLimitPowerSeriesEquiv_X]

/-- Exact preservation of the original stable norm-limit valuation on every
Laurent series, including negative orders and zero. -/
theorem normLimitLaurentEquiv_valuation (A : LaurentSeries κL) :
    normLimitValuation K L (normLimitLaurentEquiv K L u hu A) =
      Valued.v A := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_laurentUniformizerEquiv (NormLimit K L) _ _ _ π hu A

/-- The original coordinate map is uniformly continuous for precisely the
already constructed stable-valuation uniformity on the original field. -/
theorem uniformContinuous_normLimitLaurentEquiv :
    UniformContinuous (normLimitLaurentEquiv K L u hu) := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv (NormLimit K L) _ _ _ π hu

/-- The inverse also preserves the original valuation uniformities. -/
theorem uniformContinuous_normLimitLaurentEquiv_symm :
    UniformContinuous (normLimitLaurentEquiv K L u hu).symm := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv_symm (NormLimit K L) _ _ _ π hu

/-- Continuity for the existing original norm-limit field topology. -/
theorem continuous_normLimitLaurentEquiv :
    Continuous (normLimitLaurentEquiv K L u hu) := by
  exact (uniformContinuous_normLimitLaurentEquiv K L u hu).continuous

/-- Continuity of the original Laurent expansion map. -/
theorem continuous_normLimitLaurentEquiv_symm :
    Continuous (normLimitLaurentEquiv K L u hu).symm := by
  exact (uniformContinuous_normLimitLaurentEquiv_symm K L u hu).continuous

/-- The actual source constants and chosen original uniformizer characterize
the continuous Laurent-coordinate field map uniquely. -/
theorem normLimitLaurentEquiv_unique :
    ∀ (f : LaurentSeries κL →+* NormLimit K L), Continuous f →
      (∀ a, f (algebraMap κL (LaurentSeries κL) a) =
        sourceResidueConstantsFieldEmbedding K L a) →
      f (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u →
      f = (normLimitLaurentEquiv K L u hu).toRingHom := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique (NormLimit K L) _ _ _ π hu f hf hC hX

/-- Integral evaluation is continuous for the inherited original integer
ring topology and the discrete-coefficient power-series topology. -/
theorem continuous_normLimitPowerSeriesEquiv :
    letI : UniformSpace κL := ⊥
    Continuous (normLimitPowerSeriesEquiv K L u hu) := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  let := valuationSubring_isDiscreteValuationRing_of_uniformizer (NormLimit K L) π hu
  let : IsUniformAddGroup
      (normLimitFieldValuation K L).valuationSubring :=
    valuationSubring_isUniformAddGroup (NormLimit K L)
  let : IsTopologicalRing
      (normLimitFieldValuation K L).valuationSubring :=
    valuationSubring_isTopologicalRing (NormLimit K L)
  let : IsLinearTopology
      (normLimitFieldValuation K L).valuationSubring
      (normLimitFieldValuation K L).valuationSubring :=
    valuationSubring_isLinearTopology (NormLimit K L)
  let : CompleteSpace (normLimitFieldValuation K L).valuationSubring :=
    valuationSubring_completeSpace (NormLimit K L)
  exact continuous_powerSeriesUniformizerEquiv
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π (irreducible_of_valuation_exp_neg_one (NormLimit K L) π hu)
    (hasEval_of_valuation_exp_neg_one (NormLimit K L) π hu)

/-- The same exact first-nonzero-coefficient valuation formula holds in the
original field of norms for the actual integral evaluation. -/
theorem normLimitPowerSeriesEquiv_valuation (A : PowerSeries κL) (hA : A ≠ 0) :
    normLimitValuation K L (normLimitPowerSeriesEquiv K L u hu A :
      NormLimit K L) = exp (-(A.order.toNat : ℤ)) := by
  let := normLimit_completeSpace K L
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_valuedPowerSeriesEquiv (NormLimit K L) _ _ _ π hu A hA

end FontaineWintenberger
