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
identify the same original field of norms field with Laurent series, for every
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

variable (u : FieldOfNorms K L) (hu : FieldOfNorms.valuation K L u = exp (-1 : ℤ))

/-- Evaluation in the actual original integer ring, using the constructed
source constants and precisely the residue isomorphism induced by them.
It is available for every original normalized uniformizer. -/
def FieldOfNorms.powerSeriesEquiv :
    PowerSeries κL ≃+* (FieldOfNorms.fieldValuation K L).valuationSubring := by
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuedPowerSeriesEquiv (FieldOfNorms K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π hu

/-- The canonical Laurent-coordinate field isomorphism on the same original
field of norms field, for every chosen original normalized uniformizer. -/
def FieldOfNorms.laurentEquiv :
    LaurentSeries κL ≃+* FieldOfNorms K L := by
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv (FieldOfNorms K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π hu

/-- Integral constants are exactly the original source coefficient section. -/
@[simp]
theorem FieldOfNorms.powerSeriesEquiv_C (a : κL) :
    FieldOfNorms.powerSeriesEquiv K L u hu (PowerSeries.C a) =
      sourceResidueConstantsIntegerHom K L a := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact valuedPowerSeriesEquiv_C (FieldOfNorms K L)
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    ⟨u, hu.le.trans (by simp)⟩ hu a

/-- The integral parameter represents precisely the chosen original uniformizer. -/
@[simp]
theorem FieldOfNorms.powerSeriesEquiv_X :
    (FieldOfNorms.powerSeriesEquiv K L u hu PowerSeries.X : FieldOfNorms K L) = u := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact congrArg (fun z : (FieldOfNorms.fieldValuation K L).valuationSubring =>
    (z : FieldOfNorms K L)) (valuedPowerSeriesEquiv_X (FieldOfNorms K L)
      (sourceResidueConstantsIntegerHom K L)
      (sourceResidueConstantsResidueEquiv K L)
      (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
      ⟨u, hu.le.trans (by simp)⟩ hu)

/-- The Laurent isomorphism extends the actual integral evaluation. -/
theorem FieldOfNorms.laurentEquiv_powerSeries (A : PowerSeries κL) :
    FieldOfNorms.laurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) A) =
        (FieldOfNorms.powerSeriesEquiv K L u hu A : FieldOfNorms K L) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_powerSeries (FieldOfNorms K L) _ _ _ _ _ A

/-- The field constants are the actual source field embedding, including
its original inverse-Frobenius normalization. -/
@[simp]
theorem FieldOfNorms.laurentEquiv_C (a : κL) :
    FieldOfNorms.laurentEquiv K L u hu (algebraMap κL (LaurentSeries κL) a) =
      sourceResidueConstantsFieldEmbedding K L a := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_C (FieldOfNorms K L) _ _ _ _ _ a

/-- The original Laurent parameter is exactly the chosen original norm family. -/
@[simp]
theorem FieldOfNorms.laurentEquiv_X :
    FieldOfNorms.laurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u := by
  rw [FieldOfNorms.laurentEquiv_powerSeries, FieldOfNorms.powerSeriesEquiv_X]

/-- Exact preservation of the original stable field of norms valuation on every
Laurent series, including negative orders and zero. -/
theorem FieldOfNorms.laurentEquiv_valuation (A : LaurentSeries κL) :
    FieldOfNorms.valuation K L (FieldOfNorms.laurentEquiv K L u hu A) =
      Valued.v A := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_laurentUniformizerEquiv (FieldOfNorms K L) _ _ _ π hu A

/-- The original coordinate map is uniformly continuous for precisely the
already constructed stable-valuation uniformity on the original field. -/
theorem uniformContinuous_fieldOfNormsLaurentEquiv :
    UniformContinuous (FieldOfNorms.laurentEquiv K L u hu) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv (FieldOfNorms K L) _ _ _ π hu

/-- The inverse also preserves the original valuation uniformities. -/
theorem uniformContinuous_fieldOfNormsLaurentEquiv_symm :
    UniformContinuous (FieldOfNorms.laurentEquiv K L u hu).symm := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv_symm (FieldOfNorms K L) _ _ _ π hu

/-- Continuity for the existing original field of norms field topology. -/
theorem continuous_fieldOfNormsLaurentEquiv :
    Continuous (FieldOfNorms.laurentEquiv K L u hu) := by
  exact (uniformContinuous_fieldOfNormsLaurentEquiv K L u hu).continuous

/-- Continuity of the original Laurent expansion map. -/
theorem continuous_fieldOfNormsLaurentEquiv_symm :
    Continuous (FieldOfNorms.laurentEquiv K L u hu).symm := by
  exact (uniformContinuous_fieldOfNormsLaurentEquiv_symm K L u hu).continuous

/-- The actual source constants and chosen original uniformizer characterize
the continuous Laurent-coordinate field map uniquely. -/
theorem FieldOfNorms.laurentEquiv_unique :
    ∀ (f : LaurentSeries κL →+* FieldOfNorms K L), Continuous f →
      (∀ a, f (algebraMap κL (LaurentSeries κL) a) =
        sourceResidueConstantsFieldEmbedding K L a) →
      f (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u →
      f = (FieldOfNorms.laurentEquiv K L u hu).toRingHom := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique (FieldOfNorms K L) _ _ _ π hu f hf hC hX

/-- Integral evaluation is continuous for the inherited original integer
ring topology and the discrete-coefficient power-series topology. -/
theorem continuous_fieldOfNormsPowerSeriesEquiv :
    letI : UniformSpace κL := ⊥
    Continuous (FieldOfNorms.powerSeriesEquiv K L u hu) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  let := valuationSubring_isDiscreteValuationRing_of_uniformizer (FieldOfNorms K L) π hu
  let : IsUniformAddGroup
      (FieldOfNorms.fieldValuation K L).valuationSubring :=
    valuationSubring_isUniformAddGroup (FieldOfNorms K L)
  let : IsTopologicalRing
      (FieldOfNorms.fieldValuation K L).valuationSubring :=
    valuationSubring_isTopologicalRing (FieldOfNorms K L)
  let : IsLinearTopology
      (FieldOfNorms.fieldValuation K L).valuationSubring
      (FieldOfNorms.fieldValuation K L).valuationSubring :=
    valuationSubring_isLinearTopology (FieldOfNorms K L)
  let : CompleteSpace (FieldOfNorms.fieldValuation K L).valuationSubring :=
    valuationSubring_completeSpace (FieldOfNorms K L)
  exact continuous_powerSeriesUniformizerEquiv
    (sourceResidueConstantsIntegerHom K L)
    (sourceResidueConstantsResidueEquiv K L)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L x).symm)
    π (irreducible_of_valuation_exp_neg_one (FieldOfNorms K L) π hu)
    (hasEval_of_valuation_exp_neg_one (FieldOfNorms K L) π hu)

/-- The same exact first-nonzero-coefficient valuation formula holds in the
original field of norms for the actual integral evaluation. -/
theorem FieldOfNorms.powerSeriesEquiv_valuation (A : PowerSeries κL) (hA : A ≠ 0) :
    FieldOfNorms.valuation K L (FieldOfNorms.powerSeriesEquiv K L u hu A :
      FieldOfNorms K L) = exp (-(A.order.toNat : ℤ)) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_valuedPowerSeriesEquiv (FieldOfNorms K L) _ _ _ π hu A hA

end FontaineWintenberger
