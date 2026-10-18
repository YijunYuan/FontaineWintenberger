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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L)

variable (u : NormLimit K L) (hu : normLimitValuation K L hL u = exp (-1 : ℤ))

/-- Evaluation in the actual original integer ring, using the constructed
source constants and precisely the residue isomorphism induced by them.
It is available for every original normalized uniformizer. -/
def normLimitPowerSeriesEquiv :
    letI := normLimitField K L p hL hInfinite
    PowerSeries κL ≃+* (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  letI := normLimitField K L p hL hInfinite
  letI := normLimitValued K L p hL hInfinite
  letI := normLimit_completeSpace K L p hL hInfinite
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuedPowerSeriesEquiv (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L p hL hInfinite)
    (sourceResidueConstantsResidueEquiv K L p hL hInfinite)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L p hL hInfinite x).symm)
    π hu

/-- The canonical Laurent-coordinate field isomorphism on the same original
norm-limit field, for every chosen original normalized uniformizer. -/
def normLimitLaurentEquiv :
    letI := normLimitField K L p hL hInfinite
    LaurentSeries κL ≃+* NormLimit K L := by
  letI := normLimitField K L p hL hInfinite
  letI := normLimitValued K L p hL hInfinite
  letI := normLimit_completeSpace K L p hL hInfinite
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L p hL hInfinite)
    (sourceResidueConstantsResidueEquiv K L p hL hInfinite)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L p hL hInfinite x).symm)
    π hu

/-- Integral constants are exactly the original source coefficient section. -/
@[simp]
theorem normLimitPowerSeriesEquiv_C (a : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitPowerSeriesEquiv K L p hL hInfinite u hu (PowerSeries.C a) =
      sourceResidueConstantsIntegerHom K L p hL hInfinite a := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact valuedPowerSeriesEquiv_C (NormLimit K L)
    (sourceResidueConstantsIntegerHom K L p hL hInfinite)
    (sourceResidueConstantsResidueEquiv K L p hL hInfinite)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L p hL hInfinite x).symm)
    ⟨u, hu.le.trans (by simp)⟩ hu a

/-- The integral parameter represents precisely the chosen original uniformizer. -/
@[simp]
theorem normLimitPowerSeriesEquiv_X :
    letI := normLimitField K L p hL hInfinite
    (normLimitPowerSeriesEquiv K L p hL hInfinite u hu PowerSeries.X : NormLimit K L) = u := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact congrArg (fun z : (normLimitFieldValuation K L p hL hInfinite).valuationSubring =>
    (z : NormLimit K L)) (valuedPowerSeriesEquiv_X (NormLimit K L)
      (sourceResidueConstantsIntegerHom K L p hL hInfinite)
      (sourceResidueConstantsResidueEquiv K L p hL hInfinite)
      (fun x => (sourceResidueConstantsResidueEquiv_apply K L p hL hInfinite x).symm)
      ⟨u, hu.le.trans (by simp)⟩ hu)

/-- The Laurent isomorphism extends the actual integral evaluation. -/
theorem normLimitLaurentEquiv_powerSeries (A : PowerSeries κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitLaurentEquiv K L p hL hInfinite u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) A) =
        (normLimitPowerSeriesEquiv K L p hL hInfinite u hu A : NormLimit K L) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_powerSeries (NormLimit K L) _ _ _ _ _ A

/-- The field constants are the actual source field embedding, including
its original inverse-Frobenius normalization. -/
@[simp]
theorem normLimitLaurentEquiv_C (a : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitLaurentEquiv K L p hL hInfinite u hu (algebraMap κL (LaurentSeries κL) a) =
      sourceResidueConstantsFieldEmbedding K L p hL hInfinite a := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_C (NormLimit K L) _ _ _ _ _ a

/-- The original Laurent parameter is exactly the chosen original norm family. -/
@[simp]
theorem normLimitLaurentEquiv_X :
    letI := normLimitField K L p hL hInfinite
    normLimitLaurentEquiv K L p hL hInfinite u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u := by
  rw [normLimitLaurentEquiv_powerSeries, normLimitPowerSeriesEquiv_X]

/-- Exact preservation of the original stable norm-limit valuation on every
Laurent series, including negative orders and zero. -/
theorem normLimitLaurentEquiv_valuation (A : LaurentSeries κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitValuation K L hL (normLimitLaurentEquiv K L p hL hInfinite u hu A) =
      Valued.v A := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_laurentUniformizerEquiv (NormLimit K L) _ _ _ π hu A

/-- The original coordinate map is uniformly continuous for precisely the
already constructed stable-valuation uniformity on the original field. -/
theorem uniformContinuous_normLimitLaurentEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    UniformContinuous (normLimitLaurentEquiv K L p hL hInfinite u hu) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv (NormLimit K L) _ _ _ π hu

/-- The inverse also preserves the original valuation uniformities. -/
theorem uniformContinuous_normLimitLaurentEquiv_symm :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    UniformContinuous (normLimitLaurentEquiv K L p hL hInfinite u hu).symm := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv_symm (NormLimit K L) _ _ _ π hu

/-- Continuity for the existing original norm-limit field topology. -/
theorem continuous_normLimitLaurentEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    Continuous (normLimitLaurentEquiv K L p hL hInfinite u hu) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  exact (uniformContinuous_normLimitLaurentEquiv K L p hL hInfinite u hu).continuous

/-- Continuity of the original Laurent expansion map. -/
theorem continuous_normLimitLaurentEquiv_symm :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    Continuous (normLimitLaurentEquiv K L p hL hInfinite u hu).symm := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  exact (uniformContinuous_normLimitLaurentEquiv_symm K L p hL hInfinite u hu).continuous

/-- The actual source constants and chosen original uniformizer characterize
the continuous Laurent-coordinate field map uniquely. -/
theorem normLimitLaurentEquiv_unique :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    ∀ (f : LaurentSeries κL →+* NormLimit K L), Continuous f →
      (∀ a, f (algebraMap κL (LaurentSeries κL) a) =
        sourceResidueConstantsFieldEmbedding K L p hL hInfinite a) →
      f (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u →
      f = (normLimitLaurentEquiv K L p hL hInfinite u hu).toRingHom := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique (NormLimit K L) _ _ _ π hu f hf hC hX

/-- Integral evaluation is continuous for the inherited original integer
ring topology and the discrete-coefficient power-series topology. -/
theorem continuous_normLimitPowerSeriesEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    letI : UniformSpace κL := ⊥
    Continuous (normLimitPowerSeriesEquiv K L p hL hInfinite u hu) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  let := valuationSubring_isDiscreteValuationRing_of_uniformizer (NormLimit K L) π hu
  let : IsUniformAddGroup
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    valuationSubring_isUniformAddGroup (NormLimit K L)
  let : IsTopologicalRing
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    valuationSubring_isTopologicalRing (NormLimit K L)
  let : IsLinearTopology
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    valuationSubring_isLinearTopology (NormLimit K L)
  let : CompleteSpace (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    valuationSubring_completeSpace (NormLimit K L)
  exact continuous_powerSeriesUniformizerEquiv
    (sourceResidueConstantsIntegerHom K L p hL hInfinite)
    (sourceResidueConstantsResidueEquiv K L p hL hInfinite)
    (fun x => (sourceResidueConstantsResidueEquiv_apply K L p hL hInfinite x).symm)
    π (irreducible_of_valuation_exp_neg_one (NormLimit K L) π hu)
    (hasEval_of_valuation_exp_neg_one (NormLimit K L) π hu)

/-- The same exact first-nonzero-coefficient valuation formula holds in the
original field of norms for the actual integral evaluation. -/
theorem normLimitPowerSeriesEquiv_valuation (A : PowerSeries κL) (hA : A ≠ 0) :
    letI := normLimitField K L p hL hInfinite
    normLimitValuation K L hL (normLimitPowerSeriesEquiv K L p hL hInfinite u hu A :
      NormLimit K L) = exp (-(A.order.toNat : ℤ)) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  let := normLimit_completeSpace K L p hL hInfinite
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (normLimitFieldValuation K L p hL hInfinite).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_valuedPowerSeriesEquiv (NormLimit K L) _ _ _ π hu A hA

end FontaineWintenberger
