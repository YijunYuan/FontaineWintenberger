/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.ResidueEmbedding
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.LocalField.Laurent.Coordinates

/-!
# Laurent coordinates in the field of norms

The coefficient embedding and its induced residue isomorphism
identify the field of norms field with Laurent series, for every
normalized uniformizer.

## Main definitions

* `FieldOfNorms.powerSeriesEquiv`: Evaluation in the integer ring, using the constructed constants
  and precisely the residue isomorphism induced by them.
* `FieldOfNorms.laurentEquiv`: The canonical Laurent-coordinate field isomorphism on the same field
  of norms field, for every chosen normalized uniformizer.

## Main results

* `FieldOfNorms.powerSeriesEquiv_C`: Integral constants are exactly the coefficient section.
* `FieldOfNorms.powerSeriesEquiv_X`: The integral parameter represents precisely the chosen
  uniformizer.
* `FieldOfNorms.laurentEquiv_powerSeries`: The Laurent isomorphism extends the integral evaluation.
* `FieldOfNorms.laurentEquiv_C`: The field constants are the field embedding, including its
  inverse-Frobenius normalization.
* `FieldOfNorms.laurentEquiv_X`: The Laurent parameter is exactly the chosen norm family.
* `FieldOfNorms.laurentEquiv_valuation`: Exact preservation of the stable field of norms valuation
  on every Laurent series, including negative orders and zero.
* `FieldOfNorms.uniformContinuous_laurentEquiv`: The coordinate map is uniformly continuous for
  precisely the already constructed stable-valuation uniformity on the field.
* `FieldOfNorms.uniformContinuous_laurentEquiv_symm`: The inverse also preserves the valuation
  uniformities.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
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
  (integralClosure 𝒪[K] L)

variable (u : FieldOfNorms K L) (hu : FieldOfNorms.valuation K L u = exp (-1 : ℤ))

/-- Evaluation in the integer ring, using the constructed
constants and precisely the residue isomorphism induced by them.
It is available for every normalized uniformizer. -/
def FieldOfNorms.powerSeriesEquiv :
    PowerSeries κL ≃+* (FieldOfNorms.fieldValuation K L).valuationSubring := by
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuedPowerSeriesEquiv (FieldOfNorms K L)
    (residueConstantsIntegerHom K L)
    (FieldOfNorms.residueEquiv K L)
    (fun x => (FieldOfNorms.residueEquiv_apply K L x).symm)
    π hu

/-- The canonical Laurent-coordinate field isomorphism on the same
field of norms field, for every chosen normalized uniformizer. -/
def FieldOfNorms.laurentEquiv :
    LaurentSeries κL ≃+* FieldOfNorms K L := by
  letI : UniformSpace κL := ⊥
  letI : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact laurentUniformizerEquiv (FieldOfNorms K L)
    (residueConstantsIntegerHom K L)
    (FieldOfNorms.residueEquiv K L)
    (fun x => (FieldOfNorms.residueEquiv_apply K L x).symm)
    π hu

/-- Integral constants are exactly the coefficient section. -/
@[simp]
theorem FieldOfNorms.powerSeriesEquiv_C (a : κL) :
    FieldOfNorms.powerSeriesEquiv K L u hu (PowerSeries.C a) =
      residueConstantsIntegerHom K L a := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact valuedPowerSeriesEquiv_C (FieldOfNorms K L)
    (residueConstantsIntegerHom K L)
    (FieldOfNorms.residueEquiv K L)
    (fun x => (FieldOfNorms.residueEquiv_apply K L x).symm)
    ⟨u, hu.le.trans (by simp)⟩ hu a

/-- The integral parameter represents precisely the chosen uniformizer. -/
@[simp]
theorem FieldOfNorms.powerSeriesEquiv_X :
    (FieldOfNorms.powerSeriesEquiv K L u hu PowerSeries.X : FieldOfNorms K L) = u := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact congrArg (fun z : (FieldOfNorms.fieldValuation K L).valuationSubring =>
    (z : FieldOfNorms K L)) (valuedPowerSeriesEquiv_X (FieldOfNorms K L)
      (residueConstantsIntegerHom K L)
      (FieldOfNorms.residueEquiv K L)
      (fun x => (FieldOfNorms.residueEquiv_apply K L x).symm)
      ⟨u, hu.le.trans (by simp)⟩ hu)

/-- The Laurent isomorphism extends the integral evaluation. -/
theorem FieldOfNorms.laurentEquiv_powerSeries (A : PowerSeries κL) :
    FieldOfNorms.laurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) A) =
        (FieldOfNorms.powerSeriesEquiv K L u hu A : FieldOfNorms K L) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_powerSeries (FieldOfNorms K L) _ _ _ _ _ A

/-- The field constants are the field embedding, including
its inverse-Frobenius normalization. -/
@[simp]
theorem FieldOfNorms.laurentEquiv_C (a : κL) :
    FieldOfNorms.laurentEquiv K L u hu (algebraMap κL (LaurentSeries κL) a) =
      residueConstantsFieldEmbedding K L a := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  exact laurentUniformizerEquiv_C (FieldOfNorms K L) _ _ _ _ _ a

/-- The Laurent parameter is exactly the chosen norm family. -/
@[simp]
theorem FieldOfNorms.laurentEquiv_X :
    FieldOfNorms.laurentEquiv K L u hu
      (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u := by
  rw [FieldOfNorms.laurentEquiv_powerSeries, FieldOfNorms.powerSeriesEquiv_X]

/-- Exact preservation of the stable field of norms valuation on every
Laurent series, including negative orders and zero. -/
theorem FieldOfNorms.laurentEquiv_valuation (A : LaurentSeries κL) :
    FieldOfNorms.valuation K L (FieldOfNorms.laurentEquiv K L u hu A) =
      Valued.v A := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_laurentUniformizerEquiv (FieldOfNorms K L) _ _ _ π hu A

/-- The coordinate map is uniformly continuous for precisely the
already constructed stable-valuation uniformity on the field. -/
theorem FieldOfNorms.uniformContinuous_laurentEquiv :
    UniformContinuous (FieldOfNorms.laurentEquiv K L u hu) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv (FieldOfNorms K L) _ _ _ π hu

/-- The inverse also preserves the valuation uniformities. -/
theorem FieldOfNorms.uniformContinuous_laurentEquiv_symm :
    UniformContinuous (FieldOfNorms.laurentEquiv K L u hu).symm := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact uniformContinuous_laurentUniformizerEquiv_symm (FieldOfNorms K L) _ _ _ π hu

/-- Continuity for the existing field of norms field topology. -/
theorem FieldOfNorms.continuous_laurentEquiv :
    Continuous (FieldOfNorms.laurentEquiv K L u hu) := by
  exact (FieldOfNorms.uniformContinuous_laurentEquiv K L u hu).continuous

/-- Continuity of the Laurent expansion map. -/
theorem FieldOfNorms.continuous_laurentEquiv_symm :
    Continuous (FieldOfNorms.laurentEquiv K L u hu).symm := by
  exact (FieldOfNorms.uniformContinuous_laurentEquiv_symm K L u hu).continuous

/-- The constants and chosen uniformizer characterize
the continuous Laurent-coordinate field map uniquely. -/
theorem FieldOfNorms.laurentEquiv_unique :
    ∀ (f : LaurentSeries κL →+* FieldOfNorms K L), Continuous f →
      (∀ a, f (algebraMap κL (LaurentSeries κL) a) =
        residueConstantsFieldEmbedding K L a) →
      f (algebraMap (PowerSeries κL) (LaurentSeries κL) PowerSeries.X) = u →
      f = (FieldOfNorms.laurentEquiv K L u hu).toRingHom := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  intro f hf hC hX
  exact laurentUniformizerEquiv_unique (FieldOfNorms K L) _ _ _ π hu f hf hC hX

/-- Integral evaluation is continuous for the inherited integer
ring topology and the discrete-coefficient power-series topology. -/
theorem FieldOfNorms.continuous_powerSeriesEquiv :
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
    (residueConstantsIntegerHom K L)
    (FieldOfNorms.residueEquiv K L)
    (fun x => (FieldOfNorms.residueEquiv_apply K L x).symm)
    π (irreducible_of_valuation_exp_neg_one (FieldOfNorms K L) π hu)
    (hasEval_of_valuation_exp_neg_one (FieldOfNorms K L) π hu)

/-- The same exact first-nonzero-coefficient valuation formula holds in the
field of norms for the integral evaluation. -/
theorem FieldOfNorms.powerSeriesEquiv_valuation (A : PowerSeries κL) (hA : A ≠ 0) :
    FieldOfNorms.valuation K L (FieldOfNorms.powerSeriesEquiv K L u hu A :
      FieldOfNorms K L) = exp (-(A.order.toNat : ℤ)) := by
  let : UniformSpace κL := ⊥
  let : DiscreteUniformity κL := inferInstance
  let π : (FieldOfNorms.fieldValuation K L).valuationSubring :=
    ⟨u, hu.le.trans (by simp)⟩
  exact valuation_valuedPowerSeriesEquiv (FieldOfNorms K L) _ _ _ π hu A hA

end FontaineWintenberger
