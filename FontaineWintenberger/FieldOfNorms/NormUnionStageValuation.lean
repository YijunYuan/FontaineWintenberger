/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteStages

/-!
# Valuations under original finite-stage isomorphisms

A commuting original base square identifies the positive normalization
exponents, so the same stage isomorphism preserves rational valuations.

Reference: Wintenberger, Remark 3.2.4, the finite-stage valuation argument.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The actual original commuting square identifies the normalization exponents. -/
theorem RelFieldOfNorms.stageEquiv_exponent (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z)) :
    RelFieldOfNorms.stageExponent K L M P =
      RelFieldOfNorms.stageExponent K L M N := by
  apply RelFieldOfNorms.stageExponent_unique K L M N
  intro x
  change FieldOfNorms.valuation K N.val
      (RelFieldOfNorms.baseToStage K L M N x) = _
  calc
    _ = FieldOfNorms.valuation K P.val
        (FieldOfNorms.map e
          (RelFieldOfNorms.baseToStage K L M N x)) :=
      (FieldOfNorms.valuation_fieldOfNormsMap K
        e _).symm
    _ = FieldOfNorms.valuation K P.val
        (RelFieldOfNorms.baseToStage K L M P (FieldOfNorms.map a x)) :=
      congrArg (FieldOfNorms.valuation K P.val)
        (RelFieldOfNorms.stageEquiv_base K L M N P a e h x)
    _ = FieldOfNorms.valuation K L (FieldOfNorms.map a x) ^
        RelFieldOfNorms.stageExponent K L M P :=
      RelFieldOfNorms.stageExponent_spec K L M P (FieldOfNorms.map a x)
    _ = FieldOfNorms.valuation K L x ^ RelFieldOfNorms.stageExponent K L M P := by
      rw [FieldOfNorms.valuation_fieldOfNormsMap K a x]

/-- An original finite-stage isomorphism preserves the same rational valuation. -/
theorem RelFieldOfNorms.stageEquiv_valuation (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageValuation K L M P (FieldOfNorms.map e x) =
      RelFieldOfNorms.stageValuation K L M N x := by
  rw [RelFieldOfNorms.stageValuation_apply, RelFieldOfNorms.stageValuation_apply,
    RelFieldOfNorms.stageEquiv_exponent K L M N P a e h,
    FieldOfNorms.valuation_fieldOfNormsMap K
      e x]

end FontaineWintenberger
