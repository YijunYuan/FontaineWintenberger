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
theorem normUnionStageEquiv_exponent (N P : FiniteLayer L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z)) :
    separableNormUnionStageExponent K L M P =
      separableNormUnionStageExponent K L M N := by
  apply separableNormUnionStageExponent_unique K L M N
  intro x
  change normLimitValuation K N.val
      (separableNormUnionBaseToStage K L M N x) = _
  calc
    _ = normLimitValuation K P.val
        (normLimitMap e
          (separableNormUnionBaseToStage K L M N x)) :=
      (normLimitValuation_normLimitMap K
        e _).symm
    _ = normLimitValuation K P.val
        (separableNormUnionBaseToStage K L M P (normLimitMap a x)) :=
      congrArg (normLimitValuation K P.val)
        (normUnionStageEquiv_base K L M N P a e h x)
    _ = normLimitValuation K L (normLimitMap a x) ^
        separableNormUnionStageExponent K L M P :=
      separableNormUnionStageExponent_spec K L M P (normLimitMap a x)
    _ = normLimitValuation K L x ^ separableNormUnionStageExponent K L M P := by
      rw [normLimitValuation_normLimitMap K a x]

/-- An original finite-stage isomorphism preserves the same rational valuation. -/
theorem normUnionStageEquiv_valuation (N P : FiniteLayer L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : NormLimit K N.val) :
    separableNormUnionStageValuation K L M P (normLimitMap e x) =
      separableNormUnionStageValuation K L M N x := by
  rw [separableNormUnionStageValuation_apply, separableNormUnionStageValuation_apply,
    normUnionStageEquiv_exponent K L M N P a e h,
    normLimitValuation_normLimitMap K
      e x]

end FontaineWintenberger
