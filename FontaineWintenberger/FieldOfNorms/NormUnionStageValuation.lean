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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

include p hInfinite in
/-- The actual original commuting square identifies the normalization exponents. -/
theorem normUnionStageEquiv_exponent (N P : FiniteLayer L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z)) :
    separableNormUnionStageExponent K L M hL P =
      separableNormUnionStageExponent K L M hL N := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
  apply separableNormUnionStageExponent_unique K L M p hL hInfinite N
  intro x
  change normLimitValuation K N.val (separableNormUnionStage_isAPF K L M hL N)
      (separableNormUnionBaseToStage K L M p hL hInfinite N x) = _
  calc
    _ = normLimitValuation K P.val (separableNormUnionStage_isAPF K L M hL P)
        (normLimitMap e
          (separableNormUnionBaseToStage K L M p hL hInfinite N x)) :=
      (normLimitValuation_normLimitMap K
        (separableNormUnionStage_isAPF K L M hL N)
        (separableNormUnionStage_isAPF K L M hL P) e _).symm
    _ = normLimitValuation K P.val (separableNormUnionStage_isAPF K L M hL P)
        (separableNormUnionBaseToStage K L M p hL hInfinite P (normLimitMap a x)) :=
      congrArg (normLimitValuation K P.val (separableNormUnionStage_isAPF K L M hL P))
        (normUnionStageEquiv_base K L M p hL hInfinite N P a e h x)
    _ = normLimitValuation K L hL (normLimitMap a x) ^
        separableNormUnionStageExponent K L M hL P :=
      separableNormUnionStageExponent_spec K L M hL P (normLimitMap a x)
    _ = normLimitValuation K L hL x ^ separableNormUnionStageExponent K L M hL P := by
      rw [normLimitValuation_normLimitMap K hL hL a x]

/-- An original finite-stage isomorphism preserves the same rational valuation. -/
theorem normUnionStageEquiv_valuation (N P : FiniteLayer L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : NormLimit K N.val) :
    separableNormUnionStageValuation K L M p hL hInfinite P (normLimitMap e x) =
      separableNormUnionStageValuation K L M p hL hInfinite N x := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
  rw [separableNormUnionStageValuation_apply, separableNormUnionStageValuation_apply,
    normUnionStageEquiv_exponent K L M p hL hInfinite N P a e h,
    normLimitValuation_normLimitMap K
      (separableNormUnionStage_isAPF K L M hL N)
      (separableNormUnionStage_isAPF K L M hL P) e x]

end FontaineWintenberger
