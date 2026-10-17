/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteStages

/-!
# Relative and ambient transport on the same original finite stages

For an automorphism fixing the original base, the ambient image field and
its original norm-family transport are those of the relative union map.

Reference: Wintenberger, Remark 3.2.4, restriction to the relative Galois group.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]

/-- Relative and ambient transport give the identical original finite image. -/
theorem normUnionAbsoluteLayer_restrictScalars (τ : M ≃ₐ[L] M)
    (N : FiniteLayer L M) :
    normUnionAbsoluteLayer K M L (τ.restrictScalars K) N =
      FiniteLayer.map τ.toAlgHom N := by
  apply Subtype.ext
  apply SetLike.ext
  intro z
  rfl

end Fields

section NormFields

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- Forgetting the base scalars transports each original family to the same union element. -/
theorem normUnionAbsolute_relative_stage (τ : M ≃ₐ[L] M)
    (N : FiniteLayer L M) (x : NormLimit K N.val) :
    separableNormUnionOf K L M p hL hInfinite
        (normUnionAbsoluteLayer K M L (τ.restrictScalars K) N)
        (normLimitMap (normUnionAbsoluteLayerEquiv K M L (τ.restrictScalars K) N) x) =
      separableNormUnionOf K L M p hL hInfinite (FiniteLayer.map τ.toAlgHom N)
        (normLimitMap ((FiniteLayer.equivMap τ.toAlgHom N).restrictScalars K) x) := by
  exact separableNormUnionOf_transport_congr K L p hL hInfinite M
    (normUnionAbsoluteLayer K M L (τ.restrictScalars K) N) (FiniteLayer.map τ.toAlgHom N)
    (normUnionAbsoluteLayerEquiv K M L (τ.restrictScalars K) N)
    ((FiniteLayer.equivMap τ.toAlgHom N).restrictScalars K)
    (normUnionAbsoluteLayer_restrictScalars K M L τ N) (fun _ => rfl) x

end NormFields

end FontaineWintenberger
