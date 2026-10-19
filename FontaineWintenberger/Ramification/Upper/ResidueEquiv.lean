/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.Transport

/-!
# Invariance of the finite residue degree

Mathlib's local residue algebra equivalence applies to the canonical
integer-ring equivalences, preserving the base residue field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]


omit [FiniteDimensional K L] in
/-- A field isomorphism preserves the canonical residue degree. -/
theorem spectral_residueDegree_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K M)) =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K L)) :=
  (IsLocalRing.ResidueField.mapAlgEquiv' (spectralIntegerRingEquiv K
      e)).toLinearEquiv.finrank_eq.symm

/-- Any compatible extension valuation has the same residue degree
as the spectral valuation on the finite separable field. -/
theorem extensionValuationSubring_residueDegree_eq_spectral
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w] :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    Module.finrank (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField w.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K L)) := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact (IsLocalRing.ResidueField.mapAlgEquiv'
    (IsIntegralClosure.equiv 𝒪[K] (spectralIntegerRing K L) L
        w.valuationSubring)).toLinearEquiv.finrank_eq.symm

end FontaineWintenberger
