/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.Tower

/-!
# Residue fields of finite normed extensions

The compatible norm valuation gives the local map of unit balls.
Their finite module extension descends to the residue fields.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M : Type*) [NormedField M] [IsUltrametricDist M] [NormedAlgebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]

/-- The residue extension of a finite compatible normed extension is finite. -/
theorem normedAlgebra_residueField_finiteDimensional :
    FiniteDimensional
      (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
      (IsLocalRing.ResidueField (NormedField.valuation (K := M)).valuationSubring) := by
  have := extensionValuationSubring_moduleFinite K M (NormedField.valuation (K := M))
  infer_instance

/-- Perfectness propagates to the residue field; its cardinality is unrestricted. -/
theorem normedAlgebra_residueField_perfectField [PerfectField
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)] :
    PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring) := by
  have := normedAlgebra_residueField_finiteDimensional K M
  exact Algebra.IsAlgebraic.perfectField
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)

omit [IsCompleteDiscreteValuedField K] in
/-- A finite separable normed extension of a local field is again a local field, with the same
residue characteristic. -/
theorem normedAlgebra_isPerfectResidueLocalField [IsPerfectResidueLocalField K] (L : Type*)
    [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : IsPerfectResidueLocalField L :=
  have := normedAlgebra_isCompleteDiscreteValuedField K L
  have := normedAlgebra_residueField_perfectField K L
  have := normedAlgebra_residueField_finiteDimensional K L
  { residueChar_prime := by
      rw [← Algebra.ringChar_eq
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
      exact IsPerfectResidueLocalField.residueChar_prime }

omit [IsCompleteDiscreteValuedField K] in
theorem normedAlgebra_residueChar_eq [IsPerfectResidueLocalField K] (L : Type*)
    [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    haveI := normedAlgebra_isPerfectResidueLocalField K L
    residueChar L = residueChar K :=
  have := normedAlgebra_residueField_finiteDimensional K L
  (Algebra.ringChar_eq
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) _).symm

end FontaineWintenberger
