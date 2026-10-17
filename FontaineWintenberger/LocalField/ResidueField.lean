/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.NormedTower

/-!
# Residue fields of actual finite normed extensions

The compatible norm valuation gives the local map of actual unit balls.
Their finite module extension descends to the residue fields.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (M : Type*) [NormedField M] [IsUltrametricDist M] [NormedAlgebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]

/-- The actual residue extension of a finite compatible normed extension is finite. -/
theorem normedAlgebra_residueField_finiteDimensional :
    FiniteDimensional
      (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
      (IsLocalRing.ResidueField (NormedField.valuation (K := M)).valuationSubring) := by
  have := extensionValuationSubring_moduleFinite K M (NormedField.valuation (K := M))
  infer_instance

/-- Perfectness propagates to the actual residue field; its cardinality is unrestricted. -/
theorem normedAlgebra_residueField_perfectField [PerfectField
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)] :
    PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring) := by
  have := normedAlgebra_residueField_finiteDimensional K M
  exact Algebra.IsAlgebraic.perfectField
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)

end FontaineWintenberger
