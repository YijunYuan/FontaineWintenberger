/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Valuation
public import FontaineWintenberger.APF.MaximalTame

/-!
# The source normalization above the actual maximal unramified field

The existing stable valuation is computed at every original finite field above
the actual maximal unramified subfield, as in Wintenberger, paragraph 2.1.2.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The same stable valuation is computed at every actual finite layer above
the actual maximal unramified subfield, not merely above a chosen stable witness. -/
theorem normLimitValuation_eq_coordinate_of_maximalUnramified_le [IsAPF K L]
    (E : FiniteLayer K L) (hE : apfMaximalUnramified K L ≤ E) (x : NormLimit K L) :
    normLimitValuation K L x = normLimitCoordinateValuation K L E x := by
  obtain ⟨D, hD⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L
  let F := FiniteLayer.sup D E
  have hEF : E ≤ F := FiniteLayer.le_sup_right D E
  have hs := spectralResidueInclusion_surjective_of_apfMaximalUnramified_le
    K L E F hE hEF
  have hv := FiniteLayer.normalizedValuation_norm_of_residueInclusion_surjective
    K L E F hEF hs (normLimitEval K L F x)
  rw [normLimitEval_norm] at hv
  exact (hD F (FiniteLayer.le_sup_left D E) x).trans hv.symm

end FontaineWintenberger
