/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteOverfieldBaseChange
public import FontaineWintenberger.Ramification.Subgroup

/-!
# Actual upper ramification groups after finite base change

The two spectral constructions give the same actual integer subring. The
fixing-subgroup equivalence acts by the original field automorphisms, so the
subgroup change of parameter transports to the actual group over the new base.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

noncomputable local instance : NontriviallyNormedField E :=
  spectralNorm.nontriviallyNormedField K E

noncomputable local instance : NormedAlgebra K E := spectralNorm.normedAlgebra K E

local instance : IsUltrametricDist E :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))

variable (M : IntermediateField K E)

local instance : CompleteSpace M := IntermediateField.completeSpace_of_finiteDimensional M


local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

/-- Finite base change for the actual own-ring upper groups, with no normality of the base. -/
theorem finiteBase_upperRamificationGroup {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) =
      ((upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).subgroupOf
        M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom :=
  finiteBase_upperRamificationGroup_of_finiteGalois K E M hu

end FontaineWintenberger
