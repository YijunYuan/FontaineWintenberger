/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteGaloisOverfield
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
variable (E : Type*) [NontriviallyNormedField E] [NormedAlgebra K E]
    [IsUltrametricDist E] [FiniteDimensional K E] [IsGalois K E]

variable (M : IntermediateField K E)

local instance finiteOverfieldBase_completeSpace : CompleteSpace M :=
    IntermediateField.completeSpace_of_finiteDimensional M


local instance finiteOverfieldBase_discreteValuationRing : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

/-- Finite base change for the actual own-ring upper groups, with no normality of the base. -/
theorem finiteBase_upperRamificationGroup_of_finiteGalois {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) =
      ((upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).subgroupOf
        M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom := by
  have hpsi : -1 ≤ apfPsi K M u := by
    rw [apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K E M hu]
    exact herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ u)
  rw [← finiteBase_upper_map_fixingSubgroupEquiv K E M hpsi]
  congr 1
  unfold upperRamificationGroup
  rw [apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K E M hu,
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ u),
    lowerRamificationGroupReal_subgroupOf]

end FontaineWintenberger
