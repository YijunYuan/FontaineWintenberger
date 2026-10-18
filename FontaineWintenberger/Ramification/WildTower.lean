/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Subgroup
public import FontaineWintenberger.Ramification.TameField
public import FontaineWintenberger.LocalField.TotalRamification
public import FontaineWintenberger.LocalField.SpectralMaps

/-!
# Actual total ramification throughout the wild tower

Every intermediate base above the wild fixed field has full inertia in its
own actual integer ring. The ordinary inertia-cardinality theorem therefore
gives its actual total-ramification degree.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [FiniteDimensional K L] [IsGalois K L]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "P" => lowerRamificationGroup (L ≃ₐ[K] L)
  (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 1

variable (M : IntermediateField K L)

local instance : CompleteSpace M := FiniteDimensional.complete K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
local instance : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := M)).valuationSubring) :=
  Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Every actual base above the wild fixed field has full own-ring inertia. -/
theorem wildField_lower_zero_eq_top (hM : IntermediateField.fixedField P ≤ M) :
    lowerRamificationGroup (L ≃ₐ[M] L)
      (IsLocalRing.maximalIdeal (spectralIntegerRing M L)) 0 = ⊤ := by
  apply finiteBase_lower_zero_eq_top K L M
  have hfix : M.fixingSubgroup ≤ P := by
    simpa only [IntermediateField.fixingSubgroup_fixedField] using
      IntermediateField.fixingSubgroup_le hM
  exact hfix.trans (lowerRamificationGroup_antitone (L ≃ₐ[K] L)
    (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) (by norm_num : (0 : ℤ) ≤ 1))

/-- The ramification index over every actual intermediate base above the
wild fixed field is its genuine relative field degree. -/
theorem wildField_top_ramificationIdx_eq_finrank (hM : IntermediateField.fixedField P ≤ M) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing M L)).ramificationIdx
      (NormedField.valuation (K := M)).valuationSubring = Module.finrank M L := by
  rw [← spectralIntegerRing_card_lower_zero M L, wildField_lower_zero_eq_top K L M hM,
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]

/-- Every actual intermediate step above the wild fixed field is totally
ramified on its own actual spectral integers and ordinary relative degree. -/
theorem wildField_step_ramificationIdx_eq_finrank (N : IntermediateField K L)
    (hMN : M ≤ N) (hM : IntermediateField.fixedField P ≤ M) :
    let B := IntermediateField.extendScalars hMN
    (IsLocalRing.maximalIdeal (spectralIntegerRing M B)).ramificationIdx
      (NormedField.valuation (K := M)).valuationSubring = Module.finrank M B := by
  let B := IntermediateField.extendScalars hMN
  let R := (NormedField.valuation (K := M)).valuationSubring
  let S := spectralIntegerRing M B
  let T := spectralIntegerRing M L
  have : IsDiscreteValuationRing S := inferInstance
  have : IsDiscreteValuationRing T := inferInstance
  let := spectralValuation_hasExtension_tower M (E := B) (L := L)
  let := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := M)) (spectralValuation M B) (spectralValuation M L)
  have : Module.Finite R S := inferInstance
  have : Module.Finite S T := Module.Finite.of_restrictScalars_finite R S T
  have ht : (IsLocalRing.maximalIdeal T).ramificationIdx R = Module.finrank R T := by
    rw [← IsFractionRing.finrank_eq R M T L]
    exact wildField_top_ramificationIdx_eq_finrank K L M hM
  have hs := ((ramificationIdx_eq_finrank_tower_iff R S T).mp ht).1
  rw [← IsFractionRing.finrank_eq R M S B] at hs
  exact hs

end FontaineWintenberger
