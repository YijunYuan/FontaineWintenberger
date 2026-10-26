/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.Quotient

/-!
# Finite upper ramification groups and quotient compatibility

Upper groups reindex the canonical real lower groups by the proved
inverse Herbrand function. Normal restriction preserves this numbering.

## Main definitions

* `upperRamificationGroup`: Upper numbering of the ideal-inertia lower groups.

## Main results

* `fixedField_map_upperRamificationGroup`: Herbrand's upper quotient theorem for the fixed-field
  restriction map.
* `fixedField_quotient_upperRamificationGroup`: Upper quotient compatibility through the canonical
  Galois quotient equivalence.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

section GroupAction

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

/-- Upper numbering of the ideal-inertia lower groups. -/
noncomputable def upperRamificationGroup (u : ℝ) : Subgroup G :=
  lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R)
    (inverseHerbrandFunction (R := R) G u)

instance upperRamificationGroup_normal (u : ℝ) :
    (upperRamificationGroup (R := R) G u).Normal :=
  maximalIdeal_lowerRamificationGroupReal_normal G _

theorem upperRamificationGroup_antitoneOn :
    AntitoneOn (upperRamificationGroup (R := R) G) (Set.Ici (-1)) := by
  intro u hu v hv huv
  exact lowerRamificationGroupReal_antitone G _
    ((strictMonoOn_inverseHerbrandFunction (R := R) G).monotoneOn hu hv huv)

@[simp]
theorem upperRamificationGroup_neg_one : upperRamificationGroup (R := R) G (-1) = ⊤ := by
  rw [upperRamificationGroup, inverseHerbrandFunction_of_nonpos G le_rfl (by norm_num)]
  exact lowerRamificationGroupReal_of_le_neg_one G _ le_rfl

@[simp]
theorem upperRamificationGroup_zero :
    upperRamificationGroup (R := R) G 0 = (IsLocalRing.maximalIdeal R).inertia G := by
  rw [upperRamificationGroup,
    inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl, lowerRamificationGroupReal_zero]

theorem upperRamificationGroup_herbrandFunction {t : ℝ} (ht : -1 ≤ t) :
    upperRamificationGroup (R := R) G (herbrandFunction (R := R) G t) =
      lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t := by
  rw [upperRamificationGroup, inverseHerbrandFunction_herbrandFunction G ht]

theorem upperRamificationGroup_eventually_eq_bot [FaithfulSMul G R] :
    ∃ U : ℝ, ∀ u : ℝ, U ≤ u → upperRamificationGroup (R := R) G u = ⊥ := by
  obtain ⟨T, hT⟩ := lowerRamificationGroupReal_eventually_eq_bot (R := R) G
  let a := max T 0
  have ha : -1 ≤ a := (by norm_num : (-1 : ℝ) ≤ 0).trans (le_max_right _ _)
  refine ⟨herbrandFunction (R := R) G a, fun u hu => ?_⟩
  have hu' := (herbrandFunction_mem_Ici (R := R) G ha).trans hu
  have hle := (strictMonoOn_inverseHerbrandFunction (R := R) G).monotoneOn
    (herbrandFunction_mem_Ici (R := R) G ha) hu' hu
  rw [inverseHerbrandFunction_herbrandFunction G ha] at hle
  exact hT _ ((le_max_left T 0).trans hle)

end GroupAction

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
variable [PerfectField 𝓀[K]]

local notation "G₀" => L ≃ₐ[K] L
local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- **Herbrand's upper quotient theorem** for the fixed-field restriction map. -/
theorem fixedField_map_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    (upperRamificationGroup (R := B₀) G₀ u).map ρ =
      upperRamificationGroup (R := A₀) D₀ u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  rw [upperRamificationGroup, upperRamificationGroup,
    fixedField_map_lowerRamificationGroupReal K L H _
      (inverseHerbrandFunction_mem_Ici G₀ u),
    fixedField_inverseHerbrandFunction_transitivity K L H u hu,
    herbrandFunction_inverseHerbrandFunction H (inverseHerbrandFunction_mem_Ici D₀ u)]

/-- Upper quotient compatibility through the canonical Galois quotient equivalence. -/
theorem fixedField_quotient_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ((upperRamificationGroup (R := B₀) G₀ u).map (QuotientGroup.mk' H)).map
      (fixedFieldDecompositionQuotientEquiv K L H).toMonoidHom =
        upperRamificationGroup (R := A₀) D₀ u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  rw [upperRamificationGroup, upperRamificationGroup,
    fixedField_quotient_lowerRamificationGroupReal K L H _
      (inverseHerbrandFunction_mem_Ici G₀ u),
    fixedField_inverseHerbrandFunction_transitivity K L H u hu,
    herbrandFunction_inverseHerbrandFunction H (inverseHerbrandFunction_mem_Ici D₀ u)]

end FontaineWintenberger
