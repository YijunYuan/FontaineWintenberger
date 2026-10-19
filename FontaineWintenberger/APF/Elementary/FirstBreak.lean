/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.Ramification.Herbrand.Subgroup
public import FontaineWintenberger.Ramification.Fields.Nonnormal

/-!
# The finite attained first bound of a totally ramified subextension

A proper fixing subgroup with full inertia product has a finite
nonnegative first break. The intrinsic extended supremum equals that break.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "G" => L ≃ₐ[K] L
local notation "H" => M.fixingSubgroup
local notation "U" => upperRamificationGroup (R := spectralIntegerRing K L) G
local notation "D" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 0

/-- A proper fixing subgroup with full inertia product supplies a
finite attained intrinsic first bound, without normality of the subfield. -/
theorem exists_apfRamificationBound_eq_coe_of_fixingSubgroup
    (hH : H ≠ ⊤) (hzero : H ⊔ D = ⊤) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K M = (b : EReal) ∧
      ∀ u : ℝ, -1 ≤ u → (H ⊔ U u = ⊤ ↔ u ≤ b) := by
  obtain ⟨b, hb, hprofile⟩ := exists_first_upper_break_of_fixingSubgroup
    (R := spectralIntegerRing K L) G H hH hzero
  have hiff (u : ℝ) (hu : -1 ≤ u) : H ⊔ U u = ⊤ ↔ u ≤ b := by
    by_cases hu0 : 0 ≤ u
    · exact hprofile u hu0
    · have hu0' : u ≤ 0 := le_of_not_ge hu0
      have hle : D ≤ U u := by
        simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
          upperRamificationGroup_antitoneOn (R := spectralIntegerRing K L) G hu
            (by norm_num : -1 ≤ (0 : ℝ)) hu0'
      have ht : H ⊔ U u = ⊤ := top_unique (by
        simpa only [hzero] using sup_le_sup_left hle H)
      exact iff_of_true ht (hu0'.trans hb)
  refine ⟨b, hb, ?_, hiff⟩
  rw [apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper K L M]
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨u, hu, ht, rfl⟩
    exact EReal.coe_le_coe_iff.mpr ((hiff u hu).mp ht)
  · exact le_sSup ⟨b, by linarith, (hiff b (by linarith)).mpr le_rfl, rfl⟩

local notation "B" => Valuation.valuationSubring
  (Valuation.comap (algebraMap M L) (spectralValuation K L))

/-- Every nontrivial totally ramified intermediate field has a finite
nonnegative intrinsic first bound, attained in the upper filtration. -/
theorem exists_apfRamificationBound_eq_coe_of_totallyRamified
    (hdegree : 1 < Module.finrank K M)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K M) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K M = (b : EReal) ∧
      ∀ u : ℝ, -1 ≤ u → (H ⊔ U u = ⊤ ↔ u ≤ b) := by
  have hH : H ≠ ⊤ := by
    intro h
    have hi := congrArg Subgroup.index h
    rw [Subgroup.index_top, ← IntermediateField.finrank_eq_fixingSubgroup_index L M] at hi
    omega
  have hz : H ⊔ D = ⊤ := by
    apply (fixedField_ramificationIdx_eq_finrank_iff K L H).mp
    have hEq : IntermediateField.fixedField H = M := IsGalois.fixedField_fixingSubgroup M
    exact Eq.mp (congrArg (fun N : IntermediateField K L =>
      (IsLocalRing.maximalIdeal (Valuation.valuationSubring
        (Valuation.comap (algebraMap N L) (spectralValuation K L)))).ramificationIdx 𝒪[K] =
          Module.finrank K N) hEq.symm) he
  exact exists_apfRamificationBound_eq_coe_of_fixingSubgroup K L M hH hz

end FontaineWintenberger
