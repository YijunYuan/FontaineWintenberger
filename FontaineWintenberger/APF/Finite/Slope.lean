/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.Ramification.Fields.Nonnormal
public import FontaineWintenberger.Ramification.Lower.BaseChange
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Eventual slopes of finite APF extensions

## Finite APF indices stabilize and their integral is eventually affine

## The eventual ramification slope of a finite extension

The eventual intrinsic inertia index is the ramification index of the
field. This is valid for finite separable extensions without normality or total
ramification, and also for their compatible normed integer rings.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- Inertia has positive finite index relative to the finite-base fixing subgroup. -/
theorem fixingSubgroup_inertiaRelIndex_pos :
    0 < M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0) := by
  have hindex : M.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) M]
    exact Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K M)
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := Subgroup.relIndex_eq_zero_of_le_right
    (show absoluteUpperRamificationGroup K 0 ≤ ⊤ from le_top) hzero
  exact hindex (by simpa only [Subgroup.relIndex_top_right] using h)

/-- The finite-base inertia fixing index bounds every nonnegative APF index. -/
theorem apfIndex_le_fixingSubgroup_inertiaRelIndex (u : ℝ) :
    apfIndex K M u ≤ M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0) := by
  rw [apfIndex_eq_embedding K M M.val, IntermediateField.fieldRange_val, apfInertiaIndex]
  have hnonzero :
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0).relIndex
        (absoluteUpperRamificationGroup K 0) ≠ 0 := by
    simpa only [Subgroup.inf_relIndex_right] using
      Nat.ne_of_gt (fixingSubgroup_inertiaRelIndex_pos K M)
  change ((M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
    absoluteUpperRamificationGroup K u).relIndex (absoluteUpperRamificationGroup K 0) ≤ _
  have hle : M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0 ≤
      (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
        absoluteUpperRamificationGroup K u := le_sup_left
  have h := Subgroup.relIndex_le_of_le_left hle hnonzero
  simpa only [Subgroup.inf_relIndex_right] using h

/-- Monotonicity and a finite upper bound force the finite-base index to stabilize. -/
theorem exists_apfIndex_finite_constant :
    ∃ C : ℕ, 0 < C ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, b ≤ u → apfIndex K M u = C := by
  let f : ℝ → ℕ := fun u => apfIndex K M (max u 0)
  have hbound : BddAbove (Set.range f) := by
    refine ⟨M.fixingSubgroup.relIndex (absoluteUpperRamificationGroup K 0), ?_⟩
    rintro x ⟨u, rfl⟩
    exact apfIndex_le_fixingSubgroup_inertiaRelIndex K M (max u 0)
  obtain ⟨C, ⟨⟨a, ha⟩, hmax⟩⟩ :=
    hbound.exists_isGreatest_of_nonempty (show (Set.range f).Nonempty from ⟨f 0, 0, rfl⟩)
  have := isAPF_of_finite K M
  refine ⟨C, ?_, max a 0, le_max_right a 0, ?_⟩
  · rw [← ha]
    exact IsAPF.apfIndex_pos K M (le_max_right a 0)
  · intro u hu
    have hu0 : 0 ≤ u := (le_max_right a 0).trans hu
    apply le_antisymm
    · simpa only [f, max_eq_left hu0] using hmax (show f u ∈ Set.range f from ⟨u, rfl⟩)
    · rw [← ha]
      exact IsAPF.apfIndex_monotoneOn K M (le_max_right a 0) hu0 hu

/-- The finite-base Herbrand integral is affine on an eventual constant-index tail. -/
theorem exists_apfPsi_finite_affine :
    ∃ C : ℕ, 0 < C ∧ ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, b ≤ u → apfIndex K M u = C) ∧
      ∀ u : ℝ, b ≤ u → apfPsi K M u = apfPsi K M b + (C : ℝ) * (u - b) := by
  obtain ⟨C, hC, b, hb, hidx⟩ := exists_apfIndex_finite_constant K M
  refine ⟨C, hC, b, hb, hidx, ?_⟩
  intro u hu
  have hi : (∫ v in b..u, apfHerbrandSlope K M v) = (u - b) * (C : ℝ) := by
    calc
      _ = ∫ _v in b..u, (C : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hu]
        intro v hv
        simp only [apfHerbrandSlope, max_eq_left (hb.trans hv.1), hidx v hv.1]
      _ = _ := by simp
  have := isAPF_of_finite K M
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M 0 b)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M b u)
  change apfPsi K M b + (∫ v in b..u, apfHerbrandSlope K M v) = apfPsi K M u at hadd
  rw [hi] at hadd
  exact hadd.symm.trans (by ring)

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

section IntermediateField

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L
local notation "I" => lowerRamificationGroup (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) 0

/-- The own spectral ramification index of a nonnormal intermediate field
is the inertia-relative fixing-subgroup index. -/
theorem intermediate_spectral_ramificationIdx_eq_relIndex :
    (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx OK =
      M.fixingSubgroup.relIndex I := by
  let w := (spectralValuation K L).comap (algebraMap M L)
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have h := fixedField_ramificationIdx_eq_relIndex K L M.fixingSubgroup
  have hfield : IntermediateField.fixedField M.fixingSubgroup = M :=
    IsGalois.fixedField_fixingSubgroup M
  have h' : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx OK =
      M.fixingSubgroup.relIndex I := by
    exact Eq.mp (congrArg (fun N : IntermediateField K L =>
      (IsLocalRing.maximalIdeal ((spectralValuation K L).comap
        (algebraMap N L)).valuationSubring).ramificationIdx OK =
          M.fixingSubgroup.relIndex I) hfield) h
  rw [extensionValuationSubring_ramificationIdx_eq_spectral K M w] at h'
  exact h'

/-- The intrinsic APF index of an intermediate field eventually
equals its own-ring ramification index. -/
theorem exists_intermediate_apfIndex_eq_ramificationIdx :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      apfIndex K M u =
        (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx OK := by
  obtain ⟨U, hU⟩ := upperRamificationGroup_eventually_eq_bot (R := B) (L ≃ₐ[K] L)
  refine ⟨max U 0, le_max_right _ _, fun u hu => ?_⟩
  rw [apfIndex_eq_subgroupRelIndex_of_finiteGalois K L M ((le_max_right _ _).trans hu),
    hU u ((le_max_left _ _).trans hu), sup_bot_eq, Subgroup.inf_relIndex_right,
    upperRamificationGroup_zero, ← lowerRamificationGroup_zero,
    intermediate_spectral_ramificationIdx_eq_relIndex K L M]

end IntermediateField

section AbstractField

variable (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "O" => spectralIntegerRing K M

/-- Every finite separable extension has intrinsic inertia index equal to
its spectral ramification index throughout an eventual tail. -/
theorem exists_apfIndex_eq_spectral_ramificationIdx :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      apfIndex K M u = (IsLocalRing.maximalIdeal O).ramificationIdx OK := by
  let j : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let L := IntermediateField.normalClosure K M (SeparableClosure K)
  let i : M →ₐ[K] L :=
    j.codRestrict L.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let S := i.fieldRange
  let e : M ≃ₐ[K] S := i.equivFieldRange
  let : FiniteDimensional K S := Module.Finite.equiv e.toLinearEquiv
  obtain ⟨U, hU, hidx⟩ := exists_intermediate_apfIndex_eq_ramificationIdx K L S
  refine ⟨U, hU, fun u hu => ?_⟩
  rw [apfIndex_algEquiv K M e, hidx u hu, spectral_ramificationIdx_algEquiv K e]

open MeasureTheory

/-- Integrating the eventual index gives the finite-extension
Herbrand tail with its spectral ramification index as slope. -/
theorem exists_apfPsi_spectral_ramificationIdx_affine :
    ∃ U : ℝ, 0 ≤ U ∧
      (∀ u : ℝ, U ≤ u →
        apfIndex K M u = (IsLocalRing.maximalIdeal O).ramificationIdx OK) ∧
      ∀ u : ℝ, U ≤ u → apfPsi K M u = apfPsi K M U +
        ((IsLocalRing.maximalIdeal O).ramificationIdx OK : ℝ) * (u - U) := by
  obtain ⟨U, hU, hidx⟩ := exists_apfIndex_eq_spectral_ramificationIdx K M
  refine ⟨U, hU, hidx, fun u hu => ?_⟩
  have hi : (∫ v in U..u, apfHerbrandSlope K M v) =
      (u - U) * ((IsLocalRing.maximalIdeal O).ramificationIdx OK : ℝ) := by
    calc
      _ = ∫ _v in U..u, ((IsLocalRing.maximalIdeal O).ramificationIdx OK : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hu]
        intro v hv
        simp only [apfHerbrandSlope, max_eq_left (hU.trans hv.1), hidx v hv.1]
      _ = _ := by simp
  have := isAPF_of_finite K M
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M 0 U)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M U u)
  change apfPsi K M U + (∫ v in U..u, apfHerbrandSlope K M v) = apfPsi K M u at hadd
  rw [hi] at hadd
  exact hadd.symm.trans (by ring)

/-- Every nonnegative shift in the finite-extension tail changes the
intrinsic Herbrand parameter by the spectral ramification index times that shift. -/
theorem exists_apfPsi_spectral_ramificationIdx_shift :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ h : ℝ, 0 ≤ h →
      apfPsi K M (u + h) = apfPsi K M u +
        ((IsLocalRing.maximalIdeal O).ramificationIdx OK : ℝ) * h := by
  obtain ⟨U, hU, _, hpsi⟩ := exists_apfPsi_spectral_ramificationIdx_affine K M
  refine ⟨U, hU, fun u hu h hh => ?_⟩
  rw [hpsi (u + h) (by linarith), hpsi u hu]
  ring

end AbstractField

section Norm

variable (M : Type*) [NormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OM" => Valuation.valuationSubring (NormedField.valuation (K := M))

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- The normed unit ball and the spectral integer ring
have the same ramification index under the scalar map. -/
theorem normed_ramificationIdx_eq_spectral :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    (IsLocalRing.maximalIdeal OM).ramificationIdx OK =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx OK := by
  exact extensionValuationSubring_ramificationIdx_eq_spectral K M
    (NormedField.valuation (K := M))

/-- The eventual intrinsic APF index equals the ramification index on the
compatible normed field's unit ball. -/
theorem exists_apfIndex_eq_normed_ramificationIdx :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      apfIndex K M u = (IsLocalRing.maximalIdeal OM).ramificationIdx OK := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfIndex_eq_spectral_ramificationIdx K M

/-- The normed integer-ring ramification index is the
affine slope of the intrinsic finite-extension Herbrand tail. -/
theorem exists_apfPsi_normed_ramificationIdx_affine :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧
      (∀ u : ℝ, U ≤ u → apfIndex K M u = (IsLocalRing.maximalIdeal OM).ramificationIdx OK) ∧
      ∀ u : ℝ, U ≤ u → apfPsi K M u = apfPsi K M U +
        ((IsLocalRing.maximalIdeal OM).ramificationIdx OK : ℝ) * (u - U) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfPsi_spectral_ramificationIdx_affine K M

/-- Nonnegative parameter shifts in the normed finite-base
tail have the unit-ball ramification index as their exact multiplier. -/
theorem exists_apfPsi_normed_ramificationIdx_shift :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ h : ℝ, 0 ≤ h →
      apfPsi K M (u + h) = apfPsi K M u +
        ((IsLocalRing.maximalIdeal OM).ramificationIdx OK : ℝ) * h := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfPsi_spectral_ramificationIdx_shift K M

end Norm

end FontaineWintenberger
