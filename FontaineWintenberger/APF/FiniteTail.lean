module

public import FontaineWintenberger.APF.PrimeDegree
public import FontaineWintenberger.APF.FiniteSlope
public import FontaineWintenberger.Ramification.Nonnormal
public import FontaineWintenberger.LocalField.BaseChange

/-!
# The actual eventual ramification slope of a finite extension

The eventual intrinsic inertia index is the ramification index of the original
field. This is valid for finite separable extensions without normality or total
ramification, and also for their original compatible normed integer rings.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

section IntermediateField

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L
local notation "I" => lowerRamificationGroup (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) 0

/-- The own spectral ramification index of a nonnormal intermediate field
is the actual inertia-relative fixing-subgroup index. -/
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

/-- The intrinsic APF index of an actual intermediate field eventually
equals its actual own-ring ramification index. -/
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
its original spectral ramification index throughout a genuine eventual tail. -/
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

/-- Integrating the actual eventual index gives the actual finite-extension
Herbrand tail with its original spectral ramification index as slope. -/
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
  have hM := isAPF_of_finite K M
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M hM 0 U)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K M hM U u)
  change apfPsi K M U + (∫ v in U..u, apfHerbrandSlope K M v) = apfPsi K M u at hadd
  rw [hi] at hadd
  exact hadd.symm.trans (by ring)

/-- Every nonnegative shift in the actual finite-extension tail changes the
intrinsic Herbrand parameter by the actual spectral ramification index times that shift. -/
theorem exists_apfPsi_spectral_ramificationIdx_shift :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ h : ℝ, 0 ≤ h →
      apfPsi K M (u + h) = apfPsi K M u +
        ((IsLocalRing.maximalIdeal O).ramificationIdx OK : ℝ) * h := by
  obtain ⟨U, hU, _, hpsi⟩ := exists_apfPsi_spectral_ramificationIdx_affine K M
  refine ⟨U, hU, fun u hu h hh => ?_⟩
  rw [hpsi (u + h) (by linarith), hpsi u hu]
  ring

end AbstractField

section OriginalNorm

variable (M : Type*) [NormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OM" => Valuation.valuationSubring (NormedField.valuation (K := M))

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- The original normed unit ball and the actual spectral integer ring
have the same ramification index under the original scalar map. -/
theorem normed_ramificationIdx_eq_spectral :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    (IsLocalRing.maximalIdeal OM).ramificationIdx OK =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx OK := by
  exact extensionValuationSubring_ramificationIdx_eq_spectral K M
    (NormedField.valuation (K := M))

/-- The eventual intrinsic APF index equals the ramification index on the
original compatible normed field's original unit ball. -/
theorem exists_apfIndex_eq_normed_ramificationIdx :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      apfIndex K M u = (IsLocalRing.maximalIdeal OM).ramificationIdx OK := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfIndex_eq_spectral_ramificationIdx K M

/-- The actual original normed integer-ring ramification index is the
actual affine slope of the intrinsic finite-extension Herbrand tail. -/
theorem exists_apfPsi_normed_ramificationIdx_affine :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧
      (∀ u : ℝ, U ≤ u → apfIndex K M u = (IsLocalRing.maximalIdeal OM).ramificationIdx OK) ∧
      ∀ u : ℝ, U ≤ u → apfPsi K M u = apfPsi K M U +
        ((IsLocalRing.maximalIdeal OM).ramificationIdx OK : ℝ) * (u - U) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfPsi_spectral_ramificationIdx_affine K M

/-- Actual nonnegative parameter shifts in the original normed finite-base
tail have the original unit-ball ramification index as their exact multiplier. -/
theorem exists_apfPsi_normed_ramificationIdx_shift :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ h : ℝ, 0 ≤ h →
      apfPsi K M (u + h) = apfPsi K M u +
        ((IsLocalRing.maximalIdeal OM).ramificationIdx OK : ℝ) * h := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  rw [normed_ramificationIdx_eq_spectral K M]
  exact exists_apfPsi_spectral_ramificationIdx_shift K M

end OriginalNorm

end FontaineWintenberger
