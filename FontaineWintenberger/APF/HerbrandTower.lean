/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteBaseIndex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Monotone

/-!
# Actual Herbrand integrals compose across finite base change
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter

section Calculus

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- At continuity points of the actual slope, its actual primitive has that derivative. -/
theorem IsAPF.hasDerivAt_apfPsi [IsAPF K L] {u : ℝ}
    (hc : ContinuousAt (apfHerbrandSlope K L) u) :
    HasDerivAt (apfPsi K L) (apfHerbrandSlope K L u) u := by
  apply intervalIntegral.integral_hasDerivAt_right
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 u) _ hc
  exact (IsAPF.monotone_apfHerbrandSlope
    K L).measurable.stronglyMeasurable.stronglyMeasurableAtFilter

/-- The actual APF primitive has its source derivative outside a countable set. -/
theorem IsAPF.exists_apfPsi_derivative_countable [IsAPF K L] :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u : ℝ, u ∉ S →
      HasDerivAt (apfPsi K L) (apfHerbrandSlope K L u) u := by
  refine ⟨{u | ¬ ContinuousAt (apfHerbrandSlope K L) u},
    (IsAPF.monotone_apfHerbrandSlope K L).countable_not_continuousAt, ?_⟩
  intro u hu
  exact IsAPF.hasDerivAt_apfPsi K L (not_not.mp hu)

end Calculus

section FiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

noncomputable local instance : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
noncomputable local instance : NormedAlgebra K M := spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
noncomputable local instance : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'


variable (N : Type*) [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

/-- The genuine finite-base composite has the old-base slope off a countable set. -/
theorem IsAPF.exists_finiteBase_comp_derivative_countable [IsAPF K N] :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u : ℝ, 0 < u → u ∉ S →
      HasDerivAt ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N u) u := by
  have := isAPF_of_finite K M
  have hNM : IsAPF M N := (isAPF_finiteBase_iff K M).mp ‹_›
  obtain ⟨S₁, hS₁, hd₁⟩ := IsAPF.exists_apfPsi_derivative_countable K M
  obtain ⟨S₂, hS₂, hd₂⟩ := IsAPF.exists_apfPsi_derivative_countable M N
  refine ⟨S₁ ∪ (apfPsi K M ⁻¹' S₂),
    hS₁.union (hS₂.preimage (IsAPF.strictMono_apfPsi K M).injective), ?_⟩
  intro u hu hnot
  have hn₁ : u ∉ S₁ := fun h => hnot (Or.inl h)
  have hn₂ : apfPsi K M u ∉ S₂ := fun h => hnot (Or.inr h)
  have hψ : 0 ≤ apfPsi K M u := hu.le.trans (IsAPF.le_apfPsi K M u)
  have hd := (hd₂ (apfPsi K M u) hn₂).comp u (hd₁ u hn₁)
  have he : (apfIndex M N (apfPsi K M u) : ℝ) * (apfIndex K M u : ℝ) =
      (apfIndex K N u : ℝ) := by
    have he' := congrArg (fun n : ℕ => (n : ℝ))
      (apfIndex_eq_mul_finiteBase K M (N := N) hu.le)
    simpa only [Nat.cast_mul, mul_comm] using he'.symm
  simpa only [apfHerbrandSlope, max_eq_left hu.le, max_eq_left hψ, he] using hd

/-- The actual Herbrand integral composes across any finite, possibly nonnormal base. -/
theorem IsAPF.apfPsi_finiteBase_comp [IsAPF K N] (u : ℝ) :
    apfPsi M N (apfPsi K M u) = apfPsi K N u := by
  have : IsAPF M N := (isAPF_finiteBase_iff K M).mp ‹_›
  by_cases hu : 0 ≤ u
  · obtain ⟨S, hS, hd⟩ := IsAPF.exists_finiteBase_comp_derivative_countable K M N
    have hcont : ContinuousOn ((apfPsi M N) ∘ (apfPsi K M)) (Set.Icc 0 u) :=
      ((IsAPF.continuous_apfPsi M N).comp
        (IsAPF.continuous_apfPsi K M)).continuousOn
    have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N) hu hS hcont
      (fun v hv => hd v hv.1.1 hv.2)
      (IsAPF.intervalIntegrable_apfHerbrandSlope K N 0 u)
    conv_rhs => rw [apfPsi]
    simpa only [Function.comp_apply, apfPsi_zero, sub_zero] using h.symm
  · rw [apfPsi_of_nonpos K M (le_of_not_ge hu),
      apfPsi_of_nonpos M N (le_of_not_ge hu),
      apfPsi_of_nonpos K N (le_of_not_ge hu)]

end FiniteBase

end FontaineWintenberger
