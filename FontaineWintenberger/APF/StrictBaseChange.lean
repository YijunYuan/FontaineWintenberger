/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.HerbrandTower
public import FontaineWintenberger.APF.FiniteSlope
public import FontaineWintenberger.APF.Strict
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Order.Filter.AtTopBot.Map

/-!
# Strict APF under actual finite base change
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

section Cofinal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual Herbrand order isomorphism preserves the source lower limit at infinity. -/
theorem IsAPF.liminf_comp_apfPsi (hL : IsAPF K L) (f : ℝ → ℝ≥0∞) :
    liminf (f ∘ apfPsi K L) atTop = liminf f atTop := by
  rw [Filter.liminf_comp]
  have he := (apfHerbrandOrderIso K L hL).map_atTop
  change map (apfPsi K L) atTop = atTop at he
  rw [he]

end Cofinal

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

/-- Composition and actual inertia index factorization give the exact source ratio identity. -/
theorem IsAPF.apfStrictnessRatio_finiteBase (hN : IsAPF K N)
    {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio M N (apfPsi K M u) =
      (apfIndex K M u : ℝ≥0∞) * apfStrictnessRatio K N u := by
  have hM := isAPF_of_finite K M
  have hNM := (isAPF_finiteBase_iff K M).mp hN
  have hψ : 0 ≤ apfPsi K M u := hu.trans (IsAPF.le_apfPsi K M hM u)
  have ha : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hM hu)
  have hb : (0 : ℝ) < (apfIndex M N (apfPsi K M u) : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos M N hNM hψ)
  simp only [apfStrictnessRatio]
  rw [IsAPF.apfPsi_finiteBase_comp K M N hN u,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply congrArg ENNReal.ofReal
  have he : (apfIndex K N u : ℝ) =
      (apfIndex K M u : ℝ) * (apfIndex M N (apfPsi K M u) : ℝ) := by
    exact_mod_cast apfIndex_eq_mul_finiteBase K M (N := N) hu
  rw [he]
  field_simp [ne_of_gt ha, ne_of_gt hb]

/-- The actual finite-base strictness lower limits differ by a proved positive finite multiplier. -/
theorem IsAPF.exists_liminf_finiteBase_mul (hN : IsAPF K N) :
    ∃ C : ℕ, 0 < C ∧
      liminf (apfStrictnessRatio M N) atTop =
        (C : ℝ≥0∞) * liminf (apfStrictnessRatio K N) atTop := by
  obtain ⟨C, hC, b, hb, hidx⟩ := exists_apfIndex_finite_constant K M
  refine ⟨C, hC, ?_⟩
  have hev : (apfStrictnessRatio M N ∘ apfPsi K M) =ᶠ[atTop]
      (fun u => (C : ℝ≥0∞) * apfStrictnessRatio K N u) :=
    eventually_atTop.mpr ⟨b, fun u hu => by
      rw [Function.comp_apply, IsAPF.apfStrictnessRatio_finiteBase K M N hN (hb.trans hu),
        hidx u hu]⟩
  have he := liminf_congr hev
  rw [ENNReal.liminf_const_mul_of_ne_top (by simp : (C : ℝ≥0∞) ≠ ⊤)] at he
  exact (IsAPF.liminf_comp_apfPsi K M (isAPF_of_finite K M)
    (apfStrictnessRatio M N)).symm.trans he

/-- Strict APF for arbitrary abstract separable extensions is invariant under finite base change. -/
theorem isStrictlyAPF_finiteBase_iff : IsStrictlyAPF K N ↔ IsStrictlyAPF M N := by
  by_cases hN : IsAPF K N
  · have hNM := (isAPF_finiteBase_iff K M).mp hN
    obtain ⟨C, hC, he⟩ := IsAPF.exists_liminf_finiteBase_mul K M N hN
    simp only [IsStrictlyAPF, hN, hNM, true_and]
    rw [he, ENNReal.mul_pos_iff]
    exact ⟨fun hp => ⟨Nat.cast_pos.mpr hC, hp⟩, And.right⟩
  · constructor
    · intro h
      exact (hN h.1).elim
    · intro h
      exact (hN ((isAPF_finiteBase_iff K M).mpr h.1)).elim

end FiniteBase

end FontaineWintenberger
