/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Elementary.Basic
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Herbrand

/-!
# Herbrand functions of elementary extensions

The inverse Herbrand function of an elementary extension is the identity below its level.
This identifies the level with its own transformed parameter and is the starting point for
the recurrence of transformed jumps in an elementary tower.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §§1.3–1.4.
-/

@[expose] public section

namespace FontaineWintenberger

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable {i : ℝ}

/-- An elementary extension has inertia-relative index one below its level. -/
theorem IsElementary.apfIndex_eq_one (h : IsElementary K L i)
    {u : ℝ} (hu : 0 ≤ u) (hui : u ≤ i) : apfIndex K L u = 1 := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfIndex_eq_embedding K L j, apfInertiaIndex,
    apfInertiaSubgroup_eq_inf K j.fieldRange u hu,
    h.apfSubgroup_eq_top_of_le j (by linarith) hui, top_inf_eq, Subgroup.relIndex_self]

/-- The inverse Herbrand function of an elementary extension is the identity below its level. -/
theorem IsElementary.apfPsi_eq_self (h : IsElementary K L i)
    {u : ℝ} (hui : u ≤ i) : apfPsi K L u = u := by
  by_cases hu : u ≤ 0
  · exact apfPsi_of_nonpos K L hu
  · have hu := (lt_of_not_ge hu).le
    rw [apfPsi_eq_integral_index K L hu]
    have heq : (∫ v in (0 : ℝ)..u, (apfIndex K L v : ℝ)) = ∫ _v in (0 : ℝ)..u, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le hu]
      intro v hv
      dsimp only
      rw [h.apfIndex_eq_one hv.1 (hv.2.trans hui), Nat.cast_one]
    simpa using heq

/-- The intrinsic inertia index of an elementary extension has exactly one step. -/
theorem IsElementary.apfIndex_eq (h : IsElementary K L i) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K L u = if u ≤ i then 1 else Module.finrank K L := by
  let := h.finite
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfIndex_eq_index_of_apfSubgroup_zero_eq_top K L j
    (h.apfSubgroup_eq_top_of_le j (by norm_num) h.level_pos.le) hu]
  split_ifs with hui
  · rw [h.apfSubgroup_eq_top_of_le j (by linarith) hui, Subgroup.index_top]
  · rw [h.apfSubgroup_eq_fixingSubgroup j u (lt_of_not_ge hui),
      ← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K)]
    exact j.equivFieldRange.toLinearEquiv.finrank_eq.symm

/-- The inverse Herbrand function of an elementary extension is piecewise affine. -/
theorem IsElementary.apfPsi_eq (h : IsElementary K L i) (u : ℝ) :
    apfPsi K L u = if u ≤ i then u else i + (Module.finrank K L : ℝ) * (u - i) := by
  let := h.finite
  exact apfPsi_eq_of_index_profile K L h.level_pos.le (fun _ hu ↦ h.apfIndex_eq hu) u

/-- The forward Herbrand function of an elementary extension is piecewise affine. -/
theorem IsElementary.apfPhi_eq [IsAPF K L] (h : IsElementary K L i) (u : ℝ) :
    apfPhi K L u = if u ≤ i then u else i + (u - i) / (Module.finrank K L : ℝ) := by
  let := h.finite
  exact apfPhi_eq_of_index_profile K L h.level_pos.le (fun _ hu ↦ h.apfIndex_eq hu) u

end FontaineWintenberger
