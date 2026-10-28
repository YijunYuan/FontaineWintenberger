/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Stages

/-!
# Stabilization of Herbrand functions on finite stages

A finite subextension containing the APF stage at `u` has the same APF products as the
whole extension at every parameter between `-1` and `u`. Consequently its inverse Herbrand
function agrees with that of the whole extension up to `u`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4 and the proof of Corollary 3.3.6.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- Containing an APF stage preserves the APF product at that parameter. -/
theorem apfSubgroup_eq_of_apfFiniteStage_le
    (L E : IntermediateField K (SeparableClosure K)) {u : ℝ}
    (hEL : E ≤ L) (hstage : apfFiniteStage K L u ≤ E) :
    apfSubgroup K E u = apfSubgroup K L u := by
  apply le_antisymm
  · exact sup_le
      ((IntermediateField.fixingSubgroup_le hstage).trans_eq
        (fixingSubgroup_apfFiniteStage K L u)) le_sup_right
  · exact sup_le
      ((IntermediateField.fixingSubgroup_le hEL).trans le_sup_left) le_sup_right

/-- The intrinsic index agrees below a stage contained in the finite subextension. -/
theorem apfIndex_eq_of_apfFiniteStage_le
    (L E : IntermediateField K (SeparableClosure K)) {u v : ℝ}
    (hEL : E ≤ L) (hstage : apfFiniteStage K L u ≤ E) (hv : 0 ≤ v) (hvu : v ≤ u) :
    apfIndex K E v = apfIndex K L v := by
  rw [apfIndex_eq_embedding K E E.val, apfIndex_eq_embedding K L L.val]
  simp only [IntermediateField.fieldRange_val, apfInertiaIndex,
    apfInertiaSubgroup_eq_inf K _ v hv]
  rw [apfSubgroup_eq_of_apfFiniteStage_le K L E hEL
    ((apfFiniteStage_mono K L (by linarith) (by linarith) hvu).trans hstage)]

/-- A stage containment preserves the inverse Herbrand function on the preceding interval. -/
theorem apfPsi_eq_of_apfFiniteStage_le
    (L E : IntermediateField K (SeparableClosure K)) {u v : ℝ}
    (hEL : E ≤ L) (hstage : apfFiniteStage K L u ≤ E) (hvu : v ≤ u) :
    apfPsi K E v = apfPsi K L v := by
  by_cases hv : v ≤ 0
  · rw [apfPsi_of_nonpos K E hv, apfPsi_of_nonpos K L hv]
  · have hv : 0 ≤ v := (lt_of_not_ge hv).le
    rw [apfPsi_eq_integral_index K E hv, apfPsi_eq_integral_index K L hv]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hv]
    intro x hx
    exact congrArg (fun n : ℕ ↦ (n : ℝ))
      (apfIndex_eq_of_apfFiniteStage_le K L E hEL hstage hx.1 (hx.2.trans hvu))

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

/-- On every bounded interval the inverse Herbrand functions of all sufficiently large finite
subextensions agree exactly with the inverse Herbrand function of the APF extension. -/
theorem IsAPF.exists_finiteIntermediateField_apfPsi_eq (u : ℝ) :
    ∃ E : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, E ≤ F →
      ∀ v : ℝ, v ≤ u → apfPsi K F.val v = apfPsi K L v := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨E, hE⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (show -1 ≤ max u 0 by linarith [le_max_right u 0])
  refine ⟨E, fun F hEF v hv ↦ ?_⟩
  rw [apfPsi_algEquiv K F.val (IntermediateField.equivMap F.val j),
    apfPsi_algEquiv K L j.equivFieldRange]
  apply apfPsi_eq_of_apfFiniteStage_le K j.fieldRange (F.val.map j)
  · rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  · rw [← hE]
    exact IntermediateField.map_mono j hEF
  · exact hv.trans (le_max_left u 0)

end FontaineWintenberger
