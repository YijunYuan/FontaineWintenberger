/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Uniform continuity of valuation-preserving field equivalences

The valued-field uniformities are preserved without a surjectivity
assumption on the ambient value group.

## Main results

* `valuedRingEquiv_uniformContinuous`: A ring equivalence preserving the valuations preserves the
  existing valuation uniformities, even without surjectivity onto the ambient value group.

## References

* Mathlib; this file is an upstream candidate and has no project-specific reference.
-/

@[expose] public section

namespace FontaineWintenberger

/-- A ring equivalence preserving the valuations preserves the
existing valuation uniformities, even without surjectivity onto the ambient value group. -/
theorem valuedRingEquiv_uniformContinuous {R S Γ₀ : Type*} [Field R] [Field S]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀] [Valued S Γ₀]
    (e : R ≃+* S) (he : ∀ x, (Valued.v (e x) : Γ₀) = Valued.v x) :
    UniformContinuous e := by
  refine uniformContinuous_of_continuousAt_zero e.toAddMonoidHom ?_
  simp only [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero R Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero S Γ₀),
    true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit (Valued.v : Valuation S Γ₀) γ
  have hr₀ : r ≠ 0 := (Valued.v.ne_zero_iff).mp hr.ne'
  have hs₀ : s ≠ 0 := (Valued.v.ne_zero_iff).mp hs.ne'
  have hpre : e.symm (r / s) ≠ 0 := by
    simpa only [map_ne_zero] using div_ne_zero hr₀ hs₀
  let δ := Units.mk0 (Valued.v.restrict (e.symm (r / s)))
    (Valued.v.restrict.ne_zero_iff.mpr hpre)
  refine ⟨δ, ?_⟩
  intro x hx
  have hx' : (Valued.v x : Γ₀) < Valued.v (e.symm (r / s)) :=
    Valued.v.restrict_lt_iff.mp hx
  have ht : (Valued.v (r / s) : Γ₀) = Valued.v (e.symm (r / s)) := by
    simpa only [RingEquiv.apply_symm_apply] using he (e.symm (r / s))
  rw [← hrs, ← map_div₀]
  apply Valued.v.restrict_lt_iff.mpr
  change (Valued.v (e x) : Γ₀) < Valued.v (r / s)
  rw [he, ht]
  exact hx'

end FontaineWintenberger
