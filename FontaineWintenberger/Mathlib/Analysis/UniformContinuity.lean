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
  obtain ⟨y, hy⟩ : ∃ y : S, Valued.v.restrict y = γ.val :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ _
  have hy₀ : y ≠ 0 := Valued.v.restrict.ne_zero_iff.mp (hy.trans_ne γ.ne_zero)
  refine ⟨Units.mk0 (Valued.v.restrict (e.symm y)) (by simpa using hy₀), ?_⟩
  intro x hx
  change Valued.v.restrict (e x) < γ.val
  rw [← hy, Valued.v.restrict_lt_iff, he, ← e.apply_symm_apply y, he]
  exact Valued.v.restrict_lt_iff.mp hx

end FontaineWintenberger
