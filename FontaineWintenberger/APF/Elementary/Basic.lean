/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.RamificationBound

/-!
# Elementary extensions

A finite separable extension is elementary of level `i > 0` if its absolute APF product
is the whole group at `i` and is the fixing subgroup at every parameter greater than `i`.
This is Wintenberger's definition, including nonnormal extensions. Quantifying over embeddings
makes the predicate independent of the chosen separable closure embedding.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.3.1.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A finite separable extension with one positive ramification break, in the sense of
Wintenberger §1.3.1. The formulation applies to nonnormal extensions. -/
structure IsElementary (i : ℝ) : Prop where
  /-- The extension is finite. -/
  finite : FiniteDimensional K L
  /-- The extension is separable. -/
  separable : Algebra.IsSeparable K L
  /-- The elementary level is positive. -/
  level_pos : 0 < i
  /-- The upper product is full at the elementary level. -/
  apfSubgroup_eq_top : ∀ j : L →ₐ[K] SeparableClosure K, apfSubgroup K j.fieldRange i = ⊤
  /-- Above the elementary level, the upper product is the fixing subgroup. -/
  apfSubgroup_eq_fixingSubgroup : ∀ (j : L →ₐ[K] SeparableClosure K) (u : ℝ), i < u →
    apfSubgroup K j.fieldRange u = j.fieldRange.fixingSubgroup

variable {K L} {i : ℝ}

/-- It suffices to check elementarity in one separable-closure embedding. -/
theorem IsElementary.of_embedding [FiniteDimensional K L]
    (j : L →ₐ[K] SeparableClosure K) (hi : 0 < i)
    (htop : apfSubgroup K j.fieldRange i = ⊤)
    (hfix : ∀ u : ℝ, i < u → apfSubgroup K j.fieldRange u = j.fieldRange.fixingSubgroup) :
    IsElementary K L i := by
  refine ⟨inferInstance, inferInstance, hi, fun k ↦ ?_, fun k u hu ↦ ?_⟩
  · exact (apfSubgroup_fieldRange_eq_top_iff K L j k i).mp htop
  · obtain ⟨σ, hσ⟩ := exists_aut_comp_separableClosure_embeddings K L j k
    have hr : j.fieldRange.map σ.toAlgHom = k.fieldRange := by
      rw [AlgHom.map_fieldRange, hσ]
    rw [← hr, apfSubgroup_map, hfix u hu, IsGalois.map_fixingSubgroup]

omit [Algebra.IsSeparable K L] in
/-- An elementary extension has full upper product at every parameter below its level. -/
theorem IsElementary.apfSubgroup_eq_top_of_le (h : IsElementary K L i)
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) (hui : u ≤ i) :
    apfSubgroup K j.fieldRange u = ⊤ := by
  apply top_unique
  rw [← h.apfSubgroup_eq_top j]
  exact apfSubgroup_antitoneOn K j.fieldRange hu
    (show -1 ≤ i by linarith [h.level_pos]) hui

/-- The elementary level is a lower bound for the first ramification bound. -/
theorem IsElementary.le_apfRamificationBound (h : IsElementary K L i) :
    (i : EReal) ≤ apfRamificationBound K L :=
  FontaineWintenberger.le_apfRamificationBound K L
    (IsSepClosed.lift (K := K) (L := L) (M := SeparableClosure K))
    (by linarith [h.level_pos])
    (h.apfSubgroup_eq_top _)

/-- For a nontrivial elementary extension, the elementary level equals the first bound. -/
theorem IsElementary.apfRamificationBound_eq (h : IsElementary K L i)
    (hdegree : 1 < Module.finrank K L) : apfRamificationBound K L = (i : EReal) := by
  let := h.finite
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have hfix : j.fieldRange.fixingSubgroup ≠ ⊤ := by
    intro hf
    have hidx := congrArg Subgroup.index hf
    rw [Subgroup.index_top,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K)] at hidx
    have hrank := j.equivFieldRange.toLinearEquiv.finrank_eq
    omega
  apply le_antisymm _ h.le_apfRamificationBound
  rw [apfRamificationBound_eq_embedding K L j]
  apply sSup_le
  rintro x ⟨u, _hu, htop, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  by_contra! hiu
  exact hfix ((h.apfSubgroup_eq_fixingSubgroup j u hiu).symm.trans htop)

end FontaineWintenberger
