/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Defs
public import Mathlib.Data.EReal.Basic

/-!
# The extended ramification bound

The source supremum lives in the extended reals. Its defining set contains
`-1`, and for the trivial extension it is unbounded, giving positive infinity.
Actual conjugacy makes the bound independent of the separable embedding.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

omit [Algebra.IsSeparable K L] in
theorem apfSubgroup_fieldRange_index_eq (i j : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    (apfSubgroup K i.fieldRange u).index = (apfSubgroup K j.fieldRange u).index := by
  obtain ⟨σ, hσ⟩ := exists_aut_comp_separableClosure_embeddings K L i j
  have hr : i.fieldRange.map σ.toAlgHom = j.fieldRange := by
    rw [AlgHom.map_fieldRange, hσ]
  rw [← hr, apfSubgroup_map_index]

omit [Algebra.IsSeparable K L] in
theorem apfSubgroup_fieldRange_eq_top_iff (i j : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    apfSubgroup K i.fieldRange u = ⊤ ↔ apfSubgroup K j.fieldRange u = ⊤ := by
  rw [← Subgroup.index_eq_one, ← Subgroup.index_eq_one,
    apfSubgroup_fieldRange_index_eq K L i j u]

/-- The source supremum, including positive infinity for an unbounded set. -/
noncomputable def apfRamificationBound : EReal :=
  sSup {x : EReal | ∃ u : ℝ, -1 ≤ u ∧
    apfSubgroup K (IsSepClosed.lift : L →ₐ[K] SeparableClosure K).fieldRange u = ⊤ ∧
      x = (u : EReal)}

theorem apfRamificationBound_eq_embedding (i : L →ₐ[K] SeparableClosure K) :
    apfRamificationBound K L = sSup {x : EReal | ∃ u : ℝ, -1 ≤ u ∧
      apfSubgroup K i.fieldRange u = ⊤ ∧ x = (u : EReal)} := by
  unfold apfRamificationBound
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, apfSubgroup_fieldRange_eq_top_iff K L _ i]

theorem le_apfRamificationBound (i : L →ₐ[K] SeparableClosure K) {u : ℝ}
    (hu : -1 ≤ u) (h : apfSubgroup K i.fieldRange u = ⊤) :
    (u : EReal) ≤ apfRamificationBound K L := by
  rw [apfRamificationBound_eq_embedding K L i]
  exact le_sSup ⟨u, hu, h, rfl⟩

theorem neg_one_le_apfRamificationBound : (-1 : EReal) ≤ apfRamificationBound K L := by
  simpa only [EReal.coe_neg, EReal.coe_one] using
    le_apfRamificationBound K L IsSepClosed.lift le_rfl (apfSubgroup_neg_one K _)

theorem apfRamificationBound_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) :
    apfRamificationBound K L = apfRamificationBound K M := by
  let j : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfRamificationBound_eq_embedding K L (j.comp e.toAlgHom),
    apfRamificationBound_eq_embedding K M j]
  have hr : (j.comp e.toAlgHom).fieldRange = j.fieldRange := by
    rw [← AlgHom.map_fieldRange, AlgHom.fieldRange_eq_top.mpr e.surjective,
      ← AlgHom.fieldRange_eq_map]
  rw [hr]

@[simp]
theorem apfRamificationBound_self : apfRamificationBound K K = ⊤ := by
  let i : K →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have hfix : i.fieldRange.fixingSubgroup = ⊤ := by
    ext σ
    simp only [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_top, iff_true]
    intro x hx
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    have hi : i a = algebraMap K (SeparableClosure K) a := by simpa using i.commutes a
    rw [hi]
    exact σ.commutes a
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  have h : ((max r 0 + 1 : ℝ) : EReal) ≤ apfRamificationBound K K :=
    le_apfRamificationBound K K i (by linarith [le_max_right r 0])
      (by simp only [apfSubgroup, hfix, top_sup_eq])
  apply lt_of_lt_of_le _ h
  exact EReal.coe_lt_coe_iff.mpr (by linarith [le_max_left r 0])

end FontaineWintenberger
