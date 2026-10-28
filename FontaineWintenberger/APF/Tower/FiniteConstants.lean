/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.APF.Tower.Elementary

/-!
# Strictness constants for finite elementary towers

The degree formula for the strictness constant also applies to a finite sequence of jumps.
After the last jump, the index is constant on the entire remaining half-line. The infimum
is therefore over the finite collection of right limits at the jumps.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1, finite case.
-/

@[expose] public section

namespace FontaineWintenberger

open Filter
open scoped ENNReal Topology

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

omit [IsAPF K L] in
/-- Every finite separable extension is strictly APF, including unramified and tame extensions. -/
theorem isStrictlyAPF_of_finite [FiniteDimensional K L] : IsStrictlyAPF K L :=
  (isStrictlyAPF_finite_extension_iff K L K).mpr (isStrictlyAPF_self K)

/-- The infimum of the strictness ratio for finitely many plateaux, including the final
unbounded plateau, equals the infimum of its right limits at the jumps. -/
theorem apfStrictnessConstant_eq_iInf_fin_of_index_plateaux
    {m : ℕ} [NeZero m] (b : Fin m → ℝ) (d : Fin m → ℕ)
    (hb : StrictMono b) (hb0 : 0 ≤ b 0)
    (hbound : apfRamificationBound K L = (b 0 : EReal))
    (hinitial : apfIndex K L (b 0) = 1) (hd : ∀ n, 0 < d n)
    (hindex : ∀ n u, b n < u → (∀ k, n < k → u ≤ b k) → apfIndex K L u = d n) :
    apfStrictnessConstant K L = ⨅ n, ENNReal.ofReal (apfPsi K L (b n) / d n) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro n
    apply apfStrictnessConstant_le_of_eventually_apfIndex_eq K L
      (by rw [hbound]; exact EReal.coe_le_coe_iff.mpr (hb.monotone (Fin.zero_le n)))
    have hnext : ∀ᶠ u in 𝓝[>] b n, ∀ k, n < k → u ≤ b k := by
      apply eventually_all.mpr
      intro k
      by_cases hnk : n < k
      · filter_upwards [Ioc_mem_nhdsGT (hb hnk)] with u hu
        exact fun _ ↦ hu.2
      · exact Eventually.of_forall fun _ h ↦ (hnk h).elim
    filter_upwards [self_mem_nhdsWithin, hnext] with u hu hnext
    exact hindex n u hu hnext
  · apply le_iInf
    intro u
    apply le_iInf
    intro hu
    have hbu : b 0 ≤ u := EReal.coe_le_coe_iff.mp (hbound ▸ hu)
    by_cases he : u = b 0
    · subst u
      apply (iInf_le _ 0).trans
      rw [apfStrictnessRatio, hinitial, Nat.cast_one, div_one]
      apply ENNReal.ofReal_le_ofReal
      exact div_le_self (hb0.trans (IsAPF.le_apfPsi K L (b 0)))
        (by exact_mod_cast hd 0)
    · let S : Finset (Fin m) := Finset.univ.filter fun n ↦ b n < u
      have hS : S.Nonempty := by
        refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact lt_of_le_of_ne hbu (Ne.symm he)
      let n := S.max' hS
      have hnu : b n < u := (Finset.mem_filter.mp (S.max'_mem hS)).2
      have hnext (k : Fin m) (hnk : n < k) : u ≤ b k := by
        by_contra! hku
        have hk : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hku⟩
        exact (not_le_of_gt hnk) (S.le_max' k hk)
      apply (iInf_le _ n).trans
      apply ENNReal.ofReal_le_ofReal
      rw [hindex n u hnu hnext]
      exact div_le_div_of_nonneg_right
        ((IsAPF.strictMono_apfPsi K L).monotone hnu.le) (Nat.cast_nonneg _)

/-- The finite form of the degree formula, with the terminal field appearing in the
denominator at the last jump. -/
theorem apfStrictnessConstant_eq_iInf_finrank_of_finite_plateaux
    (j : L →ₐ[K] SeparableClosure K) {m : ℕ} [NeZero m]
    (E : Fin (m + 1) → FiniteIntermediateField K (SeparableClosure K))
    (b : Fin m → ℝ) (hb : StrictMono b) (hb0 : 0 ≤ b 0)
    (hfirst : ∀ u : ℝ, -1 ≤ u → (apfSubgroup K j.fieldRange u = ⊤ ↔ u ≤ b 0))
    (hstage : ∀ n u, b n < u → (∀ k, n < k → u ≤ b k) →
      apfSubgroup K j.fieldRange u = (E n.succ).val.fixingSubgroup) :
    apfStrictnessConstant K L =
      ⨅ n, ENNReal.ofReal (apfPsi K L (b n) / Module.finrank K (E n.succ).val) := by
  have hzero : apfSubgroup K j.fieldRange 0 = ⊤ :=
    (hfirst 0 (by norm_num)).mpr hb0
  apply apfStrictnessConstant_eq_iInf_fin_of_index_plateaux K L b
    (fun n ↦ Module.finrank K (E n.succ).val) hb hb0
    (apfRamificationBound_eq_of_apfSubgroup_eq_top_iff K L j (by linarith) hfirst)
    (apfIndex_eq_one_of_apfSubgroup_eq_top K L j hb0
      ((hfirst (b 0) (by linarith)).mpr le_rfl))
    (fun _ ↦ Module.finrank_pos)
  intro n u hnu hnext
  rw [apfIndex_eq_index_of_apfSubgroup_zero_eq_top K L j hzero
    (hb0.trans ((hb.monotone (Fin.zero_le n)).trans hnu.le)), hstage n u hnu hnext]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K)
    (E n.succ).val).symm

end FontaineWintenberger
