/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Tower.Stages

/-!
# Ramification bounds and strictness along elementary towers

The upper jumps of an elementary tower determine the first ramification bound and the
strictness constant. The index is constant on the left-open, right-closed interval between
successive jumps. Consequently the infimum defining the strictness constant is attained
as an infimum of right limits at the jumps, with denominator the degree of the next stage.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter
open scoped ENNReal Topology

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- An exact initial full-product interval determines the intrinsic first ramification bound. -/
theorem apfRamificationBound_eq_of_apfSubgroup_eq_top_iff
    (j : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : -1 ≤ b)
    (h : ∀ u : ℝ, -1 ≤ u → (apfSubgroup K j.fieldRange u = ⊤ ↔ u ≤ b)) :
    apfRamificationBound K L = (b : EReal) := by
  rw [apfRamificationBound_eq_embedding K L j]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨u, hu, htop, rfl⟩
    exact EReal.coe_le_coe_iff.mpr ((h u hu).mp htop)
  · exact le_sSup ⟨b, hb, (h b hb).mpr le_rfl, rfl⟩

/-- Before the first full-product failure, the APF index is one. -/
theorem apfIndex_eq_one_of_apfSubgroup_eq_top
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : 0 ≤ u)
    (h : apfSubgroup K j.fieldRange u = ⊤) : apfIndex K L u = 1 := by
  rw [apfIndex_eq_embedding K L j, apfInertiaIndex,
    apfInertiaSubgroup_eq_inf K j.fieldRange u hu, h, top_inf_eq,
    Subgroup.relIndex_self]

/-- The inverse Herbrand function fixes the endpoint of an initial full-product interval. -/
theorem apfPsi_eq_self_of_apfSubgroup_eq_top [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : 0 ≤ b)
    (h : apfSubgroup K j.fieldRange b = ⊤) : apfPsi K L b = b := by
  have hindex : ∀ u ∈ Set.Ioc 0 b, apfIndex K L u = 1 := by
    intro u hu
    apply apfIndex_eq_one_of_apfSubgroup_eq_top K L j hu.1.le
    apply top_unique
    rw [← h]
    exact apfSubgroup_antitoneOn K j.fieldRange (by change -1 ≤ u; linarith [hu.1])
      (by change -1 ≤ b; linarith) hu.2
  simpa only [apfPsi_zero, sub_zero, Nat.cast_one, mul_one] using
    apfPsi_sub_apfPsi_of_apfIndex_eq K L le_rfl hb 1 hindex

/-- Every point above the first term of a sequence tending to infinity lies between two
successive terms, with the right endpoint included. -/
theorem exists_mem_jump_interval (b : ℕ → ℝ)
    (htop : Tendsto b atTop atTop) {u : ℝ} (hu : b 0 < u) :
    ∃ n : ℕ, b n < u ∧ u ≤ b (n + 1) := by
  obtain ⟨m, hm⟩ := (htop.eventually (eventually_ge_atTop u)).exists
  have hex : ∃ m : ℕ, u ≤ b m := ⟨m, hm⟩
  let m := Nat.find hex
  have hm : u ≤ b m := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra! h
    have he : m = 0 := by omega
    exact (not_le_of_gt hu) (he ▸ hm)
  refine ⟨m - 1, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (by omega : m - 1 < m))
  · simpa only [Nat.sub_add_cancel hmpos] using hm

/-- The right limit on an index plateau bounds the strictness constant from above. -/
theorem apfStrictnessConstant_le_of_eventually_apfIndex_eq [IsAPF K L]
    {b : ℝ} {d : ℕ} (hb : apfRamificationBound K L ≤ (b : EReal))
    (hindex : ∀ᶠ u in 𝓝[>] b, apfIndex K L u = d) :
    apfStrictnessConstant K L ≤ ENNReal.ofReal (apfPsi K L b / d) := by
  have hcont : Continuous (fun u : ℝ ↦ ENNReal.ofReal (apfPsi K L u / d)) :=
    ENNReal.continuous_ofReal.comp ((IsAPF.continuous_apfPsi K L).div_const _)
  apply ge_of_tendsto (hcont.continuousAt.mono_left
    (show 𝓝[>] b ≤ 𝓝 b from inf_le_left))
  filter_upwards [self_mem_nhdsWithin, hindex] with u hu hindex
  simpa only [apfStrictnessRatio, hindex] using
    apfStrictnessConstant_le K L (hb.trans (EReal.coe_le_coe_iff.mpr hu.le))

/-- The strictness constant is the infimum of right-hand values at an unbounded sequence
of jumps. The index on each interval `(b n, b (n + 1)]` is the next-stage degree `d n`. -/
theorem apfStrictnessConstant_eq_iInf_of_index_plateaux [IsAPF K L]
    (b : ℕ → ℝ) (d : ℕ → ℕ) (hb : StrictMono b) (hb0 : 0 ≤ b 0)
    (htop : Tendsto b atTop atTop)
    (hbound : apfRamificationBound K L = (b 0 : EReal))
    (hinitial : apfIndex K L (b 0) = 1) (hd : ∀ n, 0 < d n)
    (hindex : ∀ n u, b n < u → u ≤ b (n + 1) → apfIndex K L u = d n) :
    apfStrictnessConstant K L = ⨅ n, ENNReal.ofReal (apfPsi K L (b n) / d n) := by
  apply le_antisymm
  · apply le_iInf
    intro n
    apply apfStrictnessConstant_le_of_eventually_apfIndex_eq K L
      (by rw [hbound]; exact EReal.coe_le_coe_iff.mpr (hb.monotone (Nat.zero_le n)))
    filter_upwards [Ioc_mem_nhdsGT (hb (Nat.lt_succ_self n))] with u hu
    exact hindex n u hu.1 hu.2
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
    · obtain ⟨n, hnu, hun⟩ := exists_mem_jump_interval b htop (lt_of_le_of_ne hbu (Ne.symm he))
      apply (iInf_le _ n).trans
      apply ENNReal.ofReal_le_ofReal
      rw [hindex n u hnu hun]
      exact div_le_div_of_nonneg_right
        ((IsAPF.strictMono_apfPsi K L).monotone hnu.le) (Nat.cast_nonneg _)

end FontaineWintenberger

namespace FontaineWintenberger

open Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

/-- The first upper jump equals the first lower jump when the initial APF product is full.
This is the identity `i(L/K) = i₁` in Wintenberger §1.4.1. -/
theorem apfRamificationBound_eq_apfPsi_of_apfSubgroup_eq_top_iff
    (j : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ u : ℝ, -1 ≤ u → (apfSubgroup K j.fieldRange u = ⊤ ↔ u ≤ b)) :
    apfRamificationBound K L = (apfPsi K L b : EReal) := by
  rw [apfPsi_eq_self_of_apfSubgroup_eq_top K L j hb ((h b (by linarith)).mpr le_rfl)]
  exact apfRamificationBound_eq_of_apfSubgroup_eq_top_iff K L j (by linarith) h

/-- Wintenberger's degree formula for the strictness constant, expressed in terms of the
finite fixed fields on successive jump intervals. The denominator is the degree of the
field *after* the jump, whereas the numerator is the lower-numbered jump itself. -/
theorem apfStrictnessConstant_eq_iInf_finrank_of_apfSubgroup_plateaux
    (j : L →ₐ[K] SeparableClosure K)
    (E : ℕ → FiniteIntermediateField K (SeparableClosure K))
    (b : ℕ → ℝ) (hb : StrictMono b) (hb0 : 0 ≤ b 0) (htop : Tendsto b atTop atTop)
    (hfirst : ∀ u : ℝ, -1 ≤ u →
      (apfSubgroup K j.fieldRange u = ⊤ ↔ u ≤ b 0))
    (hstage : ∀ n u, b n < u → u ≤ b (n + 1) →
      apfSubgroup K j.fieldRange u = (E (n + 1)).val.fixingSubgroup) :
    apfStrictnessConstant K L =
      ⨅ n, ENNReal.ofReal (apfPsi K L (b n) / Module.finrank K (E (n + 1)).val) := by
  have hzero : apfSubgroup K j.fieldRange 0 = ⊤ :=
    (hfirst 0 (by norm_num)).mpr hb0
  apply apfStrictnessConstant_eq_iInf_of_index_plateaux K L b
    (fun n ↦ Module.finrank K (E (n + 1)).val) hb hb0 htop
    (apfRamificationBound_eq_of_apfSubgroup_eq_top_iff K L j (by linarith) hfirst)
    (apfIndex_eq_one_of_apfSubgroup_eq_top K L j hb0
      ((hfirst (b 0) (by linarith)).mpr le_rfl))
    (fun _ ↦ Module.finrank_pos)
  intro n u hnu hun
  rw [apfIndex_eq_index_of_apfSubgroup_zero_eq_top K L j hzero
    (hb0.trans ((hb.monotone (Nat.zero_le n)).trans hnu.le)), hstage n u hnu hun]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K)
    (E (n + 1)).val).symm

end FontaineWintenberger

namespace FontaineWintenberger

open Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

/-- The lower-numbered jumps of an APF tower tend to infinity whenever its upper jumps do. -/
theorem tendsto_apfPsi_comp_atTop {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun n ↦ apfPsi K L (b n)) atTop atTop :=
  tendsto_atTop_mono (fun n ↦ IsAPF.le_apfPsi K L (b n)) hb

/-- For a positive first jump, strict APF is equivalent to a uniform positive lower bound
on the elementary-tower ratios in Wintenberger §1.4.1. -/
theorem isStrictlyAPF_iff_exists_pos_lt_of_index_plateaux
    (b : ℕ → ℝ) (d : ℕ → ℕ) (hb : StrictMono b) (hb0 : 0 < b 0)
    (htop : Tendsto b atTop atTop)
    (hbound : apfRamificationBound K L = (b 0 : EReal))
    (hinitial : apfIndex K L (b 0) = 1) (hd : ∀ n, 0 < d n)
    (hindex : ∀ n u, b n < u → u ≤ b (n + 1) → apfIndex K L u = d n) :
    IsStrictlyAPF K L ↔ ∃ c : ℝ, 0 < c ∧ ∀ n, c < apfPsi K L (b n) / d n := by
  rw [isStrictlyAPF_iff_constant_pos K L (by rw [hbound]; exact_mod_cast hb0),
    apfStrictnessConstant_eq_iInf_of_index_plateaux K L b d hb hb0.le htop hbound
      hinitial hd hindex]
  constructor
  · intro h
    obtain ⟨c, hc, hcf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    refine ⟨c, by exact_mod_cast hc, fun n ↦ ?_⟩
    have hcn := hcf.trans_le (iInf_le _ n)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg c.2).mp (by simpa using hcn)
  · rintro ⟨c, hc, hcn⟩
    exact (ENNReal.ofReal_pos.mpr hc).trans_le
      (le_iInf fun n ↦ ENNReal.ofReal_le_ofReal (hcn n).le)

end FontaineWintenberger
