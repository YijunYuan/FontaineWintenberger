/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Canonical

/-!
# Strict APF and elementary-tower ratios

Strict arithmetic profiniteness is equivalent to a uniform positive lower bound for the
lower jumps divided by the next-stage degrees. The finite initial unramified and tame
extensions are allowed: their degrees contribute a fixed positive factor to the ratios.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1.
-/

@[expose] public section

namespace FontaineWintenberger

open Filter
open scoped ENNReal Topology

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

/-- The strict APF criterion can be read from the right limits of any positive unbounded
sequence of index plateaux. It does not require a positive first ramification bound. -/
theorem isStrictlyAPF_iff_exists_pos_lt_of_unbounded_index_plateaux
    (b : ℕ → ℝ) (d : ℕ → ℕ) (hb : StrictMono b) (hb0 : 0 < b 0)
    (htop : Tendsto b atTop atTop) (hd : ∀ n, 0 < d n) (hdmono : Monotone d)
    (hindex : ∀ n u, b n < u → u ≤ b (n + 1) → apfIndex K L u = d n) :
    IsStrictlyAPF K L ↔ ∃ c : ℝ, 0 < c ∧ ∀ n, c < apfPsi K L (b n) / d n := by
  constructor
  · intro hstrict
    let := hstrict
    obtain ⟨ε, hε, hεlim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
      (IsStrictlyAPF.liminf_pos (K := K) (L := L))
    obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hεlim)
    obtain ⟨N, hN⟩ := hb.monotone.tendsto_atTop_atTop_iff.mp htop T
    have hεpos : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hsmall : 0 < b 0 / d N := div_pos hb0 (Nat.cast_pos.mpr (hd N))
    let c := min (ε : ℝ) (b 0 / d N)
    have hc : 0 < c := lt_min hεpos hsmall
    refine ⟨c / 2, half_pos hc, fun n ↦ ?_⟩
    apply (half_lt_self hc).trans_le
    rcases le_total N n with hNn | hnN
    · have hbn : T ≤ b n := hN.trans (hb.monotone hNn)
      have hlim : (ε : ℝ) ≤ apfPsi K L (b n) / d n := by
        have hcont := ((IsAPF.continuous_apfPsi K L).div_const (d n : ℝ)).tendsto (b n)
        apply ge_of_tendsto (hcont.mono_left (show 𝓝[>] b n ≤ 𝓝 (b n) from inf_le_left))
        filter_upwards [Ioc_mem_nhdsGT (hb (Nat.lt_succ_self n))] with u hu
        have he := hT u (hbn.trans hu.1.le)
        rw [apfStrictnessRatio, hindex n u hu.1 hu.2] at he
        exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.2).mp (by simpa using he)).le
      exact (min_le_left _ _).trans hlim
    · have hden : (d n : ℝ) ≤ d N := Nat.cast_le.mpr (hdmono hnN)
      have hnum : b 0 ≤ apfPsi K L (b n) :=
        (hb.monotone (Nat.zero_le n)).trans (IsAPF.le_apfPsi K L _)
      exact (min_le_right _ _).trans
        ((div_le_div_of_nonneg_left hb0.le (Nat.cast_pos.mpr (hd n)) hden).trans
          (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)))
  · rintro ⟨c, hc, hcn⟩
    refine ⟨(ENNReal.ofReal_pos.mpr hc).trans_le ?_⟩
    refine le_liminf_of_le (h := ?_)
    apply eventually_atTop.mpr
    refine ⟨b 0 + 1, fun u hu ↦ ?_⟩
    obtain ⟨n, hnu, hun⟩ := exists_mem_jump_interval b htop (by linarith : b 0 < u)
    apply ENNReal.ofReal_le_ofReal
    rw [hindex n u hnu hun]
    exact (hcn n).le.trans (div_le_div_of_nonneg_right
      ((IsAPF.strictMono_apfPsi K L).monotone hnu.le) (Nat.cast_nonneg _))

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    [Fact (¬ Module.Finite K L)]

/-- **Wintenberger §1.4.1.** Strict APF is equivalent to a uniform positive lower bound
for the lower jumps divided by the degrees of the following elementary stages. Initial
unramified and tame extensions are allowed. -/
theorem isStrictlyAPF_iff_apfElementaryLevel_div_finrank :
    IsStrictlyAPF K L ↔ ∃ c : ℝ, 0 < c ∧ ∀ n,
      c < apfElementaryLevel K L n / Module.finrank K (apfElementaryStage K L (n + 1)).val := by
  let b := apfUpperBreak K L
  let d (n : ℕ) := apfIndex K L (b (n + 1))
  let f₀ := (apfSubgroup K L 0).index
  have hf₀ : 0 < (f₀ : ℝ) := by
    apply Nat.cast_pos.mpr
    exact Nat.pos_of_ne_zero
      (((isAPFSubextension_iff_finiteIndex K L).mp inferInstance 0 (by norm_num)).index_ne_zero)
  have hd (n : ℕ) : 0 < d n :=
    IsAPF.apfIndex_pos K L (apfUpperBreak_pos K L (n + 1)).le
  have hdmono : Monotone d := by
    intro m n hmn
    exact IsAPF.apfIndex_monotoneOn K L
      (apfUpperBreak_pos K L (m + 1)).le (apfUpperBreak_pos K L (n + 1)).le
      ((strictMono_apfUpperBreak K L).monotone (Nat.add_le_add_right hmn 1))
  have hindex (n : ℕ) (u : ℝ) (hnu : b n < u) (hun : u ≤ b (n + 1)) :
      apfIndex K L u = d n := by
    have hu : 0 ≤ u := (apfUpperBreak_pos K L n).le.trans hnu.le
    have hv := (apfUpperBreak_pos K L (n + 1)).le
    change apfIndex K L u = apfIndex K L (b (n + 1))
    rw [apfIndex_eq_embedding K L L.val u, apfIndex_eq_embedding K L L.val (b (n + 1))]
    simp only [IntermediateField.fieldRange_val, apfInertiaIndex,
      apfInertiaSubgroup_eq_inf K L u hu, apfInertiaSubgroup_eq_inf K L (b (n + 1)) hv,
      apfSubgroup_eq_at_next_upperBreak K L hnu hun]
    rfl
  have hdegree (n : ℕ) :
      Module.finrank K (apfElementaryStage K L (n + 1)).val = f₀ * d n := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K),
      fixingSubgroup_apfElementaryStage]
    simpa only [IntermediateField.fieldRange_val] using
      apfSubgroup_index_eq_index_zero_mul_apfIndex K L L.val
        (apfUpperBreak_pos K L (n + 1)).le
  have hratio (n : ℕ) :
      apfElementaryLevel K L n / Module.finrank K (apfElementaryStage K L (n + 1)).val =
        (apfPsi K L (b n) / d n) / f₀ := by
    rw [apfElementaryLevel, hdegree, Nat.cast_mul,
      mul_comm (f₀ : ℝ), div_mul_eq_div_div]
  rw [isStrictlyAPF_iff_exists_pos_lt_of_unbounded_index_plateaux K L b d
    (strictMono_apfUpperBreak K L) (apfUpperBreak_pos K L 0) (tendsto_apfUpperBreak K L)
    hd hdmono hindex]
  constructor
  · rintro ⟨c, hc, hcn⟩
    refine ⟨c / f₀, div_pos hc hf₀, fun n ↦ ?_⟩
    rw [hratio]
    exact (div_lt_div_iff_of_pos_right hf₀).mpr (hcn n)
  · rintro ⟨c, hc, hcn⟩
    refine ⟨c * f₀, mul_pos hc hf₀, fun n ↦ ?_⟩
    have h := hcn n
    rw [hratio] at h
    exact (lt_div_iff₀ hf₀).mp h

end FontaineWintenberger
