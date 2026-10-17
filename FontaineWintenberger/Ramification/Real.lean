/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Valuation
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Basic.ENNReal.Real

/-!
# Real lower numbering

The real lower groups are the existing ideal-inertia groups at the integer
ceiling. Their valuation bound uses the same intrinsic order, including
infinity and negative indices.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- Real lower numbering, extending canonical integer ideal-inertia groups by ceilings. -/
noncomputable def lowerRamificationGroupReal (I : Ideal R) (t : ℝ) : Subgroup G :=
  lowerRamificationGroup G I ⌈t⌉

@[simp]
theorem lowerRamificationGroupReal_intCast (I : Ideal R) (n : ℤ) :
    lowerRamificationGroupReal G I (n : ℝ) = lowerRamificationGroup G I n := by
  simp [lowerRamificationGroupReal]

theorem lowerRamificationGroupReal_antitone (I : Ideal R) :
    Antitone (lowerRamificationGroupReal G I) :=
  (lowerRamificationGroup_antitone G I).comp_monotone Int.ceil_mono

theorem lowerRamificationGroupReal_of_le_neg_one (I : Ideal R) {t : ℝ} (ht : t ≤ -1) :
    lowerRamificationGroupReal G I t = ⊤ :=
  lowerRamificationGroup_of_le_neg_one G I (Int.ceil_le.mpr (by simpa using ht))

@[simp]
theorem lowerRamificationGroupReal_zero (I : Ideal R) :
    lowerRamificationGroupReal G I 0 = I.inertia G := by
  simp [lowerRamificationGroupReal]

@[simp]
theorem lowerRamificationGroupReal_subgroupOf (I : Ideal R) (t : ℝ) (H : Subgroup G) :
    (lowerRamificationGroupReal G I t).subgroupOf H = lowerRamificationGroupReal H I t := rfl

theorem lowerRamificationGroupReal_map_subtype (I : Ideal R) (t : ℝ) (H : Subgroup G) :
    (lowerRamificationGroupReal H I t).map H.subtype = lowerRamificationGroupReal G I t ⊓ H :=
  lowerRamificationGroup_map_subtype G I ⌈t⌉ H

instance maximalIdeal_lowerRamificationGroupReal_normal [IsLocalRing R] (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).Normal :=
  maximalIdeal_lowerRamificationGroup_normal G ⌈t⌉

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The ceiling bound is exactly the source's real displacement-order bound. -/
theorem mem_lowerRamificationGroupReal_iff_le_order (t : ℝ) (g : G) :
    g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t ↔
      ENNReal.ofReal (t + 1) ≤ (ramificationOrder (R := R) G g : ℝ≥0∞) := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_le_order]
  generalize ramificationOrder (R := R) G g = j
  cases j using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.toENNReal_coe, ENat.natCast_le_natCast, ENNReal.ofReal_le_natCast]
    rw [Int.toNat_le]
    constructor
    · intro h
      have hc : ⌈t⌉ ≤ (n : ℤ) - 1 := by omega
      have hr := Int.ceil_le.mp hc
      push_cast at hr
      linarith
    · intro h
      have hc : ⌈t⌉ ≤ (n : ℤ) - 1 := Int.ceil_le.mpr (by push_cast; linarith)
      omega

/-- Finite faithful actions are eventually trivial also in real lower numbering. -/
theorem lowerRamificationGroupReal_eventually_eq_bot [Finite G] [FaithfulSMul G R] :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t = ⊥ := by
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := R) G
  refine ⟨N, fun t ht => ?_⟩
  have hceil : (N : ℤ) ≤ ⌈t⌉ := by exact_mod_cast ht.trans (Int.le_ceil t)
  have hnonneg : 0 ≤ ⌈t⌉ := (Int.natCast_nonneg N).trans hceil
  have h := hN ⌈t⌉.toNat (by omega)
  simpa only [lowerRamificationGroupReal, Int.toNat_of_nonneg hnonneg] using h

end FontaineWintenberger
