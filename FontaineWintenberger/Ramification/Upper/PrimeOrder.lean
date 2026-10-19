/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Ramification of prime-order Galois groups

Every subgroup of a prime-order Galois group is trivial or full. The actual
lower groups consequently give the same order to every nonidentity element.
-/

@[expose] public section

namespace FontaineWintenberger

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [Fact (Nat.card G).Prime]

omit [Finite G] in
/-- Prime group order makes all nonidentity intrinsic ramification orders
equal, directly through the actual ideal-inertia subgroups. -/
theorem ramificationOrder_eq_of_prime_card {g h : G} (hg : g ≠ 1) (hh : h ≠ 1) :
    ramificationOrder (R := B) G g = ramificationOrder (R := B) G h := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have hmem (s : G) : s ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n : ℤ) ↔
        (n : ℕ∞) + 1 ≤ ramificationOrder (R := B) G s := by
      simpa using mem_lowerRamificationGroup_iff_le_order (R := B) G (n : ℤ) s
    have heq : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n : ℤ) ↔
        h ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n : ℤ) := by
      rcases (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n :
          ℤ)).eq_bot_or_eq_top_of_prime_card
        with hb | ht
      · simp [hb, hg, hh]
      · simp [ht]
    simpa only [Nat.cast_add, Nat.cast_one] using (hmem g).symm.trans (heq.trans (hmem h))

/-- A finite faithful prime-order action supplies an actual finite common
order, rather than an order certificate assumed from the caller. -/
theorem exists_common_ramificationOrder_of_prime_card [FaithfulSMul G B] :
    ∃ m : ℕ, ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = m := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (Fact.out : (Nat.card G).Prime).one_lt
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hfinite := (ramificationOrder_eq_top_iff (R := B) G g).not.mpr hg
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinite
  refine ⟨m, fun h hh => ?_⟩
  exact (ramificationOrder_eq_of_prime_card G hh hg).trans hm.symm

/-- A full zero lower group makes the actual common order a positive integer. -/
theorem exists_common_ramificationOrder_succ_of_prime_card [FaithfulSMul G B]
    (hzero : lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0 = ⊤) :
    ∃ t : ℕ, ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = (t + 1 : ℕ) := by
  obtain ⟨m, hm⟩ := exists_common_ramificationOrder_of_prime_card (B := B) G
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp
    (Fact.out : (Nat.card G).Prime).one_lt
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hge : (1 : ℕ∞) ≤ m := by
    have hmem : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0 := by
      rw [hzero]; trivial
    have hv := (mem_lowerRamificationGroup_iff_le_order (R := B) G 0 g).mp hmem
    simpa only [hm g hg, zero_add, Int.toNat_one, Nat.cast_one] using hv
  have hmpos : 1 ≤ m := by exact_mod_cast hge
  refine ⟨m - 1, fun h hh => ?_⟩
  simpa only [Nat.sub_add_cancel hmpos] using hm h hh

omit [Finite G] [Fact (Nat.card G).Prime] in
/-- A common nonidentity order computes every actual nonnegative lower group. -/
theorem lowerRamificationGroup_nat_of_common_order {m : ℕ}
    (hm : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = m) (n : ℕ) :
    lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n =
      if n < m then ⊤ else ⊥ := by
  classical
  ext g
  by_cases hg : g = 1
  · subst g
    simp
  · have hmem : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n : ℤ) ↔ n < m := by
      rw [mem_lowerRamificationGroup_iff_le_order, hm g hg]
      norm_cast
    rw [hmem]
    split_ifs <;> simp_all

omit [Finite G] [Fact (Nat.card G).Prime] in
/-- Real lower numbering keeps the weak endpoint at the actual common break. -/
theorem lowerRamificationGroupReal_of_common_order {m : ℕ}
    (hm : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = m) (s : ℝ) :
    lowerRamificationGroupReal G (IsLocalRing.maximalIdeal B) s =
      if s ≤ (m : ℝ) - 1 then ⊤ else ⊥ := by
  classical
  ext g
  by_cases hg : g = 1
  · subst g
    simp
  · have hmem : g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal B) s ↔
        s ≤ (m : ℝ) - 1 := by
      rw [mem_lowerRamificationGroupReal_iff_le_order, hm g hg]
      simp only [ENat.toENNReal_coe, ENNReal.ofReal_le_natCast]
      constructor <;> intro h <;> linarith
    rw [hmem]
    split_ifs <;> simp_all

omit [Fact (Nat.card G).Prime] in
/-- At a nonnegative common break the actual Herbrand function fixes the break. -/
theorem herbrandFunction_common_break {t : ℕ}
    (ht : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = (t + 1 : ℕ)) :
    herbrandFunction (R := B) G t = t := by
  classical
  let := Fintype.ofFinite G
  have ht0 : (-1 : ℝ) ≤ t := by have := Nat.cast_nonneg (α := ℝ) t; linarith
  have hzero : lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0 = ⊤ := by
    simpa using lowerRamificationGroup_nat_of_common_order G ht 0
  have htrunc (g : G) : truncatedRamificationOrder (R := B) G g t = (t : ℝ) + 1 := by
    by_cases hg : g = 1
    · subst g
      exact truncatedRamificationOrder_one G t ht0
    · rw [truncatedRamificationOrder_of_order_nat G (ht g hg)]
      simp [max_eq_left (show (0 : ℝ) ≤ t + 1 by positivity)]
  rw [herbrandFunction_eq_sum G ht0, herbrandSum, hzero, Subgroup.card_top]
  simp only [htrunc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

omit [Fact (Nat.card G).Prime] in
/-- The weak common lower break is also the weak common upper break. -/
theorem upperRamificationGroup_of_common_order {t : ℕ}
    (ht : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = (t + 1 : ℕ))
    {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := B) G u = if u ≤ t then ⊤ else ⊥ := by
  have ht0 : (-1 : ℝ) ≤ t := by have := Nat.cast_nonneg (α := ℝ) t; linarith
  have hfixed : inverseHerbrandFunction (R := B) G t = t := by
    simpa only [herbrandFunction_common_break G ht] using
      inverseHerbrandFunction_herbrandFunction (R := B) G ht0
  have hle : inverseHerbrandFunction (R := B) G u ≤ t ↔ u ≤ t := by
    simpa only [hfixed] using
      (strictMonoOn_inverseHerbrandFunction (R := B) G).le_iff_le hu ht0
  rw [upperRamificationGroup, lowerRamificationGroupReal_of_common_order G ht]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, hle]

omit [Finite G] [Fact (Nat.card G).Prime] in
/-- Summing the actual common nonidentity orders uses precisely `card G - 1` terms. -/
theorem sum_ramificationOrder_of_common_order [Fintype G] [DecidableEq G] {m : ℕ}
    (hm : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g = m) :
    (∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g) =
      (((Nat.card G - 1) * m : ℕ) : ℕ∞) := by
  classical
  have hsum : (∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g) =
      ∑ _g ∈ Finset.univ.erase (1 : G), (m : ℕ∞) := by
    apply Finset.sum_congr rfl
    intro g hg
    exact hm g (Finset.mem_erase.mp hg).1
  rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.cast_mul]


end FontaineWintenberger
