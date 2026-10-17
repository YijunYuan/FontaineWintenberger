/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.TraceIdeal
public import FontaineWintenberger.Ramification.Upper
public import FontaineWintenberger.APF.FiniteBound
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# The common intrinsic order in prime degree

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

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "GL" => L ≃ₐ[K] L

/-- Total ramification makes the actual full Galois action inertial. -/
theorem spectralIntegerRing_lower_zero_eq_top_of_totallyRamified
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L) :
    lowerRamificationGroup GL (IsLocalRing.maximalIdeal OL) 0 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [spectralIntegerRing_card_lower_zero K L, he, IsGalois.card_aut_eq_finrank K L]

/-- The common break is produced from prime field degree and total ramification. -/
theorem spectralIntegerRing_exists_common_break_of_prime_degree
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L) :
    ∃ t : ℕ, ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ) := by
  have : Fact (Nat.card GL).Prime := ⟨by rwa [IsGalois.card_aut_eq_finrank K L]⟩
  exact exists_common_ramificationOrder_succ_of_prime_card GL
    (spectralIntegerRing_lower_zero_eq_top_of_totallyRamified K L he)

/-- Hilbert's actual different formula specializes to the common-order formula. -/
theorem spectralIntegerRing_different_order_of_common_order {m : ℕ}
    (hm : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = m) :
    emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal OK OL) =
      (((Module.finrank K L - 1) * m : ℕ) : ℕ∞) := by
  classical
  rw [spectralIntegerRing_different_order_eq_sum_ramificationOrder K L,
    sum_ramificationOrder_of_common_order GL hm, IsGalois.card_aut_eq_finrank K L]

/-- The actual public extended APF bound is the common upper break. -/
theorem apfRamificationBound_eq_common_break [Nontrivial GL] {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ)) :
    apfRamificationBound K L = ((t : ℝ) : EReal) := by
  have ht0 : (-1 : ℝ) ≤ t := by have := Nat.cast_nonneg (α := ℝ) t; linarith
  rw [apfRamificationBound_eq_sSup_finite_upper K L]
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨u, hu, hg, rfl⟩
    have hut : u ≤ t := by
      by_contra h
      rw [upperRamificationGroup_of_common_order GL ht hu, ite_eq_right h] at hg
      exact bot_ne_top hg
    exact EReal.coe_le_coe_iff.mpr hut
  · apply le_sSup
    exact ⟨t, ht0, by rw [upperRamificationGroup_of_common_order GL ht ht0, ite_eq_left le_rfl],
        rfl⟩

/-- The actual trace ideal at a common break, with its exact floor exponent. -/
theorem spectralIntegerRing_intTraceIdeal_of_common_break {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ))
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L) :
    intTraceIdeal OK OL ⊤ = IsLocalRing.maximalIdeal OK ^
      (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) := by
  have h := intTraceIdeal_pow OK OL K L 0
  simpa only [pow_zero, Ideal.one_eq_top, spectralIntegerRing_different_order_of_common_order K L
      ht,
    ENat.toNat_natCast, Nat.add_zero, he] using h

private theorem trace_exponent_mul_le (p t : ℕ) (hp : 0 < p) :
    (p - 1) * t ≤ p * (((p - 1) * (t + 1)) / p) := by
  have hmod := Nat.mod_lt ((p - 1) * (t + 1)) hp
  have hdiv := Nat.mod_add_div ((p - 1) * (t + 1)) p
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel hp
  nlinarith

/-- The trace bound in normalized additive valuation, after clearing its
positive denominator. This includes zero traces with infinite valuation. -/
theorem spectralIntegerRing_intTrace_order_bound {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ))
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L)
    (x : OL) :
    (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
      (Module.finrank K L : ℕ∞) *
        IsDiscreteValuationRing.addVal OK (Algebra.intTrace OK OL x) := by
  have hmem : Algebra.intTrace OK OL x ∈ IsLocalRing.maximalIdeal OK ^
      (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) := by
    apply (intTraceIdeal_le_iff OK OL ⊤ _).mp
      (spectralIntegerRing_intTraceIdeal_of_common_break K L ht he).le x
    trivial
  have hval := (mem_maximalIdeal_pow_iff_addVal _ _).mp hmem
  have harith := trace_exponent_mul_le (Module.finrank K L) t (Module.finrank_pos (R := K) (M := L))
  exact (show (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
      (Module.finrank K L : ℕ∞) *
        (((Module.finrank K L - 1) * (t + 1) / Module.finrank K L : ℕ) : ℕ∞) by
      exact_mod_cast harith).trans (by gcongr)

/-- Prime degree and total ramification produce the actual break, public APF
bound, different, trace ideal, and trace valuation estimate together. -/
theorem spectralIntegerRing_prime_degree_ramification
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L) :
    ∃ t : ℕ,
      (∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ)) ∧
      apfRamificationBound K L = ((t : ℝ) : EReal) ∧
      emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal OK OL) =
        (((Module.finrank K L - 1) * (t + 1) : ℕ) : ℕ∞) ∧
      intTraceIdeal OK OL ⊤ = IsLocalRing.maximalIdeal OK ^
        (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) ∧
      ∀ x : OL, (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
        (Module.finrank K L : ℕ∞) *
          IsDiscreteValuationRing.addVal OK (Algebra.intTrace OK OL x) := by
  have : Nontrivial GL := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [IsGalois.card_aut_eq_finrank K L] using hp.one_lt)
  obtain ⟨t, ht⟩ := spectralIntegerRing_exists_common_break_of_prime_degree K L hp he
  exact ⟨t, ht, apfRamificationBound_eq_common_break K L ht,
    spectralIntegerRing_different_order_of_common_order K L ht,
    spectralIntegerRing_intTraceIdeal_of_common_break K L ht he,
    spectralIntegerRing_intTrace_order_bound K L ht he⟩

end Spectral

end FontaineWintenberger
