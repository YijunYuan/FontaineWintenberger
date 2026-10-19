/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Different.Monogenic
public import FontaineWintenberger.Ramification.Lower.Inertia

/-!
# Counting the lower groups in the different formula

The intrinsic sum over nonidentity automorphisms equals the finite sum of
lower-group cardinalities minus one. The bound is obtained from the
eventual triviality theorem for a finite faithful action.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing IsLocalRing

private theorem enat_eq_sum_range_indicator {a : ℕ∞} {N : ℕ} (ha : a ≤ N) :
    a = ∑ n ∈ Finset.range N, if (n : ℕ∞) + 1 ≤ a then 1 else 0 := by
  have hfinite : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hk : k ≤ N := by exact_mod_cast ha
  have hfilter : (Finset.range N).filter (fun n : ℕ => (n : ℕ∞) + 1 ≤ (k : ℕ∞)) =
      Finset.range k := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    norm_cast
    omega
  rw [← Finset.sum_filter, hfilter]
  simp

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type*) [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G B]

/-- Double-counting the nonidentity lower-group elements, for any
bound on the intrinsic nonidentity orders. -/
theorem sum_ramificationOrder_eq_sum_lower_card {N : ℕ}
    (hN : ∀ g : G, g ≠ 1 → ramificationOrder (R := B) G g ≤ N) :
    (∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g) =
      ∑ n ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (maximalIdeal B) n) - 1 : ℕ) : ℕ∞) := by
  classical
  calc
    (∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g) =
        ∑ g ∈ Finset.univ.erase (1 : G), ∑ n ∈ Finset.range N,
        if (n : ℕ∞) + 1 ≤ ramificationOrder (R := B) G g then (1 : ℕ∞) else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      exact enat_eq_sum_range_indicator (hN g (Finset.mem_erase.mp hg).1)
    _ = ∑ n ∈ Finset.range N, ∑ g ∈ Finset.univ.erase (1 : G),
        if (n : ℕ∞) + 1 ≤ ramificationOrder (R := B) G g then (1 : ℕ∞) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      have hmem (g : G) : (n : ℕ∞) + 1 ≤ ramificationOrder (R := B) G g ↔
          g ∈ lowerRamificationGroup G (maximalIdeal B) n := by
        simpa using (mem_lowerRamificationGroup_iff_le_order (R := B) G (n : ℤ) g).symm
      simp only [hmem, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hfilter : ((Finset.univ.erase (1 : G)).filter
          (fun g => g ∈ lowerRamificationGroup G (maximalIdeal B) n)) =
          (Finset.univ.filter (fun g => g ∈ lowerRamificationGroup G (maximalIdeal B) n)).erase 1 :=
              by
        ext g
        simp
      rw [hfilter, Finset.card_erase_of_mem (by simp)]
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Eventual triviality supplies a cutoff for the cardinal sum. -/
theorem exists_sum_ramificationOrder_eq_sum_lower_card [FaithfulSMul G B] :
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → lowerRamificationGroup G (maximalIdeal B) n = ⊥) ∧
      (∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g) =
        ∑ n ∈ Finset.range N,
          ((Nat.card (lowerRamificationGroup G (maximalIdeal B) n) - 1 : ℕ) : ℕ∞) := by
  classical
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := B) G
  refine ⟨N, hN, sum_ramificationOrder_eq_sum_lower_card G (fun g hg => ?_)⟩
  have hnot : g ∉ lowerRamificationGroup G (maximalIdeal B) (N : ℤ) := by
    rw [hN N le_rfl, Subgroup.mem_bot]
    exact hg
  have hfinite : ramificationOrder (R := B) G g ≠ ⊤ :=
    (ramificationOrder_eq_top_iff G g).not.mpr hg
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hlt : (k : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by
    simpa [mem_lowerRamificationGroup_iff_le_order, ← hk] using hnot
  have hn : k < N + 1 := by exact_mod_cast hlt
  rw [← hk]
  exact_mod_cast (show k ≤ N by omega)

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable [PerfectField (ResidueField
  (Valuation.valuationSubring (NormedField.valuation (K := K))))]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "G₀" => L ≃ₐ[K] L

/-- Hilbert's nonidentity-order formula for the different and full
Galois group; the integral generator is proved to exist. -/
theorem spectralIntegerRing_different_order_eq_sum_ramificationOrder [DecidableEq G₀] :
    emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal OK OL) =
      ∑ g ∈ Finset.univ.erase (1 : G₀), ramificationOrder (R := OL) G₀ g := by
  classical
  obtain ⟨θ, hθ⟩ := spectralIntegerRing_exists_generator K L
  exact differentIdeal_order_eq_sum_ramificationOrder OK OL K L G₀ hθ

/-- Hilbert's cardinal formula with a finite cutoff, beyond which all
lower groups are trivial. -/
theorem spectralIntegerRing_different_order_eq_sum_lower_card :
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal OL) n = ⊥) ∧
      emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal OK OL) =
        ∑ n ∈ Finset.range N,
          ((Nat.card (lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal OL) n) - 1 : ℕ) : ℕ∞) :=
              by
  classical
  obtain ⟨N, hN, hsum⟩ := exists_sum_ramificationOrder_eq_sum_lower_card (B := OL) G₀
  exact ⟨N, hN, (spectralIntegerRing_different_order_eq_sum_ramificationOrder K L).trans hsum⟩

end Spectral

end FontaineWintenberger
