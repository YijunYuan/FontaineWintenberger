/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.NormTower

/-!
# The common integer precision of actual prime-degree norms

The integral break gives the exact trace-ideal precision. Euclidean division
shows that this precision dominates the nonnegative ceiling of `(p-1)b/p`
for every lower bound `b` on the same intrinsic first ramification bound.
-/

@[expose] public section

namespace FontaineWintenberger

/-- The exact prime-step integer precision dominates the real source bound. -/
theorem mul_div_le_prime_norm_precision (p t : ℕ) (hp : 0 < p) :
    ((p - 1 : ℕ) : ℝ) / p * t ≤ (((p - 1) * (t + 1) / p : ℕ) : ℝ) := by
  have hp1 : 1 ≤ p := hp
  let a := (p - 1) * (t + 1)
  have hmod : a % p ≤ p - 1 := by
    have h := Nat.mod_lt a hp
    omega
  have hdiv := Nat.mod_add_div a p
  have hnat : (p - 1) * t ≤ p * (a / p) := by
    dsimp only [a] at hdiv hmod ⊢
    nlinarith
  have hr : (((p - 1) * t : ℕ) : ℝ) ≤ ((p * (a / p) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  calc
    ((p - 1 : ℕ) : ℝ) / p * t = (((p - 1) * t : ℕ) : ℝ) / p := by
      push_cast
      ring
    _ ≤ (((p - 1) * (t + 1) / p : ℕ) : ℝ) := by
      apply (div_le_iff₀ hpR).mpr
      simpa only [a, Nat.cast_mul, mul_comm] using hr

/-- A real lower bound on an integral prime break gives a common integer
precision, including negative lower bounds. -/
theorem ceil_mul_div_le_prime_norm_precision (p t : ℕ) (hp : 0 < p)
    {b : ℝ} (hb : b ≤ t) :
    ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ ≤ (p - 1) * (t + 1) / p := by
  apply Nat.ceil_le.mpr
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans
    (mul_div_le_prime_norm_precision p t hp)

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "S" => spectralIntegerRing K L

/-- Actual prime-degree norm congruence at every common intrinsic lower bound. -/
theorem spectralIntegerRing_prime_norm_add_congruence_of_bound
    (p : ℕ) [Fact p.Prime] (hd : Module.finrank K L = p)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    (b : ℝ) (hb : (b : EReal) ≤ apfRamificationBound K L) (x y : S) :
    Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
      IsLocalRing.maximalIdeal R ^ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  have hp : (Module.finrank K L).Prime := hd ▸ Fact.out
  obtain ⟨t, ht, hcongr⟩ := spectralIntegerRing_prime_degree_norm_add_congruence K L hp he
  have hbt : b ≤ (t : ℝ) := by
    rw [ht] at hb
    exact EReal.coe_le_coe_iff.mp hb
  have hr := ceil_mul_div_le_prime_norm_precision p t (Fact.out : p.Prime).pos hbt
  have hc := hcongr x y
  rw [hd] at hc
  exact Ideal.pow_le_pow_right hr hc

end FontaineWintenberger
