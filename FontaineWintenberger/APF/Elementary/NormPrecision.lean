/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Norm.Tower
public import FontaineWintenberger.APF.Elementary.PrimeDegree

/-!
# Norm precision in prime degree

## Finite-precision norm congruences in towers

The normalized norm valuation preserves every nonnegative precision.
An addition congruence consequently respects input congruence and
composes through a finite tower by transitivity of integral norms.

## The common integer precision of prime-degree norms

The integral break gives the exact trace-ideal precision. Euclidean division
shows that this precision dominates the nonnegative ceiling of `(p-1)b/p`
for every lower bound `b` on the same intrinsic first ramification bound.

## Main results

* `spectralIntegerRing_prime_degree_norm_add_congruence`: A prime-degree producer supplies the
  ideal-power addition congruence used in the tower step, at the exact trace-ideal precision.
* `mul_div_le_prime_norm_precision`: The exact prime-step integer precision dominates the real
  source bound.
* `ceil_mul_div_le_prime_norm_precision`: A real lower bound on an integral prime break gives a
  common integer precision, including negative lower bounds.
* `spectralIntegerRing_prime_norm_add_congruence_of_bound`: Prime-degree norm congruence at every
  common intrinsic lower bound.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

attribute [local instance] FractionRing.liftAlgebra

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable [PerfectField 𝓀[K]]

local notation "OL" => spectralIntegerRing K L

/-- A prime-degree producer supplies the ideal-power addition
congruence used in the tower step, at the exact trace-ideal precision. -/
theorem spectralIntegerRing_prime_degree_norm_add_congruence
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ t : ℕ, apfRamificationBound K L = ((t : ℝ) : EReal) ∧
      ∀ α β : OL,
        Algebra.intNorm 𝒪[K] OL (α + β) - Algebra.intNorm 𝒪[K] OL α - Algebra.intNorm 𝒪[K] OL β ∈
          IsLocalRing.maximalIdeal 𝒪[K] ^
            (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) := by
  obtain ⟨t, _ht, hbound, _hdiff, htrace, _hval⟩ :=
    spectralIntegerRing_prime_degree_ramification K L hp he
  refine ⟨t, hbound, fun α β => ?_⟩
  rw [← htrace]
  exact spectralIntegerRing_intNorm_add_sub_mem_intTraceIdeal K L hp α β

end Spectral

end FontaineWintenberger

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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField 𝓀[K]]

local notation "S" => spectralIntegerRing K L

/-- Prime-degree norm congruence at every common intrinsic lower bound. -/
theorem spectralIntegerRing_prime_norm_add_congruence_of_bound
    (p : ℕ) [Fact p.Prime] (hd : Module.finrank K L = p)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx 𝒪[K] = Module.finrank K L)
    (b : ℝ) (hb : (b : EReal) ≤ apfRamificationBound K L) (x y : S) :
    Algebra.intNorm 𝒪[K] S (x + y) - Algebra.intNorm 𝒪[K] S x - Algebra.intNorm 𝒪[K] S y ∈
      IsLocalRing.maximalIdeal 𝒪[K] ^ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
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
