/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Norm.Tower

/-!
# Norm differences at the Herbrand precision

Controlled trace representatives and the different compute the
prime-step modulus of continuity of the integral norm.

## Main results

* `ceil_prime_herbrand_piece_le_precision`: Euclidean division bounds the prime-step Herbrand piece
  by the integer norm and trace precisions simultaneously.
* `exists_spectralIntegerRing_prime_norm_sub_precision`: The prime-step norm-difference precision is
  the minimum of the norm precision and the trace ideal of the controlled error.
* `spectralIntegerRing_prime_norm_sub_congruence`: The integral norm in a totally ramified Galois
  prime step has the intrinsic Herbrand modulus of continuity.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- Euclidean division bounds the prime-step Herbrand piece by the
integer norm and trace precisions simultaneously. -/
theorem ceil_prime_herbrand_piece_le_precision (p t r : ℕ) (hp : 0 < p) :
    ⌈if (r : ℝ) ≤ t then (r : ℝ) else (t : ℝ) + ((r : ℝ) - t) / p⌉₊ ≤
      min r (((p - 1) * (t + 1) + r) / p) := by
  have hp1 : 1 ≤ p := hp
  have hpm : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  apply le_min
  · apply Nat.ceil_le.mpr
    split_ifs with h
    · exact le_rfl
    · have ht : (t : ℝ) < r := lt_of_not_ge h
      have hpR1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      have hdiv : ((r : ℝ) - t) / p ≤ (r : ℝ) - t :=
        div_le_self (by linarith) hpR1
      linarith
  · apply Nat.ceil_le.mpr
    have hmod := Nat.mod_lt ((p - 1) * (t + 1) + r) hp
    have hdiv := Nat.mod_add_div ((p - 1) * (t + 1) + r) p
    have hnat : (p - 1) * t + r ≤ p * (((p - 1) * (t + 1) + r) / p) := by
      nlinarith
    have hreal : (((p - 1) * t + r : ℕ) : ℝ) ≤
        ((p * (((p - 1) * (t + 1) + r) / p) : ℕ) : ℝ) := by exact_mod_cast hnat
    split_ifs with h
    · have hrt : r ≤ t := by exact_mod_cast h
      have hrnat : p * r ≤ (p - 1) * t + r := by nlinarith
      exact_mod_cast (Nat.le_div_iff_mul_le hp).mpr (by nlinarith : r * p ≤
        (p - 1) * (t + 1) + r)
    · push_cast at hreal
      have hpmR : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hpm
      have heq : (t : ℝ) + ((r : ℝ) - t) / p =
          (((p - 1 : ℕ) : ℝ) * t + r) / p := by
        field_simp
        nlinarith
      rw [heq]
      exact (div_le_iff₀ hpR).mpr (by nlinarith [hreal])

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "S" => spectralIntegerRing K L

attribute [local instance] FractionRing.liftAlgebra

/-- The prime-step norm-difference precision is the minimum of the
norm precision and the trace ideal of the controlled error. -/
theorem exists_spectralIntegerRing_prime_norm_sub_precision
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ t : ℕ, apfRamificationBound K L = ((t : ℝ) : EReal) ∧
      (emultiplicity (IsLocalRing.maximalIdeal S) (differentIdeal 𝒪[K] S)).toNat =
        (Module.finrank K L - 1) * (t + 1) ∧
      ∀ (r : ℕ) (x y : S), x - y ∈ IsLocalRing.maximalIdeal S ^ r →
        Algebra.intNorm 𝒪[K] S x - Algebra.intNorm 𝒪[K] S y ∈
          IsLocalRing.maximalIdeal 𝒪[K] ^
            min r (((Module.finrank K L - 1) * (t + 1) + r) / Module.finrank K L) := by
  obtain ⟨t, _, hbound, hd, _, _⟩ := spectralIntegerRing_prime_degree_ramification K L hp he
  have hd' : (emultiplicity (IsLocalRing.maximalIdeal S) (differentIdeal 𝒪[K] S)).toNat =
      (Module.finrank K L - 1) * (t + 1) := by rw [hd]; rfl
  refine ⟨t, hbound, hd', fun r x y hxy => ?_⟩
  have : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing S) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv 𝒪[K] K).symm (FractionRing.algEquiv S L).symm y
  have hn := intNorm_mem_maximalIdeal_pow 𝒪[K] S hxy
  have ht := spectralIntegerRing_intNorm_sub_sub_mem_intTraceIdeal_pow K L hp r x y hxy
  rw [intTraceIdeal_pow 𝒪[K] S K L r, he, hd'] at ht
  have hn' := Ideal.pow_le_pow_right (min_le_left r
    (((Module.finrank K L - 1) * (t + 1) + r) / Module.finrank K L)) hn
  have ht' := Ideal.pow_le_pow_right (min_le_right r
    (((Module.finrank K L - 1) * (t + 1) + r) / Module.finrank K L)) ht
  simpa only [sub_add_cancel] using (IsLocalRing.maximalIdeal 𝒪[K] ^
    min r (((Module.finrank K L - 1) * (t + 1) + r) / Module.finrank K L)).add_mem ht' hn'

/-- The integral norm in a totally ramified Galois prime step
has the intrinsic Herbrand modulus of continuity. -/
theorem spectralIntegerRing_prime_norm_sub_congruence
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx 𝒪[K] = Module.finrank K L)
    (r : ℕ) (x y : S) (hxy : x - y ∈ IsLocalRing.maximalIdeal S ^ r) :
    Algebra.intNorm 𝒪[K] S x - Algebra.intNorm 𝒪[K] S y ∈
      IsLocalRing.maximalIdeal 𝒪[K] ^ ⌈apfPhi K L (r : ℝ)⌉₊ := by
  obtain ⟨t, _hbound, hd, hprecision⟩ :=
    exists_spectralIntegerRing_prime_norm_sub_precision K L hp he
  obtain ⟨b, _hb, _hidx, _hpsi, hphi, hdiff⟩ := apf_prime_degree_different_profile K L hp he
  have hbt : b = (t : ℝ) := by
    rw [hd, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
      Nat.cast_add, Nat.cast_one] at hdiff
    have hn : (2 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hp.two_le
    nlinarith
  rw [hbt] at hphi
  have hle := ceil_prime_herbrand_piece_le_precision (Module.finrank K L) t r hp.pos
  rw [← hphi r] at hle
  exact Ideal.pow_le_pow_right hle (hprecision r x y hxy)

end FontaineWintenberger
