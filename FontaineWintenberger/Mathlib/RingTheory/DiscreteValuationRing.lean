/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Uniformizers detected by the normalized valuation

In a discrete valuation ring `A ⊆ F`, an element of normalized valuation `exp (-1)` is a
uniformizer.

Upstream candidate: `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

theorem irreducible_of_valuation_eq_exp_neg_one
    {F : Type*} [Field F] (A : ValuationSubring F) [IsDiscreteValuationRing A]
    (z : A) (hz : (maximalIdeal A).valuation F (z : F) = WithZero.exp (-1 : ℤ)) :
    Irreducible z := by
  have hne : z ≠ 0 := by
    intro h
    rw [h, ZeroMemClass.coe_zero, map_zero] at hz
    exact WithZero.exp_ne_zero hz.symm
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, heq⟩ := eq_unit_mul_pow_irreducible hne hϖ
  have hv := hz
  change (maximalIdeal A).valuation F (algebraMap A F z) = _ at hv
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_maximalIdeal, heq, addVal_def' u hϖ,
    ENat.recTopCoe_natCast] at hv
  have hn : n = 1 := by
    have hi := WithZero.exp_injective hv
    change -(n : ℤ) = -1 at hi
    omega
  rw [heq, hn, pow_one]
  exact (show Associated ϖ (↑u * ϖ) from ⟨u, mul_comm _ _⟩).irreducible hϖ

end IsDiscreteValuationRing
