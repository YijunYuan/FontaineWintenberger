/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Norm.Congruence
public import FontaineWintenberger.Ramification.Norm.Valuation

/-!
# Finite-precision norm congruences in towers

The normalized norm valuation preserves every nonnegative precision.
An addition congruence consequently respects input congruence and
composes through a finite tower by transitivity of integral norms.
-/

@[expose] public section

namespace FontaineWintenberger

attribute [local instance] FractionRing.liftAlgebra

section LocalRings

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- Integral norms preserve any fixed nonnegative ideal-power precision. -/
theorem intNorm_mem_maximalIdeal_pow {r : ℕ} {x : S}
    (hx : x ∈ IsLocalRing.maximalIdeal S ^ r) :
    Algebra.intNorm R S x ∈ IsLocalRing.maximalIdeal R ^ r := by
  rw [mem_maximalIdeal_pow_iff_addVal, addVal_intNorm R S]
  have hv := (mem_maximalIdeal_pow_iff_addVal x r).mp hx
  have hf : (1 : ℕ∞) ≤ ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℕ∞) := by
    exact_mod_cast (Ideal.inertiaDeg_pos (IsLocalRing.maximalIdeal S) R)
  apply hv.trans
  calc
    IsDiscreteValuationRing.addVal S x = 1 * IsDiscreteValuationRing.addVal S x := (one_mul _).symm
    _ ≤ ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℕ∞) *
      IsDiscreteValuationRing.addVal S x := by gcongr

/-- A proved addition congruence for the norm makes it respect
the same input precision. -/
theorem intNorm_sub_mem_maximalIdeal_pow_of_add_congruence {r : ℕ}
    (hadd : ∀ x y : S,
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r)
    {x y : S} (hxy : x - y ∈ IsLocalRing.maximalIdeal S ^ r) :
    Algebra.intNorm R S x - Algebra.intNorm R S y ∈ IsLocalRing.maximalIdeal R ^ r := by
  have hn := intNorm_mem_maximalIdeal_pow R S hxy
  have he := hadd y (x - y)
  have hsum := (IsLocalRing.maximalIdeal R ^ r).add_mem he hn
  have hidentity : y + (x - y) = x := by ring
  rw [hidentity] at hsum
  simpa only [sub_add_cancel] using hsum

variable (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [FaithfulSMul S T] [IsLocalHom (algebraMap S T)] [Module.Finite S T]

omit [IsLocalHom (algebraMap S T)] in
/-- The tower step composes norm addition congruences at a
common precision; the conclusions for the steps are supplied by their producers. -/
theorem intNorm_add_congruence_tower {r : ℕ}
    (hRS : ∀ x y : S,
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r)
    (hST : ∀ x y : T,
      Algebra.intNorm S T (x + y) - Algebra.intNorm S T x - Algebra.intNorm S T y ∈
        IsLocalRing.maximalIdeal S ^ r)
    (x y : T) :
    letI : Module.Finite R T := Module.Finite.trans S T
    letI : FaithfulSMul R T := FaithfulSMul.trans R S T
    Algebra.intNorm R T (x + y) - Algebra.intNorm R T x - Algebra.intNorm R T y ∈
      IsLocalRing.maximalIdeal R ^ r := by
  let := Module.Finite.trans (R := R) S T
  let := FaithfulSMul.trans R S T
  have htop : Algebra.intNorm S T (x + y) -
      (Algebra.intNorm S T x + Algebra.intNorm S T y) ∈ IsLocalRing.maximalIdeal S ^ r := by
    simpa only [sub_sub] using hST x y
  have hres := intNorm_sub_mem_maximalIdeal_pow_of_add_congruence R S hRS htop
  have hbottom := hRS (Algebra.intNorm S T x) (Algebra.intNorm S T y)
  have hsum := (IsLocalRing.maximalIdeal R ^ r).add_mem hres hbottom
  have heq : Algebra.intNorm R S (Algebra.intNorm S T (x + y)) -
      Algebra.intNorm R S (Algebra.intNorm S T x + Algebra.intNorm S T y) +
      (Algebra.intNorm R S (Algebra.intNorm S T x + Algebra.intNorm S T y) -
        Algebra.intNorm R S (Algebra.intNorm S T x) -
        Algebra.intNorm R S (Algebra.intNorm S T y)) =
      Algebra.intNorm R T (x + y) - Algebra.intNorm R T x - Algebra.intNorm R T y := by
    rw [Algebra.intNorm_intNorm, Algebra.intNorm_intNorm, Algebra.intNorm_intNorm]
    ring
  rwa [heq] at hsum

end LocalRings

end FontaineWintenberger
