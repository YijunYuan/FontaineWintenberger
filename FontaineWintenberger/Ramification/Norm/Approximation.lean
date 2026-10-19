/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.ResidueDigits
public import FontaineWintenberger.Ramification.Norm.Valuation

/-!
# Finite-precision approximation by actual norms

An actual totally ramified p-power extension with a norm addition congruence
at a stated precision has norms representing every base element to that
precision. Finite perfect-residue digits supply the actual preimage.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

section LocalRings

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- Residue degree one makes the actual norm of every integral uniformizer
an actual base uniformizer. -/
theorem irreducible_intNorm_of_inertiaDeg_eq_one
    (hf : (IsLocalRing.maximalIdeal S).inertiaDeg R = 1) {π : S} (hπ : Irreducible π) :
    Irreducible (Algebra.intNorm R S π) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  have hv : addVal R (Algebra.intNorm R S π) = addVal R ϖ := by
    rw [addVal_intNorm_uniformizer R S hπ, hf, Nat.cast_one, addVal_uniformizer hϖ]
  exact ((addVal_eq_iff_associated _ _).mp hv).irreducible_iff.mpr hϖ

omit [IsLocalHom (algebraMap R S)]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- Repeated actual norm addition congruences give the same finite-sum congruence. -/
theorem intNorm_sum_sub_sum_intNorm_mem_maximalIdeal_pow {r : ℕ}
    (hadd : ∀ x y : S,
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r)
    {ι : Type*} (s : Finset ι) (f : ι → S) :
    Algebra.intNorm R S (∑ j ∈ s, f j) - (∑ j ∈ s, Algebra.intNorm R S (f j)) ∈
      IsLocalRing.maximalIdeal R ^ r := by
  classical
  let : FiniteDimensional (FractionRing R) (FractionRing S) :=
    .of_isLocalization R S R⁰
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h := (IsLocalRing.maximalIdeal R ^ r).add_mem
      (hadd (f a) (∑ j ∈ s, f j)) ih
    convert h using 1
    ring

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    [PerfectField (IsLocalRing.ResidueField R)]

/-- Finite perfect-residue digits make actual norms surjective modulo any
precision at which their addition congruence has been proved. -/
theorem exists_intNorm_sub_mem_maximalIdeal_pow (n r : ℕ)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank R S)
    (hd : Module.finrank R S = p ^ n)
    (hadd : ∀ x y : S,
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r) (a : R) :
    ∃ α : S, Algebra.intNorm R S α - a ∈ IsLocalRing.maximalIdeal R ^ r := by
  have hf : (IsLocalRing.maximalIdeal S).inertiaDeg R = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (local_ramificationIdx_pos R S)
    simpa only [mul_one, he] using local_ramificationIdx_mul_inertiaDeg R S
  obtain ⟨π', hπ'⟩ := exists_irreducible S
  have hπ := irreducible_intNorm_of_inertiaDeg_eq_one R S hf hπ'
  obtain ⟨b, hb⟩ := exists_pow_digits_sub_mem_maximalIdeal_pow p hπ n r a
  let α : S := ∑ j ∈ Finset.range r, algebraMap R S (b j) * π' ^ j
  have hn := intNorm_sum_sub_sum_intNorm_mem_maximalIdeal_pow R S hadd
    (Finset.range r) (fun j => algebraMap R S (b j) * π' ^ j)
  have hterm (j : ℕ) :
      Algebra.intNorm R S (algebraMap R S (b j) * π' ^ j) =
        b j ^ (p ^ n) * (Algebra.intNorm R S π') ^ j := by
    rw [map_mul, map_pow]
    congr 1
    rw [Algebra.intNorm_eq_norm, Algebra.norm_algebraMap, hd]
  simp_rw [hterm] at hn
  refine ⟨α, ?_⟩
  have h := (IsLocalRing.maximalIdeal R ^ r).add_mem hn
    ((IsLocalRing.maximalIdeal R ^ r).neg_mem hb)
  convert h using 1
  dsimp only [α]
  ring

end LocalRings

section ChosenExtension

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "S" => Valuation.valuationSubring w

/-- Finite-precision norm approximation for the actual chosen extension
integers, with total ramification and p-power degree on the original fields. -/
theorem extensionValuationSubring_exists_intNorm_sub_mem_maximalIdeal_pow (n r : ℕ)
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    (hd : Module.finrank K L = p ^ n) :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    ∀ (_ : ∀ x y : S,
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r) (a : R),
    ∃ α : S, Algebra.intNorm R S α - a ∈ IsLocalRing.maximalIdeal R ^ r := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  intro hadd a
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv R K).symm (FractionRing.algEquiv S L).symm y
  apply exists_intNorm_sub_mem_maximalIdeal_pow R S p n r ?_ ?_ hadd a
  · rwa [← IsFractionRing.finrank_eq R K S L]
  · rw [← IsFractionRing.finrank_eq R K S L]
    exact hd

end ChosenExtension

end FontaineWintenberger
