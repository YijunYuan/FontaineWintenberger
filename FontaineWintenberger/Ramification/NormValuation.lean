/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Degree
public import FontaineWintenberger.Ramification.Tower
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Normalized valuations of algebraic norms

The relative norm of the actual maximal ideal gives normalized norm
valuations without a normality or finite residue-field assumption.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing

attribute [local instance] FractionRing.liftAlgebra

section LocalRings

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

local notation "mR" => IsLocalRing.maximalIdeal R
local notation "mS" => IsLocalRing.maximalIdeal S

/-- The norm of an actual integral uniformizer has valuation equal to the
canonical residue degree. -/
theorem addVal_intNorm_uniformizer {π : S} (hπ : Irreducible π) :
    addVal R (Algebra.intNorm R S π) = ((mS).inertiaDeg R : ℕ∞) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  have hspan : Ideal.span {Algebra.intNorm R S π} =
      Ideal.span {ϖ ^ (mS).inertiaDeg R} := by
    rw [← Ideal.relNorm_singleton, ← hπ.maximalIdeal_eq,
      Ideal.relNorm_eq_pow_of_isMaximal mS mR, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow]
  exact ((addVal_eq_iff_associated _ _).mpr
    (Ideal.span_singleton_eq_span_singleton.mp hspan)).trans (hϖ.addVal_pow _)

/-- Normalized integral norm valuations multiply by the actual residue degree,
including zero. -/
theorem addVal_intNorm (x : S) :
    addVal R (Algebra.intNorm R S x) = ((mS).inertiaDeg R : ℕ∞) * addVal S x := by
  by_cases hx : x = 0
  · have hf : (mS).inertiaDeg R ≠ 0 := (Ideal.inertiaDeg_pos mS R).ne'
    simp [hx, hf]
  · obtain ⟨π, hπ⟩ := exists_irreducible S
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    have hu : addVal R (Algebra.intNorm R S (u : S)) = 0 :=
      addVal_eq_zero_iff.mpr (u.isUnit.map (Algebra.intNorm R S))
    rw [map_mul, map_pow, addVal_mul, hu, zero_add, addVal_pow,
      addVal_intNorm_uniformizer R S hπ, addVal_def' u hπ, nsmul_eq_mul, mul_comm]

/-- The canonical normalized multiplicative valuations satisfy the same norm
identity on the actual integral rings. -/
theorem intValuation_intNorm (x : S) :
    (maximalIdeal R).intValuation (Algebra.intNorm R S x) =
      (maximalIdeal S).intValuation x ^ (mS).inertiaDeg R := by
  have hf : (mS).inertiaDeg R ≠ 0 := (Ideal.inertiaDeg_pos mS R).ne'
  by_cases hx : x = 0
  · simp [hx, hf]
  · obtain ⟨π, hπ⟩ := exists_irreducible S
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    have hu : (maximalIdeal R).intValuation (Algebra.intNorm R S (u : S)) = 1 := by
      rcases (u.isUnit.map (Algebra.intNorm R S)) with ⟨v, hv⟩
      rw [← hv]
      simp [maximalIdeal]
    have hπnorm : (maximalIdeal R).intValuation (Algebra.intNorm R S π) =
        WithZero.exp (-((mS).inertiaDeg R : ℤ)) := by
      rw [intValuation_maximalIdeal, addVal_intNorm_uniformizer R S hπ]
      simp [← WithZero.exp_eq_coe_ofAdd]
    have hπval : (maximalIdeal S).intValuation π = WithZero.exp (-1 : ℤ) :=
      (maximalIdeal S).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
    have huS : (maximalIdeal S).intValuation (u : S) = 1 := by
      simp [maximalIdeal]
    simp only [map_mul, map_pow, hu, huS, one_mul, hπnorm, hπval]
    simp [← WithZero.exp_nsmul, mul_comm]

end LocalRings

section FractionFields

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [IsScalarTower R K L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The normalized valuation of the actual field norm, for arbitrary finite
separable fraction-field extensions of finite local DVR extensions. -/
theorem normalizedValuation_norm (x : L) :
    (maximalIdeal R).valuation K (Algebra.norm K x) =
      ((maximalIdeal S).valuation L x) ^ (IsLocalRing.maximalIdeal S).inertiaDeg R := by
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv R K).symm (FractionRing.algEquiv S L).symm y
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  obtain ⟨b, c, _, rfl⟩ := IsFractionRing.div_surjective S x
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_inv₀,
    ← Algebra.algebraMap_intNorm (A := R) (B := S) (K := K) (L := L),
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_intNorm R S, mul_pow, inv_pow]

end FractionFields

section ChosenExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => Valuation.valuationSubring w

/-- The actual chosen extension valuation ring gives the field norm identity
with the actual residue-field degree. -/
theorem extensionValuationSubring_normalizedValuation_norm (x : L) :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    (maximalIdeal OK).valuation K (Algebra.norm K x) =
      ((maximalIdeal OL).valuation L x) ^
        Module.finrank (IsLocalRing.ResidueField OK) (IsLocalRing.ResidueField OL) := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  rw [← local_inertiaDeg_eq_finrank_residueField OK OL]
  exact normalizedValuation_norm OK OL K L x

/-- Norms preserve normalized valuations when the actual residue degree is one. -/
theorem extensionValuationSubring_normalizedValuation_norm_of_residueDegree_one
    (hf : Module.finrank (IsLocalRing.ResidueField OK) (IsLocalRing.ResidueField OL) = 1)
    (x : L) :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    (maximalIdeal OK).valuation K (Algebra.norm K x) =
      (maximalIdeal OL).valuation L x := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  simpa only [hf, pow_one] using extensionValuationSubring_normalizedValuation_norm K L w x

end ChosenExtension

end FontaineWintenberger
