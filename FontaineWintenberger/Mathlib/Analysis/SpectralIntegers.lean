/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Ring.Subring.IntPolynomial
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Integral elements and the spectral valuation

The spectral unit ball of an algebraic extension is the integral closure of the
base unit ball. Completeness makes the spectral norm multiplicative, yielding
an intrinsic valuation subring invariant under the full automorphism group.
No finite residue-field hypothesis is used.

## Main definitions

* `spectralValuation`: The valuation of an algebraic extension supplied by the spectral norm.
* `spectralIntegerRing`: The intrinsic valuation ring of the extended spectral valuation.

## Main results

* `isIntegral_iff_spectralNorm_le_one`: The spectral unit ball is the integral closure of the base
  unit ball.
* `smul_spectralIntegerRing`: The full algebra automorphism group preserves the spectral valuation
  ring.

## Notation

The local notation `OK` denotes the valuation ring of the norm on `K`.
-/

@[expose] public section

namespace FontaineWintenberger

open Polynomial

section IntegralCriterion

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The spectral unit ball is the integral closure of the base unit ball. -/
theorem isIntegral_iff_spectralNorm_le_one (x : L) :
    IsIntegral OK x ↔ spectralNorm K L x ≤ 1 := by
  let : IsIntegrallyClosed OK :=
    (Valuation.valuationSubring.integers (NormedField.valuation (K := K))).isIntegrallyClosed
  have hm : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  rw [spectralNorm, spectralValue_le_one_iff hm]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map]
    have h := ((minpoly OK x).coeff n).property
    exact_mod_cast h
  · intro hx
    have hp : ∀ n : ℕ, (minpoly K x).coeff n ∈ (OK).toSubring := by
      intro n
      exact_mod_cast hx n
    refine ⟨(minpoly K x).int (OK).toSubring hp, (int_monic_iff _ _ _).mpr hm, ?_⟩
    exact (int_eval₂_eq (OK).toSubring (minpoly K x) hp x).trans (minpoly.aeval K x)

end IntegralCriterion

section SpectralValuation

open scoped NNReal

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The valuation of an algebraic extension supplied by the spectral norm. -/
noncomputable def spectralValuation : Valuation L ℝ≥0 where
  toFun x := ⟨spectralNorm K L x, spectralNorm_nonneg x⟩
  map_zero' := Subtype.ext spectralNorm_zero
  map_one' := Subtype.ext spectralNorm_one
  map_mul' x y := Subtype.ext (spectralAlgNorm_mul x y)
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

@[simp]
theorem spectralValuation_algebraMap (x : K) :
    spectralValuation K L (algebraMap K L x) = ‖x‖₊ :=
  Subtype.ext (spectralNorm_extends x)

instance spectralValuation_hasExtension :
    (NormedField.valuation (K := K)).HasExtension (spectralValuation K L) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, spectralValuation_algebraMap,
      NormedField.valuation_apply]

/-- The intrinsic valuation ring of the extended spectral valuation. -/
noncomputable abbrev spectralIntegerRing : ValuationSubring L :=
  (spectralValuation K L).valuationSubring

@[simp]
theorem mem_spectralIntegerRing (x : L) :
    x ∈ spectralIntegerRing K L ↔ spectralNorm K L x ≤ 1 :=
  Iff.rfl

theorem spectralIntegerRing_eq_integralClosure :
    (spectralIntegerRing K L).toSubring =
      (integralClosure (NormedField.valuation (K := K)).valuationSubring L).toSubring := by
  ext x
  exact (mem_spectralIntegerRing K L x).trans (isIntegral_iff_spectralNorm_le_one K x).symm

instance spectralIntegerRing_isIntegralClosure :
    IsIntegralClosure (spectralIntegerRing K L)
      (NormedField.valuation (K := K)).valuationSubring L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [isIntegral_iff_spectralNorm_le_one, ← mem_spectralIntegerRing]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

open scoped Pointwise

/-- The full algebra automorphism group preserves the spectral valuation ring. -/
theorem smul_spectralIntegerRing (g : L ≃ₐ[K] L) :
    g • spectralIntegerRing K L = spectralIntegerRing K L := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_spectralIntegerRing, mem_spectralIntegerRing]
  change spectralNorm K L (g⁻¹ x) ≤ 1 ↔ spectralNorm K L x ≤ 1
  rw [← spectralNorm_eq_of_equiv g⁻¹ x]

theorem spectralIntegerRing_decompositionSubgroup :
    (spectralIntegerRing K L).decompositionSubgroup K = ⊤ := by
  apply top_unique
  intro g _
  exact smul_spectralIntegerRing K L g

end SpectralValuation

end FontaineWintenberger
