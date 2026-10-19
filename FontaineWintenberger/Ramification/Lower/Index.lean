/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The canonical ramification index and normalized integral valuations

We identify Mathlib's local-length ramification index with the exponent of the
mapped maximal ideal, then obtain the normalized valuation scaling formula.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]

local notation "mR" => IsLocalRing.maximalIdeal R
local notation "mS" => IsLocalRing.maximalIdeal S

private theorem ramificationIdx_eq_exponent {e : ℕ}
    (he : (mR).map (algebraMap R S) = mS ^ e) : (mS).ramificationIdx R = e := by
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx mR mS (maximalIdeal R).ne_bot]
  apply Ideal.ramificationIdx'_spec he.le
  intro hle
  obtain ⟨π, hπ⟩ := exists_irreducible S
  have hmem : π ^ e ∈ mS ^ e := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.subset_span (by simp)
  have hval := (mem_maximalIdeal_pow_iff_addVal (π ^ e) (e + 1)).mp
    (hle (he.symm ▸ hmem))
  rw [hπ.addVal_pow] at hval
  have : e + 1 ≤ e := by exact_mod_cast hval
  omega

/-- A mapped uniformizer has a unit-times-uniformizer-power factorization of canonical index. -/
theorem exists_uniformizer_factor_ramificationIdx {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ π : S, Irreducible π ∧ ∃ u : Sˣ,
      algebraMap R S ϖ = u * π ^ (mS).ramificationIdx R := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  have hϖ0 : algebraMap R S ϖ ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R S).ne hϖ.ne_zero
  obtain ⟨e, u, he⟩ := eq_unit_mul_pow_irreducible hϖ0 hπ
  have hmap : (mR).map (algebraMap R S) = mS ^ e := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hπ.maximalIdeal_eq]
  rw [ramificationIdx_eq_exponent R S hmap]
  exact ⟨π, hπ, u, he⟩

/-- The exponent of the mapped maximal ideal is Mathlib's canonical local-length index. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx :
    (mR).map (algebraMap R S) = mS ^ (mS).ramificationIdx R := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨π, hπ, u, he⟩ := exists_uniformizer_factor_ramificationIdx R S hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
    Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq]

theorem local_ramificationIdx_pos : 0 < (mS).ramificationIdx R := by
  apply Nat.pos_of_ne_zero
  intro he
  have hproper := IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
  rw [map_maximalIdeal_eq_pow_ramificationIdx R S, he, pow_zero] at hproper
  simp only [Ideal.one_eq_top, lt_self_iff_false] at hproper

theorem ramificationIdx_eq_addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    ((mS).ramificationIdx R : ℕ∞) = addVal S (algebraMap R S ϖ) := by
  obtain ⟨π, hπ, u, he⟩ := exists_uniformizer_factor_ramificationIdx R S hϖ
  rw [he, addVal_def' u hπ]

/-- Normalized integral valuations scale by the canonical ramification index, including at zero. -/
theorem addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = ((mS).ramificationIdx R : ℕ∞) * addVal R x := by
  by_cases hx : x = 0
  · have he : ((mS).ramificationIdx R : ℕ∞) ≠ 0 := by
      exact_mod_cast (local_ramificationIdx_pos R S).ne'
    simp [hx, he]
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, hx⟩ := eq_unit_mul_pow_irreducible hx hϖ
    have hu : addVal S (algebraMap R S (u : R)) = 0 :=
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S))
    rw [hx, addVal_def' u hϖ, map_mul, map_pow, addVal_mul, hu, zero_add,
      addVal_pow, ← ramificationIdx_eq_addVal_uniformizer R S hϖ, nsmul_eq_mul, mul_comm]

end FontaineWintenberger
