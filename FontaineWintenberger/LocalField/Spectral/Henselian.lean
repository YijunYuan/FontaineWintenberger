/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.FiniteExtension
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Henselian

/-!
# Completeness and Hensel lifting for discrete valuation rings

The norm topology on the unit ball of a discretely valued normed field agrees
with its maximal-ideal-adic topology. Completeness therefore supplies Hensel
lifting without any restriction on the residue field.

## Main results

* `mem_maximalIdeal_pow_iff_norm`: Powers of the maximal ideal are norm balls of uniformizer-power
  radius.

## References

* Serre, *Local Fields*, Chapters I–II (discrete valuation rings, completions, unramified and
  totally ramified extensions).
-/

@[expose] public section

namespace FontaineWintenberger

section UnitBall

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable [IsDiscreteValuationRing 𝒪[K]]


/-- Powers of the maximal ideal are norm balls of uniformizer-power radius. -/
theorem mem_maximalIdeal_pow_iff_norm (π : 𝒪[K]) (hπ : Irreducible π) (x : 𝒪[K]) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ n ↔ ‖(x : K)‖ ≤ ‖(π : K)‖ ^ n := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := (Valuation.valuationSubring.integers (NormedField.valuation (K := K))).dvd_iff_le
    (x := π ^ n) (y := x)
  simp only [map_pow, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem unitBall_isAdic : IsAdic (IsLocalRing.maximalIdeal 𝒪[K]) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ0 : (π : K) ≠ 0 := by exact_mod_cast hπ.ne_zero
  have hπlt : ‖(π : K)‖ < 1 := by
    have h := (Valuation.mem_maximalIdeal_iff (v := NormedField.valuation (K := K))).mp
      hπ.not_isUnit
    exact_mod_cast h
  have hball (n : ℕ) : (↑(IsLocalRing.maximalIdeal 𝒪[K] ^ n) : Set 𝒪[K]) =
      Metric.closedBall 0 (‖(π : K)‖ ^ n) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact mem_maximalIdeal_pow_iff_norm K π hπ x n
  rw [isAdic_iff]
  constructor
  · intro n
    rw [hball]
    exact IsUltrametricDist.isOpen_closedBall (0 : 𝒪[K])
      (pow_ne_zero n (norm_ne_zero_iff.mpr hπ0))
  · intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπlt
    refine ⟨n, fun x hx => hsub ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact ((mem_maximalIdeal_pow_iff_norm K π hπ x n).mp hx).trans_lt hn

omit [IsDiscreteValuationRing 𝒪[K]] in
theorem unitBall_completeSpace [CompleteSpace K] : CompleteSpace 𝒪[K] := by
  have hclosed : IsClosed (𝒪[K] : Set K) := by
    change IsClosed {x : K | ‖x‖ ≤ 1}
    exact isClosed_le continuous_norm continuous_const
  exact hclosed.completeSpace_coe

instance unitBall_isAdicComplete [CompleteSpace K] :
    IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  have : CompleteSpace 𝒪[K] := unitBall_completeSpace K
  exact (unitBall_isAdic K).isAdicComplete_iff.mpr ⟨this, inferInstance⟩

instance unitBall_henselianLocalRing [CompleteSpace K] : HenselianLocalRing 𝒪[K] where
  is_henselian f hf a₀ hroot hder :=
    HenselianRing.is_henselian f hf a₀ hroot (hder.map (Ideal.Quotient.mk _))

end UnitBall

section FiniteExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]

/-- The valuation ring in a finite separable extension is Henselian. -/
instance spectralIntegerRing_henselianLocalRing :
    HenselianLocalRing (spectralIntegerRing K L) := by
  let : NormedField L := spectralNorm.normedField K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  have : CompleteSpace L := spectralNorm.completeSpace (K := K) (L := L)
  have hval : NormedField.valuation (K := L) = spectralValuation K L := by
    ext x
    rfl
  have : IsDiscreteValuationRing 𝒪[L] := by
    rw [hval]
    exact spectralIntegerRing_isDiscreteValuationRing K L
  exact unitBall_henselianLocalRing L

end FiniteExtension

end FontaineWintenberger
