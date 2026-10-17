/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Integral polynomial discriminants

The existing Sylvester determinant and adjugate give discriminant
base change and integral Bezout identities for monic polynomials.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The signed discriminant is the padded derivative resultant, including
the constant monic polynomial. -/
theorem monic_discr_resultant (f : R[X]) (hf : f.Monic) :
    (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr =
      f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  by_cases h : 0 < f.natDegree
  · simpa [hf.leadingCoeff] using
      (resultant_deriv (natDegree_pos_iff_degree_pos.mp h)).symm
  · have he : f = 1 := eq_one_of_monic_natDegree_zero hf (Nat.eq_zero_of_not_pos h)
    subst f
    have hd : discr (1 : R[X]) = 1 := by simpa only [C_1] using discr_C (1 : R)
    simp [hd]

/-- Monic polynomial discriminants commute with arbitrary coefficient maps,
including maps to rings with zero divisors. -/
theorem monic_discr_map (f : R[X]) (hf : f.Monic) (φ : R →+* S) :
    (f.map φ).discr = φ f.discr := by
  nontriviality S
  have h := congrArg φ (monic_discr_resultant f hf)
  have h' := monic_discr_resultant (f.map φ) (hf.map φ)
  simp only [map_mul, map_pow, map_neg, map_one] at h
  rw [← resultant_map_map, ← derivative_map] at h
  rw [hf.natDegree_map φ] at h'
  exact (isUnit_neg_one.pow _).mul_left_cancel (h'.trans h.symm)

/-- The actual Sylvester adjugate produces integral coefficients for the
discriminant Bezout identity; no division by the derivative is used. -/
theorem exists_mul_add_mul_eq_discr (f : R[X]) (hf : f.Monic)
    (hdegree : 0 < f.natDegree) :
    ∃ A B : R[X], A * f + B * f.derivative =
      C ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr) := by
  obtain ⟨A, B, _, _, h⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl (natDegree_derivative_le f) (Or.inl (Nat.ne_of_gt hdegree))
  refine ⟨A, B, ?_⟩
  simpa only [← monic_discr_resultant f hf, mul_comm f A, mul_comm f.derivative B] using h

/-- Padding the derivative degree does not change a monic resultant, even
when leading derivative coefficients vanish in positive characteristic. -/
theorem monic_derivative_resultant (f : R[X]) (hf : f.Monic) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) =
      f.resultant f.derivative := by
  have h := resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree
    (f.natDegree - 1 - f.derivative.natDegree) le_rfl
  simpa [Nat.add_sub_of_le (natDegree_derivative_le f), hf.leadingCoeff] using h

/-- Nonvanishing of the existing monic discriminant is precisely
separability, in every characteristic and including degree one. -/
theorem monic_discr_ne_zero_iff {C : Type*} [Field C] (f : C[X]) (hf : f.Monic) :
    f.discr ≠ 0 ↔ f.Separable := by
  have h := monic_discr_resultant f hf
  rw [monic_derivative_resultant f hf] at h
  have he : f.discr ≠ 0 ↔ f.resultant f.derivative ≠ 0 := by
    rw [← h]
    simp
  rw [he, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

section Valuation

variable {C Γ : Type*} [Field C] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation C Γ)

/-- Every root in the original valued field of a monic integral polynomial
belongs to its actual valuation ring. -/
theorem monic_root_valuation_le_one (f : v.valuationSubring[X]) (hf : f.Monic)
    (x : C) (hx : aeval x f = 0) : v x ≤ 1 :=
  (Valuation.valuationSubring.integers v).isIntegral_iff_v_le_one.mp ⟨f, hf, hx⟩

/-- Evaluating the integral discriminant Bezout identity bounds at least
one of the polynomial and derivative values, over any valued field. -/
theorem valuation_discr_le_max (f : v.valuationSubring[X]) (hf : f.Monic)
    (hdegree : 0 < f.natDegree) (z : v.valuationSubring) :
    v (f.discr : C) ≤ max (v ((f.eval z : v.valuationSubring) : C)) (v ((f.derivative.eval z :
        v.valuationSubring) : C)) := by
  obtain ⟨A, B, h⟩ := exists_mul_add_mul_eq_discr f hf hdegree
  have he : ((A.eval z : v.valuationSubring) : C) * ((f.eval z : v.valuationSubring) : C) +
      ((B.eval z : v.valuationSubring) : C) * ((f.derivative.eval z : v.valuationSubring) : C) =
        (-1 : C) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.discr : C) := by
    simpa using congrArg
      (fun g : v.valuationSubring[X] => ((g.eval z : v.valuationSubring) : C)) h
  have hv := v.map_add (((A.eval z : v.valuationSubring) : C) * ((f.eval z : v.valuationSubring) :
      C))
    (((B.eval z : v.valuationSubring) : C) * ((f.derivative.eval z : v.valuationSubring) : C))
  rw [he, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul] at hv
  refine hv.trans (max_le_max ?_ ?_)
  · rw [map_mul]
    exact mul_le_of_le_one_left' (A.eval z).property
  · rw [map_mul]
    exact mul_le_of_le_one_left' (B.eval z).property

/-- A sufficiently small residual forces the derivative to have valuation
at least the discriminant's valuation, without a unit-derivative premise. -/
theorem valuation_discr_le_derivative (f : v.valuationSubring[X]) (hf : f.Monic)
    (hdegree : 0 < f.natDegree) (z : v.valuationSubring)
    (hz : v ((f.eval z : v.valuationSubring) : C) < v (f.discr : C)) :
    v (f.discr : C) ≤ v ((f.derivative.eval z : v.valuationSubring) : C) := by
  rcases le_max_iff.mp (valuation_discr_le_max v f hf hdegree z) with h | h
  · exact False.elim ((not_le_of_gt hz) h)
  · exact h

end Valuation

end FontaineWintenberger
