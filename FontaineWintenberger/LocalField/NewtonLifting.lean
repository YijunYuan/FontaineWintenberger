/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Henselian
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Newton lifting with a nonunit derivative

The Newton estimates generalize the proof in Mathlib's p-adic Hensel module
to the original valuation unit ball of any complete nontrivially normed
ultrametric field.
Division is performed in the original ambient field. No unit condition on
the derivative and no residue-field finiteness hypothesis are imposed.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace FontaineWintenberger

section Newton

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "O" => Valuation.valuationSubring (NormedField.valuation (K := K))

private theorem newton_unitBall_norm_le_one (x : O) : ‖x‖ ≤ 1 := by
  exact_mod_cast x.property

/-- Integral polynomial evaluation is nonexpanding on the actual valuation
unit ball. The divided difference remains in that same integer ring. -/
theorem unitBall_polynomial_norm_sub_le (F : Polynomial O) (x y : O) :
    ‖F.eval x - F.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨q, hq⟩ := F.evalSubFactor x y
  calc
    _ = ‖q‖ * ‖x - y‖ := by simp [hq]
    _ ≤ 1 * ‖x - y‖ := by
      gcongr
      exact newton_unitBall_norm_le_one q
    _ = _ := one_mul _

private theorem newton_root_unique {F : Polynomial O} {a : O}
    (ha : F.eval a = 0) (z : O) (hz : F.eval z = 0)
    (hclose : ‖z - a‖ < ‖F.derivative.eval a‖) : z = a := by
  let h := z - a
  obtain ⟨q, hq⟩ := F.binomExpansion a h
  have hmul : (F.derivative.eval a + q * h) * h = 0 := by
    calc
      _ = F.eval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
      _ = 0 := by simp [h, hz]
  have hh : h = 0 := by
    by_contra hne
    have hfactor : F.derivative.eval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right hne
    have heq : F.derivative.eval a = -q * h := by
      simpa using eq_neg_of_add_eq_zero_left hfactor
    exact lt_irrefl ‖F.derivative.eval a‖ (calc
      _ = ‖q‖ * ‖h‖ := by simp [heq]
      _ ≤ 1 * ‖h‖ := by gcongr; exact newton_unitBall_norm_le_one q
      _ < ‖F.derivative.eval a‖ := by simpa only [one_mul] using hclose)
  exact eq_of_sub_eq_zero hh

/-- In the derivative ball, Taylor's linear term determines the exact change in norm. -/
theorem unitBall_polynomial_norm_sub_eq_of_norm_lt_derivative (F : Polynomial O) (a z : O)
    (hclose : ‖z - a‖ < ‖F.derivative.eval a‖) :
    ‖F.eval z - F.eval a‖ = ‖F.derivative.eval a‖ * ‖z - a‖ := by
  let h := z - a
  obtain ⟨q, hq⟩ := F.binomExpansion a h
  have hfactor : F.eval z - F.eval a = (F.derivative.eval a + q * h) * h := by
    calc
      _ = F.eval (a + h) - F.eval a := by simp [h]
      _ = _ := by rw [hq]; ring
  have hsmall : ‖q * h‖ < ‖F.derivative.eval a‖ := by
    calc
      ‖q * h‖ = ‖q‖ * ‖h‖ := norm_mul _ _
      _ ≤ 1 * ‖h‖ := by gcongr; exact newton_unitBall_norm_le_one q
      _ < ‖F.derivative.eval a‖ := by simpa only [one_mul] using hclose
  rw [hfactor, norm_mul,
    IsUltrametricDist.isNonarchimedean_norm.add_eq_left_of_lt norm_neg hsmall]

section Hensel

open Nat

variable {F : Polynomial (Valuation.valuationSubring (NormedField.valuation (K := K)))}
  {a : Valuation.valuationSubring (NormedField.valuation (K := K))}

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
private def T_gen (F : Polynomial O) (a : O) : ℝ := ‖F.eval a‖ / ‖F.derivative.eval a‖ ^ 2

local notation "T" => T_gen F a

private theorem T_def : T = ‖F.eval a‖ / ‖F.derivative.eval a‖ ^ 2 := by
  rfl

private theorem T_nonneg : 0 ≤ T := div_nonneg (norm_nonneg _) (sq_nonneg _)

private theorem T_pow_nonneg (n : ℕ) : 0 ≤ T ^ n := pow_nonneg T_nonneg _

variable (hnorm : ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2)
include hnorm

private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.eval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm

private theorem deriv_sq_norm_ne_zero : ‖F.derivative.eval a‖ ^ 2 ≠ 0 :=
  ne_of_gt (deriv_sq_norm_pos hnorm)

private theorem deriv_norm_ne_zero : ‖F.derivative.eval a‖ ≠ 0 := fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])

private theorem deriv_norm_pos : 0 < ‖F.derivative.eval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))

private theorem deriv_ne_zero : F.derivative.eval a ≠ 0 :=
  mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)


private theorem T_lt_one : T < 1 := by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h

private theorem T_pow {n : ℕ} (hn : n ≠ 0) : T ^ n < 1 := pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn

private theorem T_pow' (n : ℕ) : T ^ 2 ^ n < 1 := T_pow hnorm (pow_ne_zero _ two_ne_zero)

/-- Newton approximations in the original valuation unit ball satisfy successive values of `ih`. -/
private def ih_gen (n : ℕ) (z : O) : Prop :=
  ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧ ‖F.eval z‖ ≤
    ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => ih_gen (F := F) (a := a)

private theorem ih_0 : ih 0 a := by
  refine ⟨rfl, ?_⟩
  simp only [pow_zero, pow_one, T_def]
  rw [mul_comm]
  exact le_of_eq (div_mul_cancel₀ _ (deriv_sq_norm_ne_zero hnorm)).symm

private theorem calc_norm_le_one {n : ℕ} {z : O} (hz : ih n z) :
    ‖(↑(F.eval z) : K) / ↑(F.derivative.eval z)‖ ≤ 1 :=
  calc
    ‖(↑(F.eval z) : K) / ↑(F.derivative.eval z)‖ =
        ‖(↑(F.eval z) : K)‖ / ‖(↑(F.derivative.eval z) : K)‖ :=
      norm_div _ _
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ :=
      congrArg (fun t : ℝ => ‖F.eval z‖ / t) hz.1
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ ≤ 1 := by bound [newton_unitBall_norm_le_one (F.derivative.eval a), T_pow' hnorm n]

private theorem calc_deriv_dist {z z' z1 : O} (hz' : z' = z - z1)
    (hz1 : ‖z1‖ = ‖F.eval z‖ / ‖F.derivative.eval a‖) {n} (hz : ih n z) :
    ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
  calc
    ‖F.derivative.eval z' - F.derivative.eval z‖ ≤ ‖z' - z‖ := unitBall_polynomial_norm_sub_le _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := hz1
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.eval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)


private theorem calc_eval_newton {z z' z1 : O} (hz' : z' = z - z1)
    {n : ℕ} (hz : ih n z)
    (hzeq : (z1 : K) = (↑(F.eval z) : K) / (↑(F.derivative.eval z) : K)) :
    ∃ q : O, F.eval z' = q * z1 ^ 2 := by
  have hdzne : F.derivative.eval z ≠ 0 := by
    intro hzero
    have := hz.1
    rw [hzero, norm_zero] at this
    exact deriv_norm_ne_zero hnorm this.symm
  have hdzne' : (↑(F.derivative.eval z) : K) ≠ 0 := by
    exact_mod_cast hdzne
  obtain ⟨q, hq⟩ := F.binomExpansion z (-z1)
  have hcancel : F.derivative.eval z * -z1 = -F.eval z := by
    apply Subtype.ext
    change (↑(F.derivative.eval z) : K) * -(z1 : K) = -(↑(F.eval z) : K)
    rw [hzeq, mul_neg, mul_div_cancel₀ _ hdzne']
  exact ⟨q, by simpa [sub_eq_add_neg, hcancel, hz'] using hq⟩

omit hnorm in
private theorem calc_eval_newton_norm {z z' z1 : O} {n : ℕ} (hz : ih n z)
    {q : O} (heq : F.eval z' = q * z1 ^ 2)
    (hz1 : ‖z1‖ = ‖F.eval z‖ / ‖F.derivative.eval a‖) :
    ‖F.eval z'‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by
  calc
    ‖F.eval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ ≤ 1 * ‖z1‖ ^ 2 := by gcongr; exact newton_unitBall_norm_le_one q
    _ = ‖F.eval z‖ ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by rw [hz1]; simp [div_pow]
    _ ≤ (‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.eval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.eval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]

/-- Division is in `K`; its norm bound proves that the correction belongs to `O`. -/
private def newton_correction {n : ℕ} {z : O} (hz : ih n z) : O :=
  ⟨(↑(F.eval z) : K) / (↑(F.derivative.eval z) : K), by
    exact_mod_cast calc_norm_le_one hnorm hz⟩

private theorem newton_correction_norm {n : ℕ} {z : O} (hz : ih n z) :
    ‖newton_correction hnorm hz‖ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := by
  change ‖(↑(F.eval z) : K) / (↑(F.derivative.eval z) : K)‖ = _
  rw [norm_div]
  exact congrArg (fun t : ℝ => ‖F.eval z‖ / t) hz.1

/-- The derivative norm is unchanged and the residual is squared at each actual Newton step. -/
private def ih_n {n : ℕ} {z : O} (hz : ih n z) : { z' : O // ih (n + 1) z' } := by
  let z1 := newton_correction hnorm hz
  let z' := z - z1
  have hdist : ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
    calc_deriv_dist hnorm rfl (newton_correction_norm hnorm hz) hz
  have hfeq : ‖F.derivative.eval z'‖ = ‖F.derivative.eval a‖ := by
    have hsmall : ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval z‖ := by
      rwa [hz.1]
    have heq := IsUltrametricDist.isNonarchimedean_norm.add_eq_right_of_lt
      (norm_neg : ∀ x : O, ‖-x‖ = ‖x‖) hsmall
    rw [sub_add_cancel] at heq
    exact heq.trans hz.1
  refine ⟨z', hfeq, ?_⟩
  obtain ⟨q, hq⟩ := calc_eval_newton hnorm (z' := z') rfl hz rfl
  exact calc_eval_newton_norm hz hq (newton_correction_norm hnorm hz)

private def newton_seq_aux : ∀ n : ℕ, { z : O // ih n z }
  | 0 => ⟨a, ih_0 hnorm⟩
  | k + 1 => ih_n hnorm (newton_seq_aux k).2

private def newton_seq_gen (n : ℕ) : O := (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm

private theorem newton_seq_deriv_norm (n : ℕ) :
    ‖F.derivative.eval (newton_seq n)‖ = ‖F.derivative.eval a‖ :=
  (newton_seq_aux hnorm n).2.1

private theorem newton_seq_norm_le (n : ℕ) :
    ‖F.eval (newton_seq n)‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux hnorm n).2.2

private theorem newton_seq_zero : newton_seq 0 = a := rfl

private theorem newton_seq_norm_eq (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ =
      ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval a‖ := by
  change ‖(newton_seq n - newton_correction hnorm (newton_seq_aux hnorm n).2) -
    newton_seq n‖ = _
  simpa only [newton_seq_gen, sub_sub_cancel_left, norm_neg] using
    newton_correction_norm hnorm (newton_seq_aux hnorm n).2

private theorem newton_seq_succ_dist (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n := by
  rw [newton_seq_norm_eq]
  calc
    ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval a‖ ≤
        (‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) / ‖F.derivative.eval a‖ := by
      gcongr
      exact newton_seq_norm_le hnorm n
    _ = _ := div_sq_cancel _ _

private theorem newton_seq_dist_aux (n : ℕ) :
    ∀ k : ℕ, ‖newton_seq (n + k) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n
  | 0 => by simp [T_pow_nonneg, mul_nonneg]
  | k + 1 => by
    have hexp : 2 ^ n ≤ 2 ^ (n + k) :=
      pow_right_mono₀ (by simp) (Nat.le_add_right n k)
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ =
          ‖newton_seq (n + k + 1) - newton_seq (n + k) +
            (newton_seq (n + k) - newton_seq n)‖ := by rw [← sub_add_sub_cancel, add_assoc]
      _ ≤ max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖
          ‖newton_seq (n + k) - newton_seq n‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (‖F.derivative.eval a‖ * T ^ 2 ^ (n + k))
          (‖F.derivative.eval a‖ * T ^ 2 ^ n) :=
        max_le_max (newton_seq_succ_dist hnorm _) (newton_seq_dist_aux n k)
      _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
        max_eq_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one T_nonneg (T_lt_one hnorm).le hexp) (norm_nonneg _))

private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
    ‖newton_seq k - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnk
  exact newton_seq_dist_aux hnorm n m

private theorem newton_bound_tendsto :
    Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.eval a‖]
  exact tendsto_const_nhds.mul
    ((tendsto_pow_atTop_nhds_zero_of_lt_one T_nonneg (T_lt_one hnorm)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by simp)))

private theorem newton_residual_bound_tendsto :
    Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.eval a‖, sq]
  simp only [mul_assoc]
  exact tendsto_const_nhds.mul (newton_bound_tendsto hnorm)

private theorem newton_seq_is_cauchy : CauchySeq newton_seq := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((newton_bound_tendsto hnorm).eventually (gt_mem_nhds hε))
  exact ⟨N, fun n hn => by
    rw [dist_eq_norm]
    exact (newton_seq_dist hnorm hn).trans_lt (hN N le_rfl)⟩

/-- Newton--Hensel lifting in the original unit ball of a complete ultrametric
field. The derivative may be a nonunit. The root has the exact Newton distance
from the initial approximation, and is unique in the derivative ball. -/
theorem unitBall_hensel_nonunit [CompleteSpace K] :
    ∃ z : O, F.eval z = 0 ∧
      ‖z - a‖ < ‖F.derivative.eval a‖ ∧
      ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧
      ‖z - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖ ∧
      ∀ z' : O, F.eval z' = 0 → ‖z' - a‖ < ‖F.derivative.eval a‖ → z' = z := by
  let : CompleteSpace O := unitBall_completeSpace K
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (newton_seq_is_cauchy hnorm)
  have heval_lim : Tendsto (fun n => F.eval (newton_seq n)) atTop (𝓝 (F.eval z)) :=
    F.continuousAt.tendsto.comp hz
  have hresidual : Tendsto (fun n => ‖F.eval (newton_seq n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm)
      (newton_residual_bound_tendsto hnorm)
  have hroot : F.eval z = 0 := tendsto_nhds_unique heval_lim
    (tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hresidual))
  have hderiv_lim : Tendsto (fun n => ‖F.derivative.eval (newton_seq n)‖)
      atTop (𝓝 ‖F.derivative.eval z‖) := (F.derivative.continuousAt.tendsto.comp hz).norm
  have hderiv_const : Tendsto (fun n => ‖F.derivative.eval (newton_seq n)‖)
      atTop (𝓝 ‖F.derivative.eval a‖) :=
    tendsto_const_nhds.congr (fun n => (newton_seq_deriv_norm hnorm n).symm)
  have hderiv : ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ :=
    tendsto_nhds_unique hderiv_lim hderiv_const
  have hdist_lim : Tendsto (fun n => ‖newton_seq n - a‖) atTop (𝓝 ‖z - a‖) :=
    (hz.sub tendsto_const_nhds).norm
  have hdist_bound : ‖z - a‖ ≤ ‖F.derivative.eval a‖ * T := by
    apply le_of_tendsto hdist_lim
    exact Eventually.of_forall (fun n => by
      simpa only [pow_zero, pow_one, newton_seq_zero] using
        (newton_seq_dist hnorm (Nat.zero_le n)))
  have hclose : ‖z - a‖ < ‖F.derivative.eval a‖ :=
    hdist_bound.trans_lt ((mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).mpr (T_lt_one hnorm))
  have hdist : ‖z - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖ := by
    have heq := unitBall_polynomial_norm_sub_eq_of_norm_lt_derivative F a z hclose
    rw [hroot, zero_sub, norm_neg] at heq
    exact (eq_div_iff (deriv_norm_ne_zero hnorm)).mpr (by simpa [mul_comm] using heq.symm)
  refine ⟨z, hroot, hclose, hderiv, hdist, ?_⟩
  intro z' hz' hclose'
  apply newton_root_unique hroot z' hz'
  rw [hderiv]
  calc
    ‖z' - z‖ = ‖z' - a + (a - z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖z' - a‖ ‖a - z‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ‖F.derivative.eval a‖ := max_lt hclose' (by rwa [norm_sub_rev])

end Hensel

end Newton

end FontaineWintenberger
