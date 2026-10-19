/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Hensel.NewtonLifting
public import FontaineWintenberger.LocalField.Spectral.CompatibleNorm

/-!
# Newton lifting for the discrete valuation

The compatible norm preserves the uniformity and the
valuation ring. Its comparison equivalence transports the proved Newton
construction back to the supplied valuation, including the exact distance.

## Main results

* `discreteValued_hensel_nonunit`: Newton lifting for the supplied discrete valuation and its
  integer ring, without any unit-derivative or residue-field finiteness assumption.
* `discreteValued_hensel_nonunit_additive`: The associated additive valuation formulation: the
  residual value exceeds twice the derivative value, and the root has exactly their difference as
  its distance value.
* `discreteValued_hensel_nonunit_ambient`: The Newton root is unique among all ambient field
  elements.
* `discreteValued_hensel_nonunit_ambient_additive`: Additive Newton statement with uniqueness over
  the entire field, including exact distance and derivative-value preservation.

## References

* Serre, *Local Fields*, Chapters I–II (discrete valuation rings, completions, unramified and
  totally ramified extensions).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [Field K] (Γ : Type*) [LinearOrderedCommGroupWithZero Γ]
variable [val : Valued K Γ] [Valuation.IsRankOneDiscrete val.v] [CompleteSpace K]

/-- Newton lifting for the supplied discrete valuation and its integer
ring, without any unit-derivative or residue-field finiteness assumption. -/
theorem discreteValued_hensel_nonunit (f : Polynomial val.v.valuationSubring)
    (z : val.v.valuationSubring)
    (hz : val.v (↑(f.eval z) : K) < val.v (↑(f.derivative.eval z) : K) ^ 2) :
    ∃ a : val.v.valuationSubring, f.eval a = 0 ∧
      val.v ((a - z : val.v.valuationSubring) : K) < val.v (↑(f.derivative.eval z) : K) ∧
      val.v (↑(f.derivative.eval a) : K) = val.v (↑(f.derivative.eval z) : K) ∧
      val.v ((a - z : val.v.valuationSubring) : K) =
        val.v (↑(f.eval z) : K) / val.v (↑(f.derivative.eval z) : K) ∧
      ∀ b : val.v.valuationSubring, f.eval b = 0 →
        val.v ((b - z : val.v.valuationSubring) : K) < val.v (↑(f.derivative.eval z) : K) →
          b = a := by
  let : Valuation.RankOne val.v :=
    Valuation.IsRankOneDiscrete.rankOne val.v (e := 2) (by norm_num)
  let : NontriviallyNormedField K := discreteValuedNormedField K Γ
  let : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (Valued.isNonarchimedean_norm K Γ)
  have hring := discreteValued_valuationSubring K Γ
  revert hz z f
  rw [← hring]
  intro f z hz
  have hle (x y : K) : ‖x‖ ≤ ‖y‖ ↔ val.v x ≤ val.v y := discreteValued_norm_le_iff K Γ x y
  have hlt (x y : K) : ‖x‖ < ‖y‖ ↔ val.v x < val.v y := by
    simp only [lt_iff_not_ge, hle]
  have heq (x y : K) : ‖x‖ = ‖y‖ ↔ val.v x = val.v y := by
    simp only [le_antisymm_iff, hle]
  have hnorm : ‖f.eval z‖ < ‖f.derivative.eval z‖ ^ 2 := by
    have h : ‖(↑(f.eval z) : K)‖ < ‖(↑(f.derivative.eval z) : K) ^ 2‖ :=
      (hlt _ _).mpr (by simpa only [map_pow] using hz)
    change ‖(↑(f.eval z) : K)‖ < ‖(↑(f.derivative.eval z) : K)‖ ^ 2
    simpa only [norm_pow] using h
  obtain ⟨a, ha, hclose, hderiv, hdist, huniq⟩ := unitBall_hensel_nonunit hnorm
  refine ⟨a, ha, (hlt _ _).mp hclose, (heq _ _).mp hderiv, ?_, ?_⟩
  · rw [← map_div₀]
    apply (heq _ _).mp
    rw [norm_div]
    exact hdist
  · intro b hb hbz
    exact huniq b hb ((hlt _ _).mpr hbz)

/-- The associated additive valuation formulation: the residual
value exceeds twice the derivative value, and the root has exactly their
difference as its distance value. The zero-residual case is included. -/
theorem discreteValued_hensel_nonunit_additive (f : Polynomial val.v.valuationSubring)
    (z : val.v.valuationSubring)
    (hz : (2 : ℕ) • (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
      (Valuation.toAddValuation val.v) (↑(f.eval z) : K)) :
    ∃ a : val.v.valuationSubring, f.eval a = 0 ∧
      (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
        (Valuation.toAddValuation val.v) ((a - z : val.v.valuationSubring) : K) ∧
      (Valuation.toAddValuation val.v) (↑(f.derivative.eval a) : K) =
        (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) ∧
      (Valuation.toAddValuation val.v) ((a - z : val.v.valuationSubring) : K) =
        (Valuation.toAddValuation val.v) (↑(f.eval z) : K) -
          (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) ∧
      ∀ b : val.v.valuationSubring, f.eval b = 0 →
        (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
          (Valuation.toAddValuation val.v) ((b - z : val.v.valuationSubring) : K) → b = a := by
  have hmul : val.v (↑(f.eval z) : K) < val.v (↑(f.derivative.eval z) : K) ^ 2 := by
    rw [two_nsmul] at hz
    change val.v (↑(f.eval z) : K) <
      val.v (↑(f.derivative.eval z) : K) * val.v (↑(f.derivative.eval z) : K) at hz
    simpa only [pow_two] using hz
  obtain ⟨a, ha, hclose, hderiv, hdist, huniq⟩ := discreteValued_hensel_nonunit K Γ f z hmul
  exact ⟨a, ha, hclose, hderiv, hdist, huniq⟩

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [Field K] (Γ : Type*) [LinearOrderedCommGroupWithZero Γ]
variable [val : Valued K Γ] [Valuation.IsRankOneDiscrete val.v] [CompleteSpace K]

/-- The Newton root is unique among all ambient field elements.
Closeness forces any competing root into the integer ring. -/
theorem discreteValued_hensel_nonunit_ambient (f : Polynomial val.v.valuationSubring)
    (z : val.v.valuationSubring)
    (hz : val.v (↑(f.eval z) : K) < val.v (↑(f.derivative.eval z) : K) ^ 2) :
    ∃ a : K, Polynomial.aeval a f = 0 ∧
      val.v (a - z) < val.v (↑(f.derivative.eval z) : K) ∧
      val.v (Polynomial.aeval a f.derivative) = val.v (↑(f.derivative.eval z) : K) ∧
      val.v (a - z) = val.v (↑(f.eval z) : K) / val.v (↑(f.derivative.eval z) : K) ∧
      ∀ b : K, Polynomial.aeval b f = 0 →
        val.v (b - z) < val.v (↑(f.derivative.eval z) : K) → b = a := by
  obtain ⟨a, ha, hclose, hderiv, hdist, huniq⟩ := discreteValued_hensel_nonunit K Γ f z hz
  have heval (x : val.v.valuationSubring) (g : Polynomial val.v.valuationSubring) :
      Polynomial.aeval (x : K) g = (g.eval x : val.v.valuationSubring) := by
    change Polynomial.aeval (algebraMap val.v.valuationSubring K x) g = _
    rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  refine ⟨a, ?_, hclose, ?_, hdist, ?_⟩
  · rw [heval, ha]
    rfl
  · rw [heval]
    exact hderiv
  · intro b hb hbz
    have hbdiff : val.v (b - z) ≤ 1 := hbz.le.trans (f.derivative.eval z).property
    have hbmem : val.v b ≤ 1 := by
      calc
        val.v b = val.v ((b - z) + (z : K)) := by rw [sub_add_cancel]
        _ ≤ max (val.v (b - z)) (val.v (z : K)) := val.v.map_add _ _
        _ ≤ 1 := max_le hbdiff z.property
    let b₀ : val.v.valuationSubring := ⟨b, hbmem⟩
    have hb₀ : f.eval b₀ = 0 := by
      apply Subtype.ext
      change (↑(f.eval b₀) : K) = 0
      rw [← heval]
      exact hb
    exact congrArg (fun x : val.v.valuationSubring => (x : K)) (huniq b₀ hb₀ hbz)

/-- Additive Newton statement with uniqueness over the entire
field, including exact distance and derivative-value preservation. -/
theorem discreteValued_hensel_nonunit_ambient_additive (f : Polynomial val.v.valuationSubring)
    (z : val.v.valuationSubring)
    (hz : (2 : ℕ) • (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
      (Valuation.toAddValuation val.v) (↑(f.eval z) : K)) :
    ∃ a : K, Polynomial.aeval a f = 0 ∧
      (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
        (Valuation.toAddValuation val.v) (a - z) ∧
      (Valuation.toAddValuation val.v) (Polynomial.aeval a f.derivative) =
        (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) ∧
      (Valuation.toAddValuation val.v) (a - z) =
        (Valuation.toAddValuation val.v) (↑(f.eval z) : K) -
          (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) ∧
      ∀ b : K, Polynomial.aeval b f = 0 →
        (Valuation.toAddValuation val.v) (↑(f.derivative.eval z) : K) <
          (Valuation.toAddValuation val.v) (b - z) → b = a := by
  have hmul : val.v (↑(f.eval z) : K) < val.v (↑(f.derivative.eval z) : K) ^ 2 := by
    rw [two_nsmul] at hz
    change val.v (↑(f.eval z) : K) <
      val.v (↑(f.derivative.eval z) : K) * val.v (↑(f.derivative.eval z) : K) at hz
    simpa only [pow_two] using hz
  exact discreteValued_hensel_nonunit_ambient K Γ f z hmul

end FontaineWintenberger
