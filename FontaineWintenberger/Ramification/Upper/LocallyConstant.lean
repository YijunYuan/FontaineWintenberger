/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Upper.Basic

/-!
# Left local constancy of finite upper ramification groups

The ceiling convention for real lower groups makes upper groups constant on a sufficiently
small interval ending at any positive parameter. This includes the endpoint even at a jump.
-/

@[expose] public section

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

/-- Finite upper ramification groups are locally constant from the left at positive parameters,
with the endpoint included. -/
theorem exists_upperRamificationGroup_eq_left {u : ℝ} (hu : 0 < u) :
    ∃ v : ℝ, 0 < v ∧ v < u ∧ ∀ w ∈ Set.Ioc v u,
      upperRamificationGroup (R := R) G w = upperRamificationGroup (R := R) G u := by
  let t := inverseHerbrandFunction (R := R) G u
  have hu' : -1 ≤ u := by linarith
  have ht : 0 < t := by
    have h := strictMonoOn_inverseHerbrandFunction (R := R) G
      (show (0 : ℝ) ∈ Set.Ici (-1) by norm_num) hu' hu
    simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl] using h
  let n : ℤ := ⌈t⌉
  have hn : (n : ℝ) - 1 < t := by
    dsimp [n]
    linarith [Int.ceil_lt_add_one t]
  have hn0 : 0 ≤ (n : ℝ) - 1 := by
    have : 0 < n := Int.ceil_pos.mpr ht
    have : (1 : ℝ) ≤ n := by exact_mod_cast this
    linarith
  let a := herbrandFunction (R := R) G ((n : ℝ) - 1)
  have hau : a < u := by
    have h := strictMonoOn_herbrandFunction (R := R) G
      (show (n : ℝ) - 1 ∈ Set.Ici (-1) by change -1 ≤ _; linarith)
      (inverseHerbrandFunction_mem_Ici (R := R) G u) hn
    simpa only [herbrandFunction_inverseHerbrandFunction G hu'] using h
  let v := max (u / 2) a
  refine ⟨v, lt_of_lt_of_le (by positivity : 0 < u / 2) (le_max_left _ _),
    max_lt (by linarith) hau, fun w hw ↦ ?_⟩
  have hw0 : 0 < w := (lt_of_lt_of_le (by positivity : 0 < u / 2)
    (le_max_left _ _)).trans hw.1
  have hw' : -1 ≤ w := by linarith
  have hlower : (n : ℝ) - 1 < inverseHerbrandFunction (R := R) G w := by
    have h := strictMonoOn_inverseHerbrandFunction (R := R) G
      (herbrandFunction_mem_Ici (R := R) G (by linarith : -1 ≤ (n : ℝ) - 1)) hw'
      ((le_max_right (u / 2) a).trans_lt hw.1)
    simpa only [inverseHerbrandFunction_herbrandFunction G
      (by linarith : -1 ≤ (n : ℝ) - 1)] using h
  have hupper : inverseHerbrandFunction (R := R) G w ≤ n :=
    ((strictMonoOn_inverseHerbrandFunction (R := R) G).monotoneOn hw' hu' hw.2).trans
      (Int.le_ceil t)
  have hceil : ⌈inverseHerbrandFunction (R := R) G w⌉ = n :=
    Int.ceil_eq_iff.mpr ⟨hlower, hupper⟩
  simp only [upperRamificationGroup, lowerRamificationGroupReal, hceil]
  rfl

end FontaineWintenberger
