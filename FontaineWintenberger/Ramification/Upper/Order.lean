/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Upper.Basic

/-!
# Ramification filtrations determined by displacement orders

Two actions of the same finite group on discrete valuation rings have identical lower and
upper ramification filtrations whenever their normalized displacement orders agree. The rings
need not be isomorphic; this applies to finite layers and fields of norms of different
characteristics.
-/

@[expose] public section

namespace FontaineWintenberger

variable (G : Type*) {R S : Type*} [Group G]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [MulSemiringAction G R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [MulSemiringAction G S]

/-- Equality of displacement orders identifies real lower ramification groups. -/
theorem lowerRamificationGroupReal_eq_of_order_eq
    (h : ∀ g : G, ramificationOrder (R := R) G g = ramificationOrder (R := S) G g)
    (t : ℝ) :
    lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t =
      lowerRamificationGroupReal G (IsLocalRing.maximalIdeal S) t := by
  ext g
  simp only [mem_lowerRamificationGroupReal_iff_le_order, h]

/-- The Herbrand integral depends only on the displacement orders of the action. -/
theorem herbrandFunction_eq_of_order_eq
    (h : ∀ g : G, ramificationOrder (R := R) G g = ramificationOrder (R := S) G g)
    (t : ℝ) :
    herbrandFunction (R := R) G t = herbrandFunction (R := S) G t := by
  have hzero : lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0 =
      lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0 := by
    simpa only [lowerRamificationGroupReal, Int.ceil_zero] using
      lowerRamificationGroupReal_eq_of_order_eq G h 0
  simp only [herbrandFunction, lowerRamificationGroupReal_eq_of_order_eq G h, hzero]

variable [Finite G]

/-- Equality of displacement orders also identifies the inverse Herbrand functions. -/
theorem inverseHerbrandFunction_eq_of_order_eq
    (h : ∀ g : G, ramificationOrder (R := R) G g = ramificationOrder (R := S) G g)
    {u : ℝ} (hu : -1 ≤ u) :
    inverseHerbrandFunction (R := R) G u = inverseHerbrandFunction (R := S) G u := by
  apply (strictMonoOn_herbrandFunction (R := S) G).injOn
    (inverseHerbrandFunction_mem_Ici G u) (inverseHerbrandFunction_mem_Ici G u)
  rw [← herbrandFunction_eq_of_order_eq G h,
    herbrandFunction_inverseHerbrandFunction G hu,
    herbrandFunction_inverseHerbrandFunction G hu]

/-- Upper ramification is determined by the normalized displacement orders, even when the
two discrete valuation rings have different characteristics. -/
theorem upperRamificationGroup_eq_of_order_eq
    (h : ∀ g : G, ramificationOrder (R := R) G g = ramificationOrder (R := S) G g)
    {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := R) G u = upperRamificationGroup (R := S) G u := by
  rw [upperRamificationGroup, upperRamificationGroup,
    lowerRamificationGroupReal_eq_of_order_eq G h,
    inverseHerbrandFunction_eq_of_order_eq G h hu]

end FontaineWintenberger
