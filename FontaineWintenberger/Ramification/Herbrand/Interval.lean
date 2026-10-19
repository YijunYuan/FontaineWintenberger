/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Herbrand.Basic

/-!
# Intervals under the Herbrand functions

`φ` maps the interval `(ψ a, ψ b]` into `(a, b]`, for `a, b ≥ -1`.

## References

* Serre, *Local Fields*, Chapter IV, §3.
-/

@[expose] public section

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

theorem herbrandFunction_mem_Ioc_of_inverseHerbrandFunction {a b t : ℝ}
    (ha : -1 ≤ a) (hb : -1 ≤ b)
    (ht0 : inverseHerbrandFunction (R := R) G a < t)
    (ht1 : t ≤ inverseHerbrandFunction (R := R) G b) :
    herbrandFunction (R := R) G t ∈ Set.Ioc a b := by
  have ht : -1 ≤ t := (inverseHerbrandFunction_mem_Ici (R := R) G a).trans ht0.le
  have hφ := herbrandFunction_mem_Ici (R := R) G ht
  have he := inverseHerbrandFunction_herbrandFunction (R := R) G ht
  constructor
  · apply ((strictMonoOn_inverseHerbrandFunction (R := R) G).lt_iff_lt ha hφ).mp
    simpa only [he] using ht0
  · apply ((strictMonoOn_inverseHerbrandFunction (R := R) G).le_iff_le hφ hb).mp
    simpa only [he] using ht1

end FontaineWintenberger
