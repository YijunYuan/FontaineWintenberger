/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Herbrand

/-!
# The inverse Herbrand function on an interval of constant index

Where the APF index is constant equal to `c` on `(a, b]`, `ψ` is affine with slope `c`:
`ψ b - ψ a = (b - a) * c`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

theorem apfPsi_sub_apfPsi_of_apfIndex_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (c : ℕ)
    (hc : ∀ u ∈ Set.Ioc a b, apfIndex K L u = c) :
    apfPsi K L b - apfPsi K L a = (b - a) * c := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 a)
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L a b)
  have heq : (∫ u in a..b, apfHerbrandSlope K L u) = ∫ _u in a..b, (c : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [Set.uIoc_of_le hab] at hu
    rw [apfHerbrandSlope, max_eq_left (ha.trans hu.1.le), hc u hu]
  change apfPsi K L a + _ = apfPsi K L b at hadd
  rw [heq, intervalIntegral.integral_const, smul_eq_mul] at hadd
  linarith

end FontaineWintenberger
