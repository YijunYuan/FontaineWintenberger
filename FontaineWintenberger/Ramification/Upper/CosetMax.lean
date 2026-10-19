/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.FixedField
public import FontaineWintenberger.Ramification.Herbrand.Affine

/-!
# The largest intrinsic ramification order in a restriction coset

The strict product rule identifies a maximal coset representative's
displacements with truncated subgroup orders. Tate's fixed-field
average then gives the Herbrand value, including maximum zero.

## Main results

* `ramificationOrder_mul_eq_min_of_coset_max`: At a maximal representative, multiplication truncates
  the subgroup order.
* `truncatedRamificationOrder_eq_coset_order`: A finite maximal coset order supplies exactly the cap
  in the Herbrand sum.
* `exists_fixedField_ramificationOrder_max`: Every nonidentity restriction fiber has an attained
  finite maximal order.
* `fixedField_order_sub_one_eq_herbrand`: Tate's average at a maximal representative is the integral
  Herbrand value.
* `exists_fixedField_order_eq_herbrand`: The coset-maximum formula on every nonidentity restriction
  fiber.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal

section GroupAction

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R]

@[simp]
theorem ramificationOrder_subgroup (H : Subgroup G) (h : H) :
    ramificationOrder (R := R) H h = ramificationOrder (R := R) G h.1 := rfl

/-- At a maximal representative, multiplication truncates the subgroup order. -/
theorem ramificationOrder_mul_eq_min_of_coset_max (H : Subgroup G) (s : G)
    (hmax : ∀ h : H, ramificationOrder (R := R) G (s * h.1) ≤
      ramificationOrder (R := R) G s) (h : H) :
    ramificationOrder (R := R) G (s * h.1) =
      min (ramificationOrder (R := R) H h) (ramificationOrder (R := R) G s) := by
  rw [ramificationOrder_subgroup]
  by_cases hlt : ramificationOrder (R := R) G h.1 < ramificationOrder (R := R) G s
  · rw [ramificationOrder_mul_of_ne G s h.1 (ne_of_gt hlt), min_comm]
  · have hle := le_of_not_gt hlt
    exact le_antisymm ((hmax h).trans_eq (min_eq_right hle).symm)
      (by simpa only [min_comm] using min_order_le_order_mul (R := R) G s h.1)

/-- A finite maximal coset order supplies exactly the cap in the Herbrand sum. -/
theorem truncatedRamificationOrder_eq_coset_order (H : Subgroup G) (s : G) {m : ℕ}
    (hs : ramificationOrder (R := R) G s = m)
    (hmax : ∀ h : H, ramificationOrder (R := R) G (s * h.1) ≤
      ramificationOrder (R := R) G s) (h : H) :
    truncatedRamificationOrder (R := R) H h ((m : ℝ) - 1) =
      (ramificationOrder (R := R) G (s * h.1) : ℝ≥0∞).toReal := by
  rw [ramificationOrder_mul_eq_min_of_coset_max G H s hmax, hs,
    ENat.toENNReal_min, ENat.toENNReal_coe, truncatedRamificationOrder]
  simp only [sub_add_cancel, ENNReal.ofReal_natCast]

end GroupAction

section FixedField

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

local notation "G₀" => L ≃ₐ[K] L
local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- Every nonidentity restriction fiber has an attained finite maximal order. -/
theorem exists_fixedField_ramificationOrder_max (τ : D₀) (hτ : τ ≠ 1) :
    ∃ s : G₀, ρ s = τ ∧ ramificationOrder (R := B₀) G₀ s ≠ ⊤ ∧
      ∀ r : G₀, ρ r = τ →
        ramificationOrder (R := B₀) G₀ r ≤ ramificationOrder (R := B₀) G₀ s := by
  classical
  let := Fintype.ofFinite {s : G₀ // ρ s = τ}
  obtain ⟨s, hs⟩ := fixedFieldDecompositionRestriction_surjective K L H τ
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun r : {s : G₀ // ρ s = τ} => ramificationOrder (R := B₀) G₀ r.1)
    ⟨⟨s, hs⟩, Finset.mem_univ _⟩
  refine ⟨r.1, r.2, ?_, fun s hs => hr ⟨s, hs⟩ (Finset.mem_univ _)⟩
  apply (ramificationOrder_eq_top_iff G₀ r.1).not.mpr
  intro h
  exact hτ (r.2.symm.trans (h ▸ map_one ρ))

variable [PerfectField 𝓀[K]]

/-- Tate's average at a maximal representative is the integral Herbrand value. -/
theorem fixedField_order_sub_one_eq_herbrand (s : G₀) (hs : ρ s ≠ 1)
    (hmax : ∀ h : H, ramificationOrder (R := B₀) G₀ (s * h.1) ≤
      ramificationOrder (R := B₀) G₀ s) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    (((A₀).ramificationOrder K (ρ s)).toNat : ℝ) - 1 =
      herbrandFunction (R := B₀) H
        ((ramificationOrder (R := B₀) G₀ s).toNat - 1) := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  let := Fintype.ofFinite H
  have hsfinite : ramificationOrder (R := B₀) G₀ s ≠ ⊤ := by
    apply (ramificationOrder_eq_top_iff G₀ s).not.mpr
    intro h
    exact hs (h ▸ map_one ρ)
  have hτfinite : (A₀).ramificationOrder K (ρ s) ≠ ⊤ :=
    ((A₀).ramificationOrder_eq_top_iff K (ρ s)).not.mpr hs
  have hnat := ENat.natCast_toNat hsfinite
  have havg := congrArg ENNReal.toReal
    (fixedField_order_eq_sum_div_card_inertia K L H s)
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_sum] at havg
  · rw [← ENat.natCast_toNat hτfinite, ENat.toENNReal_coe,
      ENNReal.toReal_natCast] at havg
    rw [herbrandFunction_eq_sum H (by
      have : (0 : ℝ) ≤ (ramificationOrder (R := B₀) G₀ s).toNat := Nat.cast_nonneg _
      linarith), herbrandSum]
    rw [havg]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    exact (truncatedRamificationOrder_eq_coset_order G₀ H s hnat.symm hmax h).symm
  · intro h _
    exact ENat.toENNReal_ne_top.mpr (ne_top_of_le_ne_top hsfinite (hmax h))

/-- The coset-maximum formula on every nonidentity restriction fiber. -/
theorem exists_fixedField_order_eq_herbrand (τ : D₀) (hτ : τ ≠ 1) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ∃ s : G₀, ρ s = τ ∧ ramificationOrder (R := B₀) G₀ s ≠ ⊤ ∧
      (∀ r : G₀, ρ r = τ →
        ramificationOrder (R := B₀) G₀ r ≤ ramificationOrder (R := B₀) G₀ s) ∧
      (((A₀).ramificationOrder K τ).toNat : ℝ) - 1 =
        herbrandFunction (R := B₀) H
          ((ramificationOrder (R := B₀) G₀ s).toNat - 1) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  obtain ⟨s, hs, hsfinite, hmax⟩ := exists_fixedField_ramificationOrder_max K L H τ hτ
  refine ⟨s, hs, hsfinite, hmax, ?_⟩
  rw [← hs]
  apply fixedField_order_sub_one_eq_herbrand K L H s (hs ▸ hτ)
  intro h
  apply hmax
  have hker : h.1 ∈ (ρ).ker := by
    rw [fixedFieldDecompositionRestriction_ker]
    exact h.2
  rw [map_mul, MonoidHom.mem_ker.mp hker, mul_one, hs]

end FixedField

end FontaineWintenberger
