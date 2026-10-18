/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Field

/-!
# The original stable norm valuation on the constructed field

The existing multiplicative valuation satisfies the ultrametric inequality
for precisely the constructed addition on the same field of norms carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The original stable multiplicative valuation is ultrametric for the
actual field of norms addition, before any valuation topology is chosen. -/
theorem FieldOfNorms.valuation_add_le_max [IsAPF K L] (α β : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.add K L α β) ≤
      max (FieldOfNorms.valuation K L α) (FieldOfNorms.valuation K L β) := by
  by_cases hα : α = 0
  · simp only [hα, FieldOfNorms.add_zero_left, _root_.map_zero, zero_le, max_eq_right, le_refl]
  by_cases hβ : β = 0
  · simp only [hβ, FieldOfNorms.add_zero_right, _root_.map_zero, zero_le, max_eq_left, le_refl]
  let w := FieldOfNorms.valuation K L
  have hαw : w α ≠ 0 := fun h => hα ((FieldOfNorms.valuation_eq_zero_iff K L α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((FieldOfNorms.valuation_eq_zero_iff K L β).mp h)
  have hscale : ∃ δ : FieldOfNorms K L, δ ≠ 0 ∧ w δ = max (w α) (w β) ∧
      w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
    rcases le_total (w α) (w β) with h | h
    · refine ⟨β, hβ, (max_eq_right h).symm, ?_, ?_⟩
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hβw)).mpr h
      · simp only [div_self hβ, _root_.map_one, le_refl]
    · refine ⟨α, hα, (max_eq_left h).symm, ?_, ?_⟩
      · simp only [div_self hα, _root_.map_one, le_refl]
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hαw)).mpr h
  obtain ⟨δ, hδ, hmax, ha, hb⟩ := hscale
  have hδα : δ * (α / δ) = α := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hsum := FieldOfNorms.valuation_fieldOfNormsAdd_le_one K L (α / δ) (β / δ) ha hb
  have heq := mul_fieldOfNormsAdd K L δ (α / δ) (β / δ)
  rw [hδα, hδβ] at heq
  change w (FieldOfNorms.add K L α β) ≤ max (w α) (w β)
  rw [← heq, _root_.map_mul, ← hmax]
  simpa only [mul_one] using mul_le_mul' (le_refl (w δ)) hsum

/-- The same stable map, now bundled as a field valuation for the actual
constructed field. No new map or alternate field carrier is introduced. -/
def FieldOfNorms.fieldValuation [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) :=
  { FieldOfNorms.valuation K L with
    map_add_le_max' := FieldOfNorms.valuation_add_le_max K L }

/-- Bundling the field valuation preserves exactly the existing stable map. -/
@[simp]
theorem FieldOfNorms.fieldValuation_apply [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (α : FieldOfNorms K L) :
    FieldOfNorms.fieldValuation K L α = FieldOfNorms.valuation K L α := rfl

/-- The canonical valued-field structure uses exactly the existing stable
map and its valuation uniformity on the same original field carrier. -/
instance FieldOfNorms.instValued [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Valued (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) :=
  Valued.mk' (FieldOfNorms.fieldValuation K L)

end FontaineWintenberger
