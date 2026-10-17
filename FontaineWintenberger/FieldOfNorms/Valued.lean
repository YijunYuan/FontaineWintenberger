module

public import FontaineWintenberger.FieldOfNorms.Field

/-!
# The original stable norm valuation on the constructed field

The existing multiplicative valuation satisfies the ultrametric inequality
for precisely the constructed addition on the same norm-limit carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The original stable multiplicative valuation is ultrametric for the
actual norm-limit addition, before any valuation topology is chosen. -/
theorem normLimitValuation_add_le_max (hL : IsAPF K L) (α β : NormLimit K L) :
    normLimitValuation K L hL (normLimitAdd K L p hL α β) ≤
      max (normLimitValuation K L hL α) (normLimitValuation K L hL β) := by
  by_cases hα : α = 0
  · simp only [hα, normLimitAdd_zero_left, map_zero, zero_le, max_eq_right, le_refl]
  by_cases hβ : β = 0
  · simp only [hβ, normLimitAdd_zero_right, map_zero, zero_le, max_eq_left, le_refl]
  let w := normLimitValuation K L hL
  have hαw : w α ≠ 0 := fun h => hα ((normLimitValuation_eq_zero_iff K L hL α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((normLimitValuation_eq_zero_iff K L hL β).mp h)
  have hscale : ∃ δ : NormLimit K L, δ ≠ 0 ∧ w δ = max (w α) (w β) ∧
      w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
    rcases le_total (w α) (w β) with h | h
    · refine ⟨β, hβ, (max_eq_right h).symm, ?_, ?_⟩
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hβw)).mpr h
      · simp only [div_self hβ, map_one, le_refl]
    · refine ⟨α, hα, (max_eq_left h).symm, ?_, ?_⟩
      · simp only [div_self hα, map_one, le_refl]
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hαw)).mpr h
  obtain ⟨δ, hδ, hmax, ha, hb⟩ := hscale
  have hδα : δ * (α / δ) = α := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hsum := normLimitValuation_normLimitAdd_le_one K L p hL (α / δ) (β / δ) ha hb
  have heq := mul_normLimitAdd K L p hL δ (α / δ) (β / δ)
  rw [hδα, hδβ] at heq
  change w (normLimitAdd K L p hL α β) ≤ max (w α) (w β)
  rw [← heq, map_mul, ← hmax]
  simpa only [mul_one] using mul_le_mul' (le_refl (w δ)) hsum

/-- The same stable map, now bundled as a field valuation for the actual
constructed field. No new map or alternate field carrier is introduced. -/
def normLimitFieldValuation (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    Valuation (NormLimit K L) (WithZero (Multiplicative ℤ)) := by
  letI := normLimitField K L p hL hInfinite
  exact {
    normLimitValuation K L hL with
    map_add_le_max' := normLimitValuation_add_le_max K L p hL }

/-- Bundling the field valuation preserves exactly the existing stable map. -/
@[simp]
theorem normLimitFieldValuation_apply (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) (α : NormLimit K L) :
    normLimitFieldValuation K L p hL hInfinite α = normLimitValuation K L hL α := rfl

/-- The canonical valued-field structure uses exactly the existing stable
map and its valuation uniformity on the same original field carrier. -/
@[instance_reducible]
def normLimitValued (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    Valued (NormLimit K L) (WithZero (Multiplicative ℤ)) := by
  letI := normLimitField K L p hL hInfinite
  exact Valued.mk' (normLimitFieldValuation K L p hL hInfinite)

end FontaineWintenberger
