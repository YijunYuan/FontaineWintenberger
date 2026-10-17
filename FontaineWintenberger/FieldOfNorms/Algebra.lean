/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Approximation
public import FontaineWintenberger.FieldOfNorms.Separation

/-!
# Algebraic laws of the original norm-limit addition

Asymptotic coordinate approximation and fixed-base separation prove the laws
of the operation already constructed from actual original norm-sum limits.
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

/-- Associativity of the actual norm-limit addition follows from four
coordinate approximations and separation at a fixed original finite base. -/
theorem normLimitAdd_assoc (hL : IsAPF K L) (α β γ : NormLimit K L) :
    normLimitAdd K L p hL (normLimitAdd K L p hL α β) γ =
      normLimitAdd K L p hL α (normLimitAdd K L p hL β γ) := by
  apply normLimit_ext_of_eventually_sub_mem K L p hL
  intro n
  obtain ⟨T₁, hT₁⟩ := normLimitAdd_sub_mem K L p hL (normLimitAdd K L p hL α β) γ n
  obtain ⟨T₂, hT₂⟩ := normLimitAdd_sub_mem K L p hL α β n
  obtain ⟨T₃, hT₃⟩ := normLimitAdd_sub_mem K L p hL α (normLimitAdd K L p hL β γ) n
  obtain ⟨T₄, hT₄⟩ := normLimitAdd_sub_mem K L p hL β γ n
  refine ⟨FiniteLayer.sup (FiniteLayer.sup T₁ T₂) (FiniteLayer.sup T₃ T₄), fun E hE => ?_⟩
  have hE₁₂ := (FiniteLayer.le_sup_left (FiniteLayer.sup T₁ T₂)
    (FiniteLayer.sup T₃ T₄)).trans hE
  have hE₃₄ := (FiniteLayer.le_sup_right (FiniteLayer.sup T₁ T₂)
    (FiniteLayer.sup T₃ T₄)).trans hE
  obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteLayer.le_sup_left T₁ T₂).trans hE₁₂)
  obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteLayer.le_sup_right T₁ T₂).trans hE₁₂)
  obtain ⟨d₃, hd₃, heq₃⟩ := hT₃ E ((FiniteLayer.le_sup_left T₃ T₄).trans hE₃₄)
  obtain ⟨d₄, hd₄, heq₄⟩ := hT₄ E ((FiniteLayer.le_sup_right T₃ T₄).trans hE₃₄)
  refine ⟨d₁ + d₂ - d₃ - d₄,
    Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.add_mem _ hd₁ hd₂) hd₃) hd₄, ?_⟩
  change (d₁ : E.val) + (d₂ : E.val) - (d₃ : E.val) - (d₄ : E.val) = _
  linear_combination heq₁ + heq₂ - heq₃ - heq₄

/-- The original zero and the constructed addition form a commutative monoid
on the same carrier. This named value is used by the subsequent field structure. -/
@[instance_reducible]
def normLimitAddCommMonoid (hL : IsAPF K L) : AddCommMonoid (NormLimit K L) where
  zero := 0
  add := normLimitAdd K L p hL
  add_assoc := normLimitAdd_assoc K L p hL
  zero_add := normLimitAdd_zero_left K L p hL
  add_zero := normLimitAdd_zero_right K L p hL
  add_comm := normLimitAdd_comm K L p hL
  nsmul := @nsmulRec (NormLimit K L) inferInstance ⟨normLimitAdd K L p hL⟩

end FontaineWintenberger
