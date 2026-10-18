/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Associativity of the actual norm-limit addition follows from four
coordinate approximations and separation at a fixed original finite base. -/
theorem normLimitAdd_assoc [IsAPF K L] (α β γ : NormLimit K L) :
    normLimitAdd K L (normLimitAdd K L α β) γ =
      normLimitAdd K L α (normLimitAdd K L β γ) := by
  apply normLimit_ext_of_eventually_sub_mem K L
  intro n
  obtain ⟨T₁, hT₁⟩ := normLimitAdd_sub_mem K L (normLimitAdd K L α β) γ n
  obtain ⟨T₂, hT₂⟩ := normLimitAdd_sub_mem K L α β n
  obtain ⟨T₃, hT₃⟩ := normLimitAdd_sub_mem K L α (normLimitAdd K L β γ) n
  obtain ⟨T₄, hT₄⟩ := normLimitAdd_sub_mem K L β γ n
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
on the same carrier. Low priority: when `L/K` is infinite the `Field` instance supplies the
same structure, and instance search should go through it so that all paths agree syntactically. -/
instance (priority := low) normLimitAddCommMonoid [IsAPF K L] : AddCommMonoid (NormLimit K L) where
  zero := 0
  add := normLimitAdd K L
  add_assoc := normLimitAdd_assoc K L
  zero_add := normLimitAdd_zero_left K L
  add_zero := normLimitAdd_zero_right K L
  add_comm := normLimitAdd_comm K L
  nsmul := @nsmulRec (NormLimit K L) inferInstance ⟨normLimitAdd K L⟩

end FontaineWintenberger
