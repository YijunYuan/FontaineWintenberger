/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Algebra

/-!
# Finite sums and their original coordinate approximations

The named additive structure uses precisely the sum operation constructed
from original finite-field fields of norms.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Finite sums of integral original families remain integral for the
already constructed additive structure. -/
theorem FieldOfNorms.valuation_sum_le_one [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → FieldOfNorms K L)
    (ha : ∀ i ∈ s, FieldOfNorms.valuation K L (a i) ≤ 1) :
    FieldOfNorms.valuation K L (∑ i ∈ s, a i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact FieldOfNorms.valuation_fieldOfNormsAdd_le_one K L _ _
      (ha i (Finset.mem_insert_self i s)) (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- Every finite sum of original families approximates the ordinary sum
of its coordinates on an actual finite tail at each prescribed precision. -/
theorem FieldOfNorms.coord_sum_sub_mem [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (∑ i ∈ s, a i) - ∑ i ∈ s, FieldOfNorms.coord K L E (a i) ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    refine ⟨FiniteIntermediateField.bottom, fun E _ => ?_⟩
    simp only [Finset.sum_empty, _root_.map_zero, sub_self]
    exact ⟨0, Ideal.zero_mem _, rfl⟩
  | @insert i s hi ih =>
    intro n
    obtain ⟨T₁, hT₁⟩ := FieldOfNorms.add_sub_mem K L (a i) (∑ j ∈ s, a j) n
    obtain ⟨T₂, hT₂⟩ := ih n
    refine ⟨FiniteIntermediateField.sup T₁ T₂, fun E hE => ?_⟩
    obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteIntermediateField.le_sup_left T₁ T₂).trans hE)
    obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteIntermediateField.le_sup_right T₁ T₂).trans hE)
    refine ⟨d₁ + d₂, Ideal.add_mem _ hd₁ hd₂, ?_⟩
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (d₁ : E.val) + (d₂ : E.val) = _
    linear_combination heq₁ + heq₂

/-- Repeated addition approximates ordinary coordinate repeated addition. -/
theorem FieldOfNorms.coord_nsmul_sub_mem [IsAPF K L] (m : ℕ) (α : FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (m • α) - m • FieldOfNorms.coord K L E α ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  simpa only [Finset.sum_const, Finset.card_range] using
    FieldOfNorms.coord_sum_sub_mem K L (Finset.range m) (fun _ => α)

end FontaineWintenberger
