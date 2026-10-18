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
from original finite-field norm limits.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- Finite sums of integral original families remain integral for the
already constructed additive structure. -/
theorem normLimitValuation_sum_le_one [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → NormLimit K L)
    (ha : ∀ i ∈ s, normLimitValuation K L (a i) ≤ 1) :
    letI := normLimitAddCommMonoid K L p
    normLimitValuation K L (∑ i ∈ s, a i) ≤ 1 := by
  classical
  let := normLimitAddCommMonoid K L p
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact normLimitValuation_normLimitAdd_le_one K L p _ _
      (ha i (Finset.mem_insert_self i s)) (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- Every finite sum of original families approximates the ordinary sum
of its coordinates on an actual finite tail at each prescribed precision. -/
theorem normLimitEval_sum_sub_mem [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → NormLimit K L) :
    letI := normLimitAddCommMonoid K L p
    ∀ n : ℕ, ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      normLimitEval K L E (∑ i ∈ s, a i) - ∑ i ∈ s, normLimitEval K L E (a i) ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  let := normLimitAddCommMonoid K L p
  induction s using Finset.induction_on with
  | empty =>
    intro n
    refine ⟨FiniteLayer.bottom, fun E _ => ?_⟩
    simp only [Finset.sum_empty, map_zero, sub_self]
    exact ⟨0, Ideal.zero_mem _, rfl⟩
  | @insert i s hi ih =>
    intro n
    obtain ⟨T₁, hT₁⟩ := normLimitAdd_sub_mem K L p (a i) (∑ j ∈ s, a j) n
    obtain ⟨T₂, hT₂⟩ := ih n
    refine ⟨FiniteLayer.sup T₁ T₂, fun E hE => ?_⟩
    obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteLayer.le_sup_left T₁ T₂).trans hE)
    obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteLayer.le_sup_right T₁ T₂).trans hE)
    refine ⟨d₁ + d₂, Ideal.add_mem _ hd₁ hd₂, ?_⟩
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (d₁ : E.val) + (d₂ : E.val) = _
    linear_combination heq₁ + heq₂

/-- Repeated addition approximates ordinary coordinate repeated addition. -/
theorem normLimitEval_nsmul_sub_mem [IsAPF K L] (m : ℕ) (α : NormLimit K L) :
    letI := normLimitAddCommMonoid K L p
    ∀ n : ℕ, ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      normLimitEval K L E (m • α) - m • normLimitEval K L E α ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  let := normLimitAddCommMonoid K L p
  simpa only [Finset.sum_const, Finset.card_range] using
    normLimitEval_sum_sub_mem K L p (Finset.range m) (fun _ => α)

end FontaineWintenberger
