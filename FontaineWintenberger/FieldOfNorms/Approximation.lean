/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Operations

/-!
# Asymptotic coordinate approximation of the original field of norms addition

The existing normalized valuations control multiplicative scaling of integral
coordinate errors on the original fields.
-/

@[expose] public section

noncomputable section

namespace ValuationSubring

variable {E : Type*} [Field E] (A : ValuationSubring E) [IsDiscreteValuationRing A]

/-- An ambient-field ideal-power bound is exactly the bound for the existing
canonical normalized valuation, including its integrality consequence. -/
theorem mem_image_maximalIdeal_pow_iff_normalizedValuation (x : E) (n : ℕ) :
    x ∈ (fun a : A => (a : E)) ''
        ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation E x ≤ WithZero.exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_maximalIdeal_pow_iff_normalizedValuation A a n).mp ha
  · intro hx
    have hbound : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hmem : x ∈ A := by
      rw [← normalizedValuation_valuationSubring A]
      exact hx.trans hbound
    exact ⟨⟨x, hmem⟩,
      (mem_maximalIdeal_pow_iff_normalizedValuation A ⟨x, hmem⟩ n).mpr hx, rfl⟩

end ValuationSubring

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual sum of arbitrary original norm families agrees with coordinate
addition to every eventual ideal-power precision. -/
theorem FieldOfNorms.add_sub_mem [IsAPF K L] (α β : FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
        FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  let w := FieldOfNorms.valuation K L
  let S : Finset (FieldOfNorms K L) := {1, α, β}
  obtain ⟨δ, _, hmax⟩ := Finset.exists_max_image S w ⟨1, by simp [S]⟩
  have hone : 1 ≤ w δ := by simpa only [_root_.map_one] using hmax 1 (by simp [S])
  have hδpos : 0 < w δ := zero_lt_one.trans_le hone
  have hδ : δ ≠ 0 := by
    intro hz
    rw [hz, _root_.map_zero] at hone
    exact not_le_of_gt zero_lt_one hone
  have ha : w (α / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax α (by simp [S]))
  have hb : w (β / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax β (by simp [S]))
  have hδα : δ * (α / δ) = α := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  let q := (WithZero.log (w δ)).toNat
  have hδbound : w δ ≤ WithZero.exp (q : ℤ) :=
    WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat _))
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  intro n
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.add_sub_mem_of_valuation_le_one
    K L (α / δ) (β / δ) ha hb (n + q)
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E hE => ?_⟩
  have hE₀ := (FiniteIntermediateField.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteIntermediateField.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hvδ : v (FieldOfNorms.coord K L E δ) ≤ WithZero.exp (q : ℤ) := by
    change FieldOfNorms.coordinateValuation K L E δ ≤ _
    rw [← hT₀ E hE₀ δ]
    exact hδbound
  have hvε : v (FieldOfNorms.coord K L E (FieldOfNorms.add K L (α / δ) (β / δ)) -
      FieldOfNorms.coord K L E (α / δ) - FieldOfNorms.coord K L E (β / δ)) ≤
        WithZero.exp (-((n + q : ℕ) : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ (n + q)).mp (hT₁ E hE₁)
  apply (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) _ n).mpr
  have hs := congrArg (FieldOfNorms.coord K L E)
    (mul_fieldOfNormsAdd K L δ (α / δ) (β / δ))
  rw [_root_.map_mul, hδα, hδβ] at hs
  have hαE : FieldOfNorms.coord K L E δ * FieldOfNorms.coord K L E (α / δ) =
      FieldOfNorms.coord K L E α := by rw [← _root_.map_mul, hδα]
  have hβE : FieldOfNorms.coord K L E δ * FieldOfNorms.coord K L E (β / δ) =
      FieldOfNorms.coord K L E β := by rw [← _root_.map_mul, hδβ]
  have heq : FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
      FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β =
      FieldOfNorms.coord K L E δ *
        (FieldOfNorms.coord K L E (FieldOfNorms.add K L (α / δ) (β / δ)) -
          FieldOfNorms.coord K L E (α / δ) - FieldOfNorms.coord K L E (β / δ)) := by
    rw [← hs, ← hαE, ← hβE]
    ring
  change v _ ≤ _
  rw [heq, _root_.map_mul]
  calc
    _ ≤ WithZero.exp (q : ℤ) * WithZero.exp (-((n + q : ℕ) : ℤ)) :=
      mul_le_mul' hvδ hvε
    _ = WithZero.exp (-(n : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega

end FontaineWintenberger
