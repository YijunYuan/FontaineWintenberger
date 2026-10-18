/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Convergence

/-!
# The actual field of norms addition operation

Multiplicative scaling of the proved integral convergence constructs addition
on the same original multiplicative carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

section ScalarCovariance

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Multiplicative scaling is an exact identity on the original norm-sum
nets, before any limits or additive structure are chosen on the carrier. -/
theorem normSumNet_mul_left (E : FiniteIntermediateField K L) (δ α β : FieldOfNorms K L)
    (F : Set.Ici E) :
    normSumNet K L E (δ * α) (δ * β) F =
      FieldOfNorms.coord K L E δ * normSumNet K L E α β F := by
  simp only [normSumNet, map_mul]
  rw [← mul_add, map_mul, FieldOfNorms.coord_norm K L E F.val F.property δ]

end ScalarCovariance

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every pair of actual norm-compatible families has convergent original
norm-sum nets; existing nonzero families themselves provide the scaling. -/
theorem exists_tendsto_normSumNet [IsAPF K L] (α β : FieldOfNorms K L) :
    ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  by_cases hα : α = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨FieldOfNorms.coord K L E β, ?_⟩
    have heq : normSumNet K L E α β = fun _ => FieldOfNorms.coord K L E β := by
      funext F
      simp only [hα, normSumNet_zero_left]
    rw [heq]
    exact tendsto_const_nhds
  by_cases hβ : β = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨FieldOfNorms.coord K L E α, ?_⟩
    have heq : normSumNet K L E α β = fun _ => FieldOfNorms.coord K L E α := by
      funext F
      simp only [hβ, normSumNet_zero_right]
    rw [heq]
    exact tendsto_const_nhds
  let w := FieldOfNorms.valuation K L
  have hαw : w α ≠ 0 := fun h => hα ((FieldOfNorms.valuation_eq_zero_iff K L α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((FieldOfNorms.valuation_eq_zero_iff K L β).mp h)
  have hscale : ∃ δ : FieldOfNorms K L, δ ≠ 0 ∧ w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
    rcases le_total (w α) (w β) with h | h
    · refine ⟨β, hβ, ?_, ?_⟩
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hβw)).mpr h
      · simp only [div_self hβ, map_one, le_refl]
    · refine ⟨α, hα, ?_, ?_⟩
      · simp only [div_self hα, map_one, le_refl]
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hαw)).mpr h
  obtain ⟨δ, hδ, ha, hb⟩ := hscale
  have hδα : δ * (α / δ) = α := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  obtain ⟨z, hz⟩ := exists_tendsto_normSumNet_of_valuation_le_one
    K L (α / δ) (β / δ) ha hb E
  refine ⟨FieldOfNorms.coord K L E δ * z, ?_⟩
  simpa only [← normSumNet_mul_left, hδα, hδβ] using
    hz.const_mul (FieldOfNorms.coord K L E δ)

/-- The actual original field of norms contains the unique sum family of any
pair of its elements, characterized by the original norm-sum limits. -/
theorem existsUnique_fieldOfNorms_add [IsAPF K L] (α β : FieldOfNorms K L) :
    ∃! γ : FieldOfNorms K L, ∀ E : FiniteIntermediateField K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ)) :=
  existsUnique_fieldOfNorms_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet K L α β)

/-- Addition on the same original multiplicative field of norms carrier,
characterized by the actual norm-sum limits at every finite base. -/
def FieldOfNorms.add [IsAPF K L] (α β : FieldOfNorms K L) : FieldOfNorms K L :=
  (existsUnique_fieldOfNorms_add K L α β).choose

/-- Every original coordinate of the actual sum is its original norm-sum limit. -/
theorem tendsto_normSumNet_fieldOfNormsAdd [IsAPF K L] (α β : FieldOfNorms K L)
    (E : FiniteIntermediateField K L) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    Tendsto (normSumNet K L E α β) atTop
      (nhds (FieldOfNorms.coord K L E (FieldOfNorms.add K L α β))) :=
  (existsUnique_fieldOfNorms_add K L α β).choose_spec.1 E

/-- The original norm-sum limits uniquely characterize the same sum operation. -/
theorem eq_fieldOfNormsAdd_of_tendsto [IsAPF K L] (α β γ : FieldOfNorms K L)
    (hγ : ∀ E : FiniteIntermediateField K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ))) :
    γ = FieldOfNorms.add K L α β :=
  (existsUnique_fieldOfNorms_add K L α β).choose_spec.2 γ hγ

/-- Commutativity follows from the exact finite-field sums in the defining nets. -/
theorem FieldOfNorms.add_comm [IsAPF K L] (α β : FieldOfNorms K L) :
    FieldOfNorms.add K L α β = FieldOfNorms.add K L β α := by
  symm
  apply eq_fieldOfNormsAdd_of_tendsto K L α β
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E α β = normSumNet K L E β α := by
    funext F
    simp only [normSumNet, _root_.add_comm]
  rw [heq]
  exact tendsto_normSumNet_fieldOfNormsAdd K L β α E

/-- The original zero is the left identity for the actual field of norms addition. -/
theorem FieldOfNorms.add_zero_left [IsAPF K L] (α : FieldOfNorms K L) :
    FieldOfNorms.add K L 0 α = α := by
  symm
  apply eq_fieldOfNormsAdd_of_tendsto K L 0 α α
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E 0 α = fun _ => FieldOfNorms.coord K L E α :=
    funext (normSumNet_zero_left K L E α)
  rw [heq]
  exact tendsto_const_nhds

/-- The original zero is the right identity for the actual field of norms addition. -/
theorem FieldOfNorms.add_zero_right [IsAPF K L] (α : FieldOfNorms K L) :
    FieldOfNorms.add K L α 0 = α := by
  rw [FieldOfNorms.add_comm, FieldOfNorms.add_zero_left]

/-- Exact norm multiplicativity gives distributivity of the original
multiplication over the actual field of norms addition. -/
theorem mul_fieldOfNormsAdd [IsAPF K L] (δ α β : FieldOfNorms K L) :
    δ * FieldOfNorms.add K L α β =
      FieldOfNorms.add K L (δ * α) (δ * β) := by
  apply eq_fieldOfNormsAdd_of_tendsto K L (δ * α) (δ * β)
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  rw [map_mul]
  simpa only [← normSumNet_mul_left] using
    (tendsto_normSumNet_fieldOfNormsAdd K L α β E).const_mul (FieldOfNorms.coord K L E δ)

/-- Integral inputs have an integral actual sum, on the same stable valuation. -/
theorem FieldOfNorms.valuation_fieldOfNormsAdd_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    FieldOfNorms.valuation K L (FieldOfNorms.add K L α β) ≤ 1 := by
  rw [FieldOfNorms.valuation_le_one_iff K L]
  intro E
  exact normSumNet_limit_mem_of_valuation_le_one K L α β hα hβ E _
    (tendsto_normSumNet_fieldOfNormsAdd K L α β E)

/-- The actual sum of integral inputs has the proved eventual coordinate
approximation at every finite precision. -/
theorem FieldOfNorms.add_sub_mem_of_valuation_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∀ s : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
        FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, _⟩ := existsUnique_fieldOfNorms_integral_add K L α β hα hβ
  have heq := eq_fieldOfNormsAdd_of_tendsto K L α β γ hγ.2.1
  simpa only [heq] using hγ.2.2

end FontaineWintenberger
