/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Convergence

/-!
# The actual norm-limit addition operation

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
theorem normSumNet_mul_left (E : FiniteLayer K L) (δ α β : NormLimit K L)
    (F : Set.Ici E) :
    normSumNet K L E (δ * α) (δ * β) F =
      normLimitEval K L E δ * normSumNet K L E α β F := by
  simp only [normSumNet, map_mul]
  rw [← mul_add, map_mul, normLimitEval_norm K L E F.val F.property δ]

end ScalarCovariance

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

include p

/-- Every pair of actual norm-compatible families has convergent original
norm-sum nets; existing nonzero families themselves provide the scaling. -/
theorem exists_tendsto_normSumNet (hL : IsAPF K L) (α β : NormLimit K L) :
    ∀ E : FiniteLayer K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  by_cases hα : α = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨normLimitEval K L E β, ?_⟩
    have heq : normSumNet K L E α β = fun _ => normLimitEval K L E β := by
      funext F
      simp only [hα, normSumNet_zero_left]
    rw [heq]
    exact tendsto_const_nhds
  by_cases hβ : β = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨normLimitEval K L E α, ?_⟩
    have heq : normSumNet K L E α β = fun _ => normLimitEval K L E α := by
      funext F
      simp only [hβ, normSumNet_zero_right]
    rw [heq]
    exact tendsto_const_nhds
  let w := normLimitValuation K L hL
  have hαw : w α ≠ 0 := fun h => hα ((normLimitValuation_eq_zero_iff K L hL α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((normLimitValuation_eq_zero_iff K L hL β).mp h)
  have hscale : ∃ δ : NormLimit K L, δ ≠ 0 ∧ w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
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
    K L p hL (α / δ) (β / δ) ha hb E
  refine ⟨normLimitEval K L E δ * z, ?_⟩
  simpa only [← normSumNet_mul_left, hδα, hδβ] using
    hz.const_mul (normLimitEval K L E δ)

/-- The actual original norm limit contains the unique sum family of any
pair of its elements, characterized by the original norm-sum limits. -/
theorem existsUnique_normLimit_add (hL : IsAPF K L) (α β : NormLimit K L) :
    ∃! γ : NormLimit K L, ∀ E : FiniteLayer K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (normLimitEval K L E γ)) :=
  existsUnique_normLimit_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet K L p hL α β)

/-- Addition on the same original multiplicative norm-limit carrier,
characterized by the actual norm-sum limits at every finite base. -/
def normLimitAdd (hL : IsAPF K L) (α β : NormLimit K L) : NormLimit K L :=
  (existsUnique_normLimit_add K L p hL α β).choose

/-- Every original coordinate of the actual sum is its original norm-sum limit. -/
theorem tendsto_normSumNet_normLimitAdd (hL : IsAPF K L) (α β : NormLimit K L)
    (E : FiniteLayer K L) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    Tendsto (normSumNet K L E α β) atTop
      (nhds (normLimitEval K L E (normLimitAdd K L p hL α β))) :=
  (existsUnique_normLimit_add K L p hL α β).choose_spec.1 E

/-- The original norm-sum limits uniquely characterize the same sum operation. -/
theorem eq_normLimitAdd_of_tendsto (hL : IsAPF K L) (α β γ : NormLimit K L)
    (hγ : ∀ E : FiniteLayer K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (normLimitEval K L E γ))) :
    γ = normLimitAdd K L p hL α β :=
  (existsUnique_normLimit_add K L p hL α β).choose_spec.2 γ hγ

/-- Commutativity follows from the exact finite-field sums in the defining nets. -/
theorem normLimitAdd_comm (hL : IsAPF K L) (α β : NormLimit K L) :
    normLimitAdd K L p hL α β = normLimitAdd K L p hL β α := by
  symm
  apply eq_normLimitAdd_of_tendsto K L p hL α β
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E α β = normSumNet K L E β α := by
    funext F
    simp only [normSumNet, add_comm]
  rw [heq]
  exact tendsto_normSumNet_normLimitAdd K L p hL β α E

/-- The original zero is the left identity for the actual norm-limit addition. -/
theorem normLimitAdd_zero_left (hL : IsAPF K L) (α : NormLimit K L) :
    normLimitAdd K L p hL 0 α = α := by
  symm
  apply eq_normLimitAdd_of_tendsto K L p hL 0 α α
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E 0 α = fun _ => normLimitEval K L E α :=
    funext (normSumNet_zero_left K L E α)
  rw [heq]
  exact tendsto_const_nhds

/-- The original zero is the right identity for the actual norm-limit addition. -/
theorem normLimitAdd_zero_right (hL : IsAPF K L) (α : NormLimit K L) :
    normLimitAdd K L p hL α 0 = α := by
  rw [normLimitAdd_comm, normLimitAdd_zero_left]

/-- Exact norm multiplicativity gives distributivity of the original
multiplication over the actual norm-limit addition. -/
theorem mul_normLimitAdd (hL : IsAPF K L) (δ α β : NormLimit K L) :
    δ * normLimitAdd K L p hL α β =
      normLimitAdd K L p hL (δ * α) (δ * β) := by
  apply eq_normLimitAdd_of_tendsto K L p hL (δ * α) (δ * β)
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  rw [map_mul]
  simpa only [← normSumNet_mul_left] using
    (tendsto_normSumNet_normLimitAdd K L p hL α β E).const_mul (normLimitEval K L E δ)

/-- Integral inputs have an integral actual sum, on the same stable valuation. -/
theorem normLimitValuation_normLimitAdd_le_one (hL : IsAPF K L) (α β : NormLimit K L)
    (hα : normLimitValuation K L hL α ≤ 1) (hβ : normLimitValuation K L hL β ≤ 1) :
    normLimitValuation K L hL (normLimitAdd K L p hL α β) ≤ 1 := by
  rw [normLimitValuation_le_one_iff K L hL]
  intro E
  exact normSumNet_limit_mem_of_valuation_le_one K L hL α β hα hβ E _
    (tendsto_normSumNet_normLimitAdd K L p hL α β E)

/-- The actual sum of integral inputs has the proved eventual coordinate
approximation at every finite precision. -/
theorem normLimitAdd_sub_mem_of_valuation_le_one (hL : IsAPF K L) (α β : NormLimit K L)
    (hα : normLimitValuation K L hL α ≤ 1) (hβ : normLimitValuation K L hL β ≤ 1) :
    ∀ s : ℕ, ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      normLimitEval K L E (normLimitAdd K L p hL α β) -
        normLimitEval K L E α - normLimitEval K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, _⟩ := existsUnique_normLimit_integral_add K L p hL α β hα hβ
  have heq := eq_normLimitAdd_of_tendsto K L p hL α β γ hγ.2.1
  simpa only [heq] using hγ.2.2

end FontaineWintenberger
