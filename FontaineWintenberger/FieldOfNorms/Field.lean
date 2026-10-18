/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Semiring
public import FontaineWintenberger.FieldOfNorms.PrimeValuation
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The field structure on the same original norm-limit carrier

Actual ramification divergence kills the residue prime. The resulting
additive inverses complete the existing multiplication to a field.
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

/-- The residue prime vanishes in the actual norm-limit semiring, by
coordinate approximation and actual ramification divergence. -/
theorem normLimit_natCast_prime_eq_zero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    letI := normLimitCommSemiring K L p
    (p : NormLimit K L) = 0 := by
  let := normLimitCommSemiring K L p
  apply normLimit_ext_of_eventually_sub_mem K L p
  intro n
  obtain ⟨T₁, hT₁⟩ := normLimitEval_nsmul_sub_mem K L p p 1 n
  obtain ⟨T₂, hT₂⟩ := IsAPF.exists_finiteLayer_natCast_mem_image_maximalIdeal_pow
    K L p n
  refine ⟨FiniteLayer.sup T₁ T₂, fun E hE => ?_⟩
  obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteLayer.le_sup_left T₁ T₂).trans hE)
  obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteLayer.le_sup_right T₁ T₂).trans hE)
  refine ⟨d₁ + d₂, Ideal.add_mem _ hd₁ hd₂, ?_⟩
  change (d₁ : E.val) + (d₂ : E.val) = _
  simp only [map_one, nsmul_eq_mul, mul_one] at heq₁
  rw [map_zero, sub_zero]
  change (d₁ : E.val) + (d₂ : E.val) = normLimitEval K L E (p • (1 : NormLimit K L))
  linear_combination heq₁ + heq₂

/-- The actual (p-1)-fold sum is an additive inverse, including p=2. -/
theorem normLimit_pred_nsmul_add_eq_zero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (α : NormLimit K L) :
    letI := normLimitCommSemiring K L p
    (p - 1) • α + α = 0 := by
  let := normLimitCommSemiring K L p
  rw [← AddMonoid.nsmul_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [nsmul_eq_mul, normLimit_natCast_prime_eq_zero K L p, zero_mul]

/-- The original multiplicative norm limit is a field under the actual
addition. Every additive inverse is its actual (p-1)-fold sum. -/
@[instance_reducible]
def normLimitField [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Field (NormLimit K L) := by
  letI := normLimitCommSemiring K L p
  letI : Neg (NormLimit K L) := ⟨fun α => (p - 1) • α⟩
  letI : CommRing (NormLimit K L) := CommRing.ofMinimalAxioms
    add_assoc zero_add (normLimit_pred_nsmul_add_eq_zero K L p)
    mul_assoc mul_comm one_mul left_distrib
  exact {
    (inferInstance : CommRing (NormLimit K L)),
    (inferInstance : CommGroupWithZero (NormLimit K L)) with
    nnqsmul := _
    qsmul := _ }

/-- The actual field has residue characteristic p, with no finiteness
assumption on the perfect residue field of the original base. -/
theorem normLimitField_charP [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    letI := normLimitField K L p
    CharP (NormLimit K L) p := by
  let := normLimitField K L p
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have h := normLimit_natCast_prime_eq_zero K L p
  change p • (1 : NormLimit K L) = 0 at h
  simpa only [nsmul_one] using h

/-- The field addition is definitionally the actual norm-limit sum operation. -/
@[simp]
theorem normLimitField_add [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (α β : NormLimit K L) :
    letI := normLimitField K L p
    α + β = normLimitAdd K L p α β := rfl

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- The entire original commutative group with zero is retained definitionally
by the field structure, including multiplication, inversion and division. -/
theorem normLimitField_toCommGroupWithZero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    let original : CommGroupWithZero (NormLimit K L) := inferInstance
    letI := normLimitField K L p
    (inferInstance : CommGroupWithZero (NormLimit K L)) = original := rfl

end FontaineWintenberger
