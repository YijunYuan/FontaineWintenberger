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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The residue prime vanishes in the actual norm-limit semiring, by
coordinate approximation and actual ramification divergence. -/
theorem normLimit_natCast_prime_eq_zero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    letI := normLimitCommSemiring K L
    (p : NormLimit K L) = 0 := by
  let := normLimitCommSemiring K L
  apply normLimit_ext_of_eventually_sub_mem K L
  intro n
  obtain ⟨T₁, hT₁⟩ := normLimitEval_nsmul_sub_mem K L p 1 n
  obtain ⟨T₂, hT₂⟩ := IsAPF.exists_finiteLayer_natCast_mem_image_maximalIdeal_pow
    K L n
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
    (p - 1) • α + α = 0 := by
  rw [← AddMonoid.nsmul_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le]
  rw [nsmul_eq_mul, normLimit_natCast_prime_eq_zero K L, zero_mul]

/-- The original multiplicative norm limit is a field under the actual
addition. Every additive inverse is its actual (p-1)-fold sum. -/
instance normLimitNeg [IsAPF K L] [Fact (¬ Module.Finite K L)] : Neg (NormLimit K L) :=
  ⟨fun α => (p - 1) • α⟩

instance normLimitField [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Field (NormLimit K L) :=
  { normLimitCommSemiring K L, NormLimit.instCommGroupWithZero K L, normLimitNeg K L with
    neg_add_cancel := normLimit_pred_nsmul_add_eq_zero K L
    zsmul := zsmulRec
    nnqsmul := _
    qsmul := _ }

/-- The field structure extends the semiring structure definitionally: there is a single
addition, `natCast` and `nsmul` on the carrier. -/
theorem normLimitField_toCommSemiring [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    @Semifield.toCommSemiring _ (normLimitField K L).toSemifield = normLimitCommSemiring K L :=
  rfl

/-- The actual field has residue characteristic p, with no finiteness
assumption on the perfect residue field of the original base. -/
instance normLimitField_charP [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    CharP (NormLimit K L) p := by
  have h := normLimit_natCast_prime_eq_zero K L
  change p • (1 : NormLimit K L) = 0 at h
  exact (CharP.charP_iff_prime_eq_zero (R := NormLimit K L) (Fact.out : Nat.Prime p)).mpr
    (by simpa only [nsmul_one] using h)

/-- The field addition is definitionally the actual norm-limit sum operation. -/
@[simp]
theorem normLimitField_add [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (α β : NormLimit K L) :
    α + β = normLimitAdd K L α β := rfl

/-- The entire original commutative group with zero is retained definitionally
by the field structure, including multiplication, inversion and division. -/
theorem normLimitField_toCommGroupWithZero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    @Semifield.toCommGroupWithZero _ (normLimitField K L).toSemifield =
      NormLimit.instCommGroupWithZero K L := rfl

end FontaineWintenberger
