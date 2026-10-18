/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteSums

/-!
# The original norm limit as a commutative semiring

The named structure preserves its original multiplicative data and uses the
addition already constructed from original norm limits.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual norm-limit addition and original multiplication give a named
commutative semiring, preserving the original multiplicative structure. -/
@[instance_reducible]
def normLimitCommSemiring [IsAPF K L] : CommSemiring (NormLimit K L) := by
  letI := normLimitAddCommMonoid K L
  exact {
    (inferInstance : CommMonoidWithZero (NormLimit K L)), normLimitAddCommMonoid K L with
    left_distrib := mul_normLimitAdd K L
    right_distrib := fun a b c => by
      change normLimitAdd K L a b * c =
        normLimitAdd K L (a * c) (b * c)
      rw [mul_comm _ c, mul_normLimitAdd, mul_comm c a, mul_comm c b]
    natCast := fun n => n • (1 : NormLimit K L)
    natCast_zero := zero_nsmul _
    natCast_succ := fun n => AddMonoid.nsmul_succ n _ }

end FontaineWintenberger
