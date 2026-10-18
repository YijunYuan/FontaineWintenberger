/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteSums

/-!
# The original field of norms as a commutative semiring

The named structure preserves its original multiplicative data and uses the
addition already constructed from original fields of norms.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual field of norms addition and original multiplication give a named
commutative semiring, preserving the original multiplicative structure. -/
instance (priority := low) FieldOfNorms.instCommSemiring [IsAPF K L] : CommSemiring (FieldOfNorms K
    L) :=
  {
    (inferInstance : CommMonoidWithZero (FieldOfNorms K L)), FieldOfNorms.instAddCommMonoid K L with
    left_distrib := mul_fieldOfNormsAdd K L
    right_distrib := fun a b c => by
      change FieldOfNorms.add K L a b * c =
        FieldOfNorms.add K L (a * c) (b * c)
      rw [mul_comm _ c, mul_fieldOfNormsAdd, mul_comm c a, mul_comm c b]
    natCast := fun n => n • (1 : FieldOfNorms K L)
    natCast_zero := zero_nsmul _
    natCast_succ := fun n => AddMonoid.nsmul_succ n _ }

end FontaineWintenberger
