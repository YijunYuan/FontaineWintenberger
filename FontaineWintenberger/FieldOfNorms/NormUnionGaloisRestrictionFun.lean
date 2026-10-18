/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionGaloisAction

/-!
# The original base automorphism selected by a norm-union automorphism

The checked subgroup membership theorem supplies an actual original base
automorphism and its exact square on the original norm field.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K))
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L

local notation "S" => RelFieldOfNorms.galoisSubgroup K L

/-- The original automorphism supplied by the actual subgroup membership theorem. -/
def RelFieldOfNorms.galoisRestrictionFun (β : S) : L ≃ₐ[K] L :=
  Classical.choose ((mem_relFieldOfNormsGaloisSubgroup K L β.val).mp β.property)

/-- The chosen original automorphism has the actual base square on every element. -/
theorem RelFieldOfNorms.galoisRestrictionFun_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) =
      ι (ρ (RelFieldOfNorms.galoisRestrictionFun K L β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact Classical.choose_spec
    ((mem_relFieldOfNormsGaloisSubgroup K L β.val).mp β.property) x

end FontaineWintenberger
