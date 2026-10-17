/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

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

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : IntermediateField K (SeparableClosure K))
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

local notation "Ω" => SeparableClosure K
local notation "X" => NormLimit K L
local notation "U" => SeparableNormUnion K L Ω p hL hInfinite
local notation "ι" => separableNormUnionBaseHom K L Ω p hL hInfinite
local notation "ρ" => normLimitAut K p hL hInfinite

local notation "S" => normUnionGaloisSubgroup K L p hL hInfinite

/-- The original automorphism supplied by the actual subgroup membership theorem. -/
def normUnionGaloisRestrictionFun (β : S) : L ≃ₐ[K] L :=
  Classical.choose ((mem_normUnionGaloisSubgroup K L p hL hInfinite β.val).mp β.property)

/-- The chosen original automorphism has the actual base square on every element. -/
theorem normUnionGaloisRestrictionFun_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) =
      ι (ρ (normUnionGaloisRestrictionFun K L p hL hInfinite β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact Classical.choose_spec
    ((mem_normUnionGaloisSubgroup K L p hL hInfinite β.val).mp β.property) x

end FontaineWintenberger
