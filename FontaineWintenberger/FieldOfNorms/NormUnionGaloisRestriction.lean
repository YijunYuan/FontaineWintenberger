/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionGaloisRestrictionFun

/-!
# The original base automorphism selected by a norm-union automorphism

The checked subgroup membership theorem supplies an actual original base
automorphism and its exact square on the original norm field.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : IntermediateField K (SeparableClosure K))
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => NormLimit K L
local notation "U" => SeparableNormUnion K L Ω p
local notation "ι" => separableNormUnionBaseHom K L Ω p
local notation "ρ" => normLimitAut K L p

local notation "S" => normUnionGaloisSubgroup K L p

local notation "f" => normUnionGaloisRestrictionFun K L p

/-- The actual restriction preserves multiplication in the canonical
homomorphism domain structure. -/
theorem normUnionGaloisRestrictionFun_mul :
    let : Mul S := (inferInstance : MulOne S).toMul
    ∀ β γ : S, f (β * γ) = f β * f γ := by
  let : Mul S := (inferInstance : MulOne S).toMul
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  dsimp only
  intro β γ
  apply normUnionGaloisSubgroup_base_unique K L p
    (β * γ).val (f (β * γ)) (f β * f γ)
    (normUnionGaloisRestrictionFun_base K L p (β * γ))
  intro x
  calc
    (β * γ).val (ι x) = β.val (γ.val (ι x)) :=
      congrArg (fun a => a (ι x)) ((Subgroup.subtype S).map_mul β γ)
    _ = ι (ρ (f β) (ρ (f γ) x)) :=
      (congrArg β.val (normUnionGaloisRestrictionFun_base K L p γ x)).trans
        (normUnionGaloisRestrictionFun_base K L p β (ρ (f γ) x))
    _ = ι (ρ (f β * f γ) x) := by
      rw [(ρ).map_mul]
      rfl

/-- The actual original base restriction, as a group homomorphism. -/
def normUnionGaloisRestriction : S →* (L ≃ₐ[K] L) :=
  MonoidHom.mk' f (normUnionGaloisRestrictionFun_mul K L p)

local notation "r" => normUnionGaloisRestriction K L p

/-- The restriction retains the actual base square on every element. -/
theorem normUnionGaloisRestriction_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) = ι (ρ (r β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact normUnionGaloisRestrictionFun_base K L p β x

/-- The original automorphism is determined by its genuine base square. -/
theorem normUnionGaloisRestriction_eq_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (σ : L ≃ₐ[K] L), r β = σ ↔
      ∀ x : X, β.val (ι x) = ι (ρ σ x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β σ
  constructor
  · rintro rfl
    exact normUnionGaloisRestriction_base K L p β
  · intro hσ
    exact normUnionGaloisSubgroup_base_unique K L p β.val (r β) σ
      (normUnionGaloisRestriction_base K L p β) hσ

/-- The kernel consists exactly of automorphisms fixing the actual base pointwise. -/
theorem mem_normUnionGaloisRestriction_ker_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β : S, β ∈ (r).ker ↔ ∀ x : X, β.val (ι x) = ι x := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  rw [MonoidHom.mem_ker, normUnionGaloisRestriction_eq_iff]
  simp only [map_one, RingAut.one_apply]

end FontaineWintenberger
