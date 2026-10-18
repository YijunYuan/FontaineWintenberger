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

local notation "f" => RelFieldOfNorms.galoisRestrictionFun K L

/-- The actual restriction preserves multiplication in the canonical
homomorphism domain structure. -/
theorem RelFieldOfNorms.galoisRestrictionFun_mul :
    let : Mul S := (inferInstance : MulOne S).toMul
    ∀ β γ : S, f (β * γ) = f β * f γ := by
  let : Mul S := (inferInstance : MulOne S).toMul
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  dsimp only
  intro β γ
  apply RelFieldOfNorms.galoisSubgroup_base_unique K L
    (β * γ).val (f (β * γ)) (f β * f γ)
    (RelFieldOfNorms.galoisRestrictionFun_base K L (β * γ))
  intro x
  calc
    (β * γ).val (ι x) = β.val (γ.val (ι x)) :=
      congrArg (fun a => a (ι x)) ((Subgroup.subtype S).map_mul β γ)
    _ = ι (ρ (f β) (ρ (f γ) x)) :=
      (congrArg β.val (RelFieldOfNorms.galoisRestrictionFun_base K L γ x)).trans
        (RelFieldOfNorms.galoisRestrictionFun_base K L β (ρ (f γ) x))
    _ = ι (ρ (f β * f γ) x) := by
      rw [(ρ).map_mul]
      rfl

/-- The actual original base restriction, as a group homomorphism. -/
def RelFieldOfNorms.galoisRestriction : S →* (L ≃ₐ[K] L) :=
  MonoidHom.mk' f (RelFieldOfNorms.galoisRestrictionFun_mul K L)

local notation "r" => RelFieldOfNorms.galoisRestriction K L

/-- The restriction retains the actual base square on every element. -/
theorem RelFieldOfNorms.galoisRestriction_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) = ι (ρ (r β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact RelFieldOfNorms.galoisRestrictionFun_base K L β x

/-- The original automorphism is determined by its genuine base square. -/
theorem RelFieldOfNorms.galoisRestriction_eq_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (σ : L ≃ₐ[K] L), r β = σ ↔
      ∀ x : X, β.val (ι x) = ι (ρ σ x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β σ
  constructor
  · rintro rfl
    exact RelFieldOfNorms.galoisRestriction_base K L β
  · intro hσ
    exact RelFieldOfNorms.galoisSubgroup_base_unique K L β.val (r β) σ
      (RelFieldOfNorms.galoisRestriction_base K L β) hσ

/-- The kernel consists exactly of automorphisms fixing the actual base pointwise. -/
theorem mem_relFieldOfNormsGaloisRestriction_ker_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β : S, β ∈ (r).ker ↔ ∀ x : X, β.val (ι x) = ι x := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  rw [MonoidHom.mem_ker, RelFieldOfNorms.galoisRestriction_eq_iff]
  simp only [map_one, RingAut.one_apply]

end FontaineWintenberger
