/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.AbsoluteBaseAction
public import FontaineWintenberger.FieldOfNorms.NormUnionAutomorphisms

/-!
# The ambient Galois group and the original norm-union automorphism subgroup

The target is the actual subgroup of ring automorphisms of the same union
whose restriction to the actual base image is an original norm-field action.
Faithfulness gives a unique original base restriction; its kernel consists
of the actual base-algebra automorphisms.

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
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

local notation "Ω" => SeparableClosure K
local notation "X" => NormLimit K L
local notation "U" => SeparableNormUnion K L Ω p hL hInfinite
local notation "ι" => separableNormUnionBaseHom K L Ω p hL hInfinite
local notation "ρ" => normLimitAut K p hL hInfinite

/-- The literal source target, inside ring automorphisms of the same union. -/
def normUnionGaloisSubgroup :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    Subgroup (RingAut U) := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L Ω p hL hInfinite
  letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  letI : Group (RingAut U) := RingAut.instGroup U
  exact
    { carrier := {β | ∃ σ : L ≃ₐ[K] L, ∀ x : X, β (ι x) = ι (ρ σ x)}
      one_mem' := by
        refine ⟨1, ?_⟩
        intro x
        change ι x = ι ((ρ) 1 x)
        rw [(ρ).map_one]
        rfl
      mul_mem' := by
        rintro β γ ⟨σ, hσ⟩ ⟨τ, hτ⟩
        refine ⟨σ * τ, ?_⟩
        intro x
        change β (γ (ι x)) = ι (ρ (σ * τ) x)
        rw [hτ, hσ, map_mul]
        rfl
      inv_mem' := by
        rintro β ⟨σ, hσ⟩
        refine ⟨σ⁻¹, ?_⟩
        intro x
        apply β.injective
        change β (β.symm (ι x)) = β (ι (ρ (σ⁻¹) x))
        rw [β.apply_symm_apply, hσ, map_inv]
        change ι x = ι ((ρ σ) ((ρ σ).symm x))
        rw [RingEquiv.apply_symm_apply] }

/-- Membership means an actual commuting square with an original automorphism. -/
theorem mem_normUnionGaloisSubgroup :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ β : RingAut U, β ∈ normUnionGaloisSubgroup K L p hL hInfinite ↔
      ∃ σ : L ≃ₐ[K] L, ∀ x : X, β (ι x) = ι (ρ σ x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro β
  rfl

/-- The base square determines its original automorphism uniquely. -/
theorem normUnionGaloisSubgroup_base_unique :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ (β : RingAut U) (σ τ : L ≃ₐ[K] L),
      (∀ x : X, β (ι x) = ι (ρ σ x)) →
      (∀ x : X, β (ι x) = ι (ρ τ x)) → σ = τ := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro β σ τ hσ hτ
  apply normLimitAut_injective K L p hL hInfinite
  apply RingEquiv.ext
  intro x
  let : Nontrivial U := (separableNormUnionField K L Ω p hL hInfinite).toNontrivial
  apply (ι).injective
  exact (hσ x).symm.trans (hτ x)

/-- The existential square is exactly preservation of the actual base image
and membership of its transported restriction in the actual action image. -/
theorem mem_normUnionGaloisSubgroup_iff_stable_image :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ β : RingAut U, β ∈ normUnionGaloisSubgroup K L p hL hInfinite ↔
      β '' Set.range ι = Set.range ι ∧
        ∃ a ∈ (ρ).range, ∀ x : X, β (ι x) = ι (a x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro β
  rw [mem_normUnionGaloisSubgroup]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨?_, ρ σ, ⟨σ, rfl⟩, hσ⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨ρ σ x, (hσ x).symm⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨ι ((ρ σ).symm x), ⟨_, rfl⟩, ?_⟩
      rw [hσ, RingEquiv.apply_symm_apply]
  · rintro ⟨_, a, ⟨σ, rfl⟩, ha⟩
    exact ⟨σ, ha⟩

end FontaineWintenberger
