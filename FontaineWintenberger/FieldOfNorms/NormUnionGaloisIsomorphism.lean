/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionGaloisEquiv
public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteAction

/-!
# The original ambient Galois group of the relative field of norms

The actual same-union action identifies the original absolute Galois group
with the actual subgroup whose base restriction is an original norm-field action.
The restriction square and relative kernel comparison are retained literally.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L
local notation "S" => RelFieldOfNorms.galoisSubgroup K L
local notation "A" => RelFieldOfNorms.absoluteAut K L
local notation "r" => RelFieldOfNorms.galoisRestriction K L
local notation "κ" => RelFieldOfNorms.galoisKernelEquiv K L

/-- The actual ambient action takes values in the original semilinear subgroup. -/
def RelFieldOfNorms.ambientGaloisHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (Ω ≃ₐ[K] Ω) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  refine (A).codRestrict S ?_
  intro σ
  apply (mem_relFieldOfNormsGaloisSubgroup K L (A σ)).mpr
  refine ⟨AlgEquiv.restrictNormalHom L σ, ?_⟩
  intro x
  simpa only [FieldOfNorms.absoluteAut_apply] using
    (RelFieldOfNorms.absoluteAut_base K L σ x)

local notation "Φ" => RelFieldOfNorms.ambientGaloisHom K L

/-- The subgroup-valued homomorphism retains the original action on every union element. -/
theorem RelFieldOfNorms.ambientGaloisHom_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U), (Φ σ).val z = A σ z := by
  intro σ z
  rfl

/-- Its actual base restriction is ordinary Galois restriction. -/
theorem RelFieldOfNorms.ambientGaloisHom_restriction :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ σ : Ω ≃ₐ[K] Ω, r (Φ σ) = AlgEquiv.restrictNormalHom L σ := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro σ
  apply (RelFieldOfNorms.galoisRestriction_eq_iff K L _ _).mpr
  intro x
  change A σ (ι x) = ι (FieldOfNorms.absoluteAut K L σ x)
  exact RelFieldOfNorms.absoluteAut_base K L σ x

/-- On the original relative Galois subgroup it is exactly the proved kernel correspondence. -/
theorem RelFieldOfNorms.ambientGaloisHom_relative :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (τ :
      letI : Semiring Ω :=
        @CommSemiring.toSemiring Ω
          (@Semifield.toCommSemiring Ω
            (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
      Ω ≃ₐ[L] Ω),
      Φ (τ.restrictScalars K) = (κ τ).val := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro τ
  apply Subtype.ext
  apply RingEquiv.ext
  intro z
  change A (τ.restrictScalars K) z = (κ τ).val.val z
  exact (RelFieldOfNorms.absoluteAut_restrictScalars K L τ z).trans
    (RelFieldOfNorms.galoisKernelEquiv_apply K L τ z).symm

/-- The actual ambient action is faithful on the same union. -/
theorem RelFieldOfNorms.ambientGaloisHom_injective :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    Function.Injective (Φ) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  apply (injective_iff_map_eq_one (Φ)).mpr
  intro σ hσ
  have hr : AlgEquiv.restrictNormalHom L σ = 1 := by
    rw [← RelFieldOfNorms.ambientGaloisHom_restriction K L σ, hσ, map_one]
  have hfix : σ ∈ L.fixingSubgroup := by
    rw [← L.restrictNormalHom_ker]
    exact hr
  let τ := L.fixingSubgroupEquiv ⟨σ, hfix⟩
  have ht : τ.restrictScalars K = σ := by
    apply AlgEquiv.ext
    intro z
    rfl
  have hk : (κ τ).val = 1 :=
    (RelFieldOfNorms.ambientGaloisHom_relative K L τ).symm.trans
      ((congrArg (Φ) ht).trans hσ)
  have hk_mem : κ τ = 1 := Subtype.ext hk
  have hτ : τ = 1 := (κ).injective (hk_mem.trans (κ).map_one.symm)
  have hτK : τ.restrictScalars K = 1 := by
    rw [hτ]
    rfl
  exact ht.symm.trans hτK

/-- Every automorphism with original base restriction is an actual ambient Galois action. -/
theorem RelFieldOfNorms.ambientGaloisHom_surjective :
    Function.Surjective (RelFieldOfNorms.ambientGaloisHom K L) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := L) Ω (r β)
  let δ : S := β * (Φ σ)⁻¹
  have hδ : δ ∈ (r).ker := by
    change r δ = 1
    simp only [δ, map_mul, map_inv,
      RelFieldOfNorms.ambientGaloisHom_restriction K L, hσ, mul_inv_cancel]
  let d : (r).ker := ⟨δ, hδ⟩
  obtain ⟨τ, hτ⟩ := (κ).surjective d
  have hrel : Φ (τ.restrictScalars K) = δ :=
    (RelFieldOfNorms.ambientGaloisHom_relative K L τ).trans
      (congrArg Subtype.val hτ)
  refine ⟨τ.restrictScalars K * σ, ?_⟩
  exact ((Φ).map_mul (τ.restrictScalars K) σ).trans
    ((congrArg (fun z : S => z * Φ σ) hrel).trans (inv_mul_cancel_right β (Φ σ)))

/-- Wintenberger’s actual ambient Galois group isomorphism for the original union. -/
def RelFieldOfNorms.ambientGaloisEquiv :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (Ω ≃ₐ[K] Ω) ≃* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact MulEquiv.ofBijective (Φ)
    ⟨RelFieldOfNorms.ambientGaloisHom_injective K L,
      RelFieldOfNorms.ambientGaloisHom_surjective K L⟩

/-- The final group isomorphism is the literal original same-union action. -/
theorem RelFieldOfNorms.ambientGaloisEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U),
      (RelFieldOfNorms.ambientGaloisEquiv K L σ).val z = A σ z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro σ z
  rfl

end FontaineWintenberger
