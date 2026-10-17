/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.NormUnionGaloisEquiv
public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteAction

/-!
# The original ambient Galois group of the norm-field union

The actual same-union action identifies the original absolute Galois group
with the actual subgroup whose base restriction is an original norm-field action.
The restriction square and relative kernel comparison are retained literally.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
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
local notation "A" => separableNormUnionAbsoluteAut K L p hL hInfinite
local notation "r" => normUnionGaloisRestriction K L p hL hInfinite
local notation "κ" => normUnionGaloisKernelEquiv K L p hL hInfinite

/-- The actual ambient action takes values in the original semilinear subgroup. -/
def normUnionAmbientGaloisHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    (Ω ≃ₐ[K] Ω) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L Ω p hL hInfinite
  letI : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  letI : Group (RingAut U) := RingAut.instGroup U
  refine (A).codRestrict S ?_
  intro σ
  apply (mem_normUnionGaloisSubgroup K L p hL hInfinite (A σ)).mpr
  refine ⟨AlgEquiv.restrictNormalHom L σ, ?_⟩
  intro x
  simpa only [normLimitAbsoluteAut_apply] using
    (separableNormUnionAbsoluteAut_base K L p hL hInfinite σ x)

local notation "Φ" => normUnionAmbientGaloisHom K L p hL hInfinite

/-- The subgroup-valued homomorphism retains the original action on every union element. -/
theorem normUnionAmbientGaloisHom_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U), (Φ σ).val z = A σ z := by
  intro σ z
  rfl

/-- Its actual base restriction is ordinary Galois restriction. -/
theorem normUnionAmbientGaloisHom_restriction :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ σ : Ω ≃ₐ[K] Ω, r (Φ σ) = AlgEquiv.restrictNormalHom L σ := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro σ
  apply (normUnionGaloisRestriction_eq_iff K L p hL hInfinite _ _).mpr
  intro x
  change A σ (ι x) = ι (normLimitAbsoluteAut K L p hL hInfinite σ x)
  exact separableNormUnionAbsoluteAut_base K L p hL hInfinite σ x

/-- On the original relative Galois subgroup it is exactly the proved kernel correspondence. -/
theorem normUnionAmbientGaloisHom_relative :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ (τ :
      letI : Semiring Ω :=
        @CommSemiring.toSemiring Ω
          (@Semifield.toCommSemiring Ω
            (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
      Ω ≃ₐ[L] Ω),
      Φ (τ.restrictScalars K) = (κ τ).val := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro τ
  apply Subtype.ext
  apply RingEquiv.ext
  intro z
  change A (τ.restrictScalars K) z = (κ τ).val.val z
  exact (separableNormUnionAbsoluteAut_restrictScalars K L p hL hInfinite τ z).trans
    (normUnionGaloisKernelEquiv_apply K L p hL hInfinite τ z).symm

/-- The actual ambient action is faithful on the same union. -/
theorem normUnionAmbientGaloisHom_injective :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    Function.Injective (Φ) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  apply (injective_iff_map_eq_one (Φ)).mpr
  intro σ hσ
  have hr : AlgEquiv.restrictNormalHom L σ = 1 := by
    rw [← normUnionAmbientGaloisHom_restriction K L p hL hInfinite σ, hσ, map_one]
  have hfix : σ ∈ L.fixingSubgroup := by
    rw [← L.restrictNormalHom_ker]
    exact hr
  let τ := L.fixingSubgroupEquiv ⟨σ, hfix⟩
  have ht : τ.restrictScalars K = σ := by
    apply AlgEquiv.ext
    intro z
    rfl
  have hk : (κ τ).val = 1 :=
    (normUnionAmbientGaloisHom_relative K L p hL hInfinite τ).symm.trans
      ((congrArg (Φ) ht).trans hσ)
  have hk_mem : κ τ = 1 := Subtype.ext hk
  have hτ : τ = 1 := (κ).injective (hk_mem.trans (κ).map_one.symm)
  have hτK : τ.restrictScalars K = 1 := by
    rw [hτ]
    rfl
  exact ht.symm.trans hτK

/-- Every automorphism with original base restriction is an actual ambient Galois action. -/
theorem normUnionAmbientGaloisHom_surjective :
    Function.Surjective (normUnionAmbientGaloisHom K L p hL hInfinite) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro β
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := L) Ω (r β)
  let δ : S := β * (Φ σ)⁻¹
  have hδ : δ ∈ (r).ker := by
    change r δ = 1
    simp only [δ, map_mul, map_inv,
      normUnionAmbientGaloisHom_restriction K L p hL hInfinite, hσ, mul_inv_cancel]
  let d : (r).ker := ⟨δ, hδ⟩
  obtain ⟨τ, hτ⟩ := (κ).surjective d
  have hrel : Φ (τ.restrictScalars K) = δ :=
    (normUnionAmbientGaloisHom_relative K L p hL hInfinite τ).trans
      (congrArg Subtype.val hτ)
  refine ⟨τ.restrictScalars K * σ, ?_⟩
  exact ((Φ).map_mul (τ.restrictScalars K) σ).trans
    ((congrArg (fun z : S => z * Φ σ) hrel).trans (inv_mul_cancel_right β (Φ σ)))

/-- Wintenberger’s actual ambient Galois group isomorphism for the original union. -/
def normUnionAmbientGaloisEquiv :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    (Ω ≃ₐ[K] Ω) ≃* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L Ω p hL hInfinite
  letI : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  letI : Group (RingAut U) := RingAut.instGroup U
  exact MulEquiv.ofBijective (Φ)
    ⟨normUnionAmbientGaloisHom_injective K L p hL hInfinite,
      normUnionAmbientGaloisHom_surjective K L p hL hInfinite⟩

/-- The final group isomorphism is the literal original same-union action. -/
theorem normUnionAmbientGaloisEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p hL hInfinite N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
    letI : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U),
      (normUnionAmbientGaloisEquiv K L p hL hInfinite σ).val z = A σ z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p hL hInfinite N).toNonAssocSemiring
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p hL hInfinite).toNonAssocSemiring
  let : Mul U := (separableNormUnionField K L Ω p hL hInfinite).toMul
  let : Add U := (separableNormUnionField K L Ω p hL hInfinite).toAdd
  let : Group (RingAut U) := RingAut.instGroup U
  intro σ z
  rfl

end FontaineWintenberger
