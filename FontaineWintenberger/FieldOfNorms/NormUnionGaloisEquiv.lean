/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionGaloisRestriction

/-!
# Relative automorphisms of the original norm union

Forgetting the base algebra gives a canonical homomorphism into the original
norm-union target subgroup.

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

local notation "r" => RelFieldOfNorms.galoisRestriction K L

/-- Forgetting the base algebra gives an actual member of the source target. -/
def RelFieldOfNorms.galoisRelativeHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (U ≃ₐ[X] U) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact
    (MulSemiringAction.toRingEquiv (U ≃ₐ[X] U) U).codRestrict S fun β => by
      apply (mem_relFieldOfNormsGaloisSubgroup K L β.toRingEquiv).mpr
      refine ⟨1, ?_⟩
      intro x
      change β (ι x) = ι ((ρ) 1 x)
      rw [(ρ).map_one]
      exact β.commutes x

/-- The canonical forgetful map is injective, retaining the actual ring automorphism. -/
theorem RelFieldOfNorms.galoisRelativeHom_injective :
    Function.Injective (RelFieldOfNorms.galoisRelativeHom K L) := by
  intro β γ h
  exact DFunLike.ext β γ fun z => congrArg (fun η : S => η.val z) h

/-- Actual base-algebra automorphisms have trivial original base restriction. -/
theorem RelFieldOfNorms.galoisRelativeHom_mem_ker :
    ∀ β, RelFieldOfNorms.galoisRelativeHom K L β ∈ (r).ker := by
  intro β
  apply (mem_relFieldOfNormsGaloisRestriction_ker_iff K L _).mpr
  cases β
  assumption

/-- Every genuine kernel element is induced by a base-algebra automorphism. -/
theorem RelFieldOfNorms.galoisRelativeHom_surjective_ker :
    Function.Surjective
      ((RelFieldOfNorms.galoisRelativeHom K L).codRestrict (r).ker
        (RelFieldOfNorms.galoisRelativeHom_mem_ker K L)) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  have hfix := (mem_relFieldOfNormsGaloisRestriction_ker_iff K L β.val).mp
    β.property
  refine ⟨{ β.val.val with commutes' := hfix }, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  rfl

/-- The relative algebra automorphism group is precisely the genuine kernel. -/
def RelFieldOfNorms.galoisRelativeKernelEquiv :=
  MulEquiv.ofBijective
    ((RelFieldOfNorms.galoisRelativeHom K L).codRestrict (r).ker
      (RelFieldOfNorms.galoisRelativeHom_mem_ker K L))
    ⟨(MonoidHom.injective_codRestrict
        (RelFieldOfNorms.galoisRelativeHom K L) (r).ker
        (RelFieldOfNorms.galoisRelativeHom_mem_ker K L)).mpr
        (RelFieldOfNorms.galoisRelativeHom_injective K L),
      RelFieldOfNorms.galoisRelativeHom_surjective_ker K L⟩

/-- The canonical kernel comparison retains the same underlying automorphism. -/
theorem RelFieldOfNorms.galoisRelativeKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β, (RelFieldOfNorms.galoisRelativeKernelEquiv K L β).val.val =
      β.toRingEquiv := by
  intro β
  apply DFunLike.ext
  intro z
  rfl

/-- The original relative Galois group identifies with that same actual kernel. -/
def RelFieldOfNorms.galoisKernelEquiv :=
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  (RelFieldOfNorms.autEquiv K L Ω).trans
    (RelFieldOfNorms.galoisRelativeKernelEquiv K L)

/-- The relative-kernel equivalence is the original union map on every element. -/
theorem RelFieldOfNorms.galoisKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI : Semiring Ω :=
      @CommSemiring.toSemiring Ω
        (@Semifield.toCommSemiring Ω
          (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
    ∀ σ z, (RelFieldOfNorms.galoisKernelEquiv K L σ).val.val z =
      RelFieldOfNorms.map K L Ω Ω σ.toAlgHom z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  intro σ z
  have h := RelFieldOfNorms.galoisRelativeKernelEquiv_apply K L
    (RelFieldOfNorms.autEquiv K L Ω σ)
  exact (DFunLike.congr_fun h z).trans
    (RelFieldOfNorms.autEquiv_apply K L Ω σ z)

end FontaineWintenberger
