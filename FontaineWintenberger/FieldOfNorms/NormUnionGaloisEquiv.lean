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
local notation "X" => NormLimit K L
local notation "U" => SeparableNormUnion K L Ω
local notation "ι" => separableNormUnionBaseHom K L Ω
local notation "ρ" => normLimitAut K L

local notation "S" => normUnionGaloisSubgroup K L

local notation "r" => normUnionGaloisRestriction K L

/-- Forgetting the base algebra gives an actual member of the source target. -/
def normUnionGaloisRelativeHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω N).toNonAssocSemiring
    letI := normLimitField K L
    letI := separableNormUnionField K L Ω
    letI : Semiring U :=
      @CommSemiring.toSemiring U
        (@Semifield.toCommSemiring U
          (@Field.toSemifield U (separableNormUnionField K L Ω)))
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω).toMul
    letI : Add U := (separableNormUnionField K L Ω).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    letI := separableNormUnionAlgebra K L Ω
    (U ≃ₐ[X] U) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω N
  letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω N).toNonAssocSemiring
  letI := normLimitField K L
  letI := separableNormUnionField K L Ω
  letI : Semiring U :=
    @CommSemiring.toSemiring U
      (@Semifield.toCommSemiring U
        (@Field.toSemifield U (separableNormUnionField K L Ω)))
  letI : NonAssocSemiring U :=
    (separableNormUnionField K L Ω).toNonAssocSemiring
  letI : Mul U := (separableNormUnionField K L Ω).toMul
  letI : Add U := (separableNormUnionField K L Ω).toAdd
  letI : Group (RingAut U) := RingAut.instGroup U
  letI := separableNormUnionAlgebra K L Ω
  exact
    (MulSemiringAction.toRingEquiv (U ≃ₐ[X] U) U).codRestrict S fun β => by
      apply (mem_normUnionGaloisSubgroup K L β.toRingEquiv).mpr
      refine ⟨1, ?_⟩
      intro x
      change β (ι x) = ι ((ρ) 1 x)
      rw [(ρ).map_one]
      exact β.commutes x

/-- The canonical forgetful map is injective, retaining the actual ring automorphism. -/
theorem normUnionGaloisRelativeHom_injective :
    Function.Injective (normUnionGaloisRelativeHom K L) := by
  intro β γ h
  exact DFunLike.ext β γ fun z => congrArg (fun η : S => η.val z) h

/-- Actual base-algebra automorphisms have trivial original base restriction. -/
theorem normUnionGaloisRelativeHom_mem_ker :
    ∀ β, normUnionGaloisRelativeHom K L β ∈ (r).ker := by
  intro β
  apply (mem_normUnionGaloisRestriction_ker_iff K L _).mpr
  cases β
  assumption

/-- Every genuine kernel element is induced by a base-algebra automorphism. -/
theorem normUnionGaloisRelativeHom_surjective_ker :
    Function.Surjective
      ((normUnionGaloisRelativeHom K L).codRestrict (r).ker
        (normUnionGaloisRelativeHom_mem_ker K L)) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := normLimitField K L
  let : Semiring U :=
    @CommSemiring.toSemiring U
      (@Semifield.toCommSemiring U
        (@Field.toSemifield U (separableNormUnionField K L Ω)))
  let := separableNormUnionAlgebra K L Ω
  intro β
  have hfix := (mem_normUnionGaloisRestriction_ker_iff K L β.val).mp
    β.property
  refine ⟨{ β.val.val with commutes' := hfix }, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  rfl

/-- The relative algebra automorphism group is precisely the genuine kernel. -/
def normUnionGaloisRelativeKernelEquiv :=
  MulEquiv.ofBijective
    ((normUnionGaloisRelativeHom K L).codRestrict (r).ker
      (normUnionGaloisRelativeHom_mem_ker K L))
    ⟨(MonoidHom.injective_codRestrict
        (normUnionGaloisRelativeHom K L) (r).ker
        (normUnionGaloisRelativeHom_mem_ker K L)).mpr
        (normUnionGaloisRelativeHom_injective K L),
      normUnionGaloisRelativeHom_surjective_ker K L⟩

/-- The canonical kernel comparison retains the same underlying automorphism. -/
theorem normUnionGaloisRelativeKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L
    letI : Semiring U :=
      @CommSemiring.toSemiring U
        (@Semifield.toCommSemiring U
          (@Field.toSemifield U (separableNormUnionField K L Ω)))
    letI := separableNormUnionAlgebra K L Ω
    ∀ β, (normUnionGaloisRelativeKernelEquiv K L β).val.val =
      β.toRingEquiv := by
  let := normLimitField K L
  intro β
  apply DFunLike.ext
  intro z
  rfl

/-- The original relative Galois group identifies with that same actual kernel. -/
def normUnionGaloisKernelEquiv :=
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  (separableNormUnionAutEquiv K L Ω).trans
    (normUnionGaloisRelativeKernelEquiv K L)

/-- The relative-kernel equivalence is the original union map on every element. -/
theorem normUnionGaloisKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI : Semiring Ω :=
      @CommSemiring.toSemiring Ω
        (@Semifield.toCommSemiring Ω
          (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
    ∀ σ z, (normUnionGaloisKernelEquiv K L σ).val.val z =
      separableNormUnionMap K L Ω Ω σ.toAlgHom z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  intro σ z
  have h := normUnionGaloisRelativeKernelEquiv_apply K L
    (separableNormUnionAutEquiv K L Ω σ)
  exact (DFunLike.congr_fun h z).trans
    (separableNormUnionAutEquiv_apply K L Ω σ z)

end FontaineWintenberger
