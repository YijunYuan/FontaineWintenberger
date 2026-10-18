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

local notation "r" => normUnionGaloisRestriction K L p

/-- Forgetting the base algebra gives an actual member of the source target. -/
def normUnionGaloisRelativeHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
      separableNormUnionStageField K L Ω p N
    letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
      (separableNormUnionStageField K L Ω p N).toNonAssocSemiring
    letI := normLimitField K L p
    letI := separableNormUnionField K L Ω p
    letI : Semiring U :=
      @CommSemiring.toSemiring U
        (@Semifield.toCommSemiring U
          (@Field.toSemifield U (separableNormUnionField K L Ω p)))
    letI : NonAssocSemiring U :=
      (separableNormUnionField K L Ω p).toNonAssocSemiring
    letI : Mul U := (separableNormUnionField K L Ω p).toMul
    letI : Add U := (separableNormUnionField K L Ω p).toAdd
    letI : Group (RingAut U) := RingAut.instGroup U
    letI := separableNormUnionAlgebra K L Ω p
    (U ≃ₐ[X] U) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p N
  letI (N : FiniteLayer L Ω) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L Ω p N).toNonAssocSemiring
  letI := normLimitField K L p
  letI := separableNormUnionField K L Ω p
  letI : Semiring U :=
    @CommSemiring.toSemiring U
      (@Semifield.toCommSemiring U
        (@Field.toSemifield U (separableNormUnionField K L Ω p)))
  letI : NonAssocSemiring U :=
    (separableNormUnionField K L Ω p).toNonAssocSemiring
  letI : Mul U := (separableNormUnionField K L Ω p).toMul
  letI : Add U := (separableNormUnionField K L Ω p).toAdd
  letI : Group (RingAut U) := RingAut.instGroup U
  letI := separableNormUnionAlgebra K L Ω p
  exact
    (MulSemiringAction.toRingEquiv (U ≃ₐ[X] U) U).codRestrict S fun β => by
      apply (mem_normUnionGaloisSubgroup K L p β.toRingEquiv).mpr
      refine ⟨1, ?_⟩
      intro x
      change β (ι x) = ι ((ρ) 1 x)
      rw [(ρ).map_one]
      exact β.commutes x

/-- The canonical forgetful map is injective, retaining the actual ring automorphism. -/
theorem normUnionGaloisRelativeHom_injective :
    Function.Injective (normUnionGaloisRelativeHom K L p) := by
  intro β γ h
  exact DFunLike.ext β γ fun z => congrArg (fun η : S => η.val z) h

/-- Actual base-algebra automorphisms have trivial original base restriction. -/
theorem normUnionGaloisRelativeHom_mem_ker :
    ∀ β, normUnionGaloisRelativeHom K L p β ∈ (r).ker := by
  intro β
  apply (mem_normUnionGaloisRestriction_ker_iff K L p _).mpr
  cases β
  assumption

/-- Every genuine kernel element is induced by a base-algebra automorphism. -/
theorem normUnionGaloisRelativeHom_surjective_ker :
    Function.Surjective
      ((normUnionGaloisRelativeHom K L p).codRestrict (r).ker
        (normUnionGaloisRelativeHom_mem_ker K L p)) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := normLimitField K L p
  let : Semiring U :=
    @CommSemiring.toSemiring U
      (@Semifield.toCommSemiring U
        (@Field.toSemifield U (separableNormUnionField K L Ω p)))
  let := separableNormUnionAlgebra K L Ω p
  intro β
  have hfix := (mem_normUnionGaloisRestriction_ker_iff K L p β.val).mp
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
    ((normUnionGaloisRelativeHom K L p).codRestrict (r).ker
      (normUnionGaloisRelativeHom_mem_ker K L p))
    ⟨(MonoidHom.injective_codRestrict
        (normUnionGaloisRelativeHom K L p) (r).ker
        (normUnionGaloisRelativeHom_mem_ker K L p)).mpr
        (normUnionGaloisRelativeHom_injective K L p),
      normUnionGaloisRelativeHom_surjective_ker K L p⟩

/-- The canonical kernel comparison retains the same underlying automorphism. -/
theorem normUnionGaloisRelativeKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := normLimitField K L p
    letI : Semiring U :=
      @CommSemiring.toSemiring U
        (@Semifield.toCommSemiring U
          (@Field.toSemifield U (separableNormUnionField K L Ω p)))
    letI := separableNormUnionAlgebra K L Ω p
    ∀ β, (normUnionGaloisRelativeKernelEquiv K L p β).val.val =
      β.toRingEquiv := by
  let := normLimitField K L p
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
  (separableNormUnionAutEquiv K L Ω p).trans
    (normUnionGaloisRelativeKernelEquiv K L p)

/-- The relative-kernel equivalence is the original union map on every element. -/
theorem normUnionGaloisKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI : Semiring Ω :=
      @CommSemiring.toSemiring Ω
        (@Semifield.toCommSemiring Ω
          (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
    ∀ σ z, (normUnionGaloisKernelEquiv K L p σ).val.val z =
      separableNormUnionMap K L Ω p Ω σ.toAlgHom z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  intro σ z
  have h := normUnionGaloisRelativeKernelEquiv_apply K L p
    (separableNormUnionAutEquiv K L Ω p σ)
  exact (DFunLike.congr_fun h z).trans
    (separableNormUnionAutEquiv_apply K L Ω p σ z)

end FontaineWintenberger
