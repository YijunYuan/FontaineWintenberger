/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.SeparableNormUnion
public import Mathlib.Algebra.Field.ULift

/-!
# Isomorphisms of original norm-field unions

An isomorphism of the original separable algebraic extensions induces an
algebra isomorphism of their same canonical norm-field unions. The inverse
is induced by the original inverse, using the actual union-map laws.

Reference: Wintenberger, §§3.2.1 and 3.2.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

universe u v w w' w'' z

variable (K : Type u) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type v) (M : Type w) (N : Type w') [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L M] [Algebra L N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An original algebra isomorphism induces the original isomorphism of the same unions. -/
def separableNormUnionCongr (e : M ≃ₐ[L] N) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L N p
    letI := separableNormUnionAlgebra K L M p
    letI := separableNormUnionAlgebra K L N p
    SeparableNormUnion K L M p ≃ₐ[NormLimit K L]
      SeparableNormUnion K L N p := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionField K L N p
  letI := separableNormUnionAlgebra K L M p
  letI := separableNormUnionAlgebra K L N p
  refine AlgEquiv.ofAlgHom
    (separableNormUnionAlgMap K L M p N e.toAlgHom)
    (separableNormUnionAlgMap K L N p M e.symm.toAlgHom) ?_ ?_
  · apply AlgHom.ext
    intro x
    change separableNormUnionMap K L M p N e.toAlgHom
      (separableNormUnionMap K L N p M e.symm.toAlgHom x) = x
    have h := congrArg
      (fun f : SeparableNormUnion K L N p →+*
        SeparableNormUnion K L N p => f x)
      (separableNormUnionMap_comp K L N p M e.symm.toAlgHom N e.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.comp_symm, separableNormUnionMap_id,
      RingHom.id_apply] using h
  · apply AlgHom.ext
    intro x
    change separableNormUnionMap K L N p M e.symm.toAlgHom
      (separableNormUnionMap K L M p N e.toAlgHom x) = x
    have h := congrArg
      (fun f : SeparableNormUnion K L M p →+*
        SeparableNormUnion K L M p => f x)
      (separableNormUnionMap_comp K L M p N e.toAlgHom M e.symm.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.symm_comp, separableNormUnionMap_id,
      RingHom.id_apply] using h

/-- The comparison has exactly the original induced algebra homomorphism. -/
@[simp]
theorem separableNormUnionCongr_toAlgHom (e : M ≃ₐ[L] N) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L N p
    letI := separableNormUnionAlgebra K L M p
    letI := separableNormUnionAlgebra K L N p
    (separableNormUnionCongr K L M N p e).toAlgHom =
      separableNormUnionAlgMap K L M p N e.toAlgHom := rfl

/-- The comparison acts by the original map on the original union carrier. -/
@[simp]
theorem separableNormUnionCongr_apply (e : M ≃ₐ[L] N)
    (x : SeparableNormUnion K L M p) :
    separableNormUnionCongr K L M N p e x =
      separableNormUnionMap K L M p N e.toAlgHom x := rfl

/-- The inverse comparison is induced by the original inverse isomorphism. -/
@[simp]
theorem separableNormUnionCongr_symm_apply (e : M ≃ₐ[L] N)
    (x : SeparableNormUnion K L N p) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L N p
    letI := separableNormUnionAlgebra K L M p
    letI := separableNormUnionAlgebra K L N p
    (separableNormUnionCongr K L M N p e).symm x =
      separableNormUnionMap K L N p M e.symm.toAlgHom x := rfl

/-- The actual union comparison preserves the original rational valuation. -/
theorem separableNormUnionCongr_valuation (e : M ≃ₐ[L] N)
    (x : SeparableNormUnion K L M p) :
    separableNormUnionValuation K L N p
        (separableNormUnionCongr K L M N p e x) =
      separableNormUnionValuation K L M p x :=
  separableNormUnionMap_valuation K L M p N e.toAlgHom x

/-- The identity original isomorphism acts as the identity on the actual union. -/
@[simp]
theorem separableNormUnionCongr_refl_apply
    (x : SeparableNormUnion K L M p) :
    separableNormUnionCongr K L M M p (AlgEquiv.refl : M ≃ₐ[L] M) x = x := by
  let := separableNormUnionField K L M p
  change separableNormUnionMap K L M p M (AlgHom.id L M) x = x
  exact DFunLike.congr_fun (separableNormUnionMap_id K L M p) x

variable (P : Type w'') [Field P] [Algebra K P] [Algebra L P]
    [IsScalarTower K L P] [Algebra.IsSeparable L P]

/-- The actual comparison of a composite is the composite of the actual comparisons. -/
theorem separableNormUnionCongr_trans_apply (e : M ≃ₐ[L] N) (f : N ≃ₐ[L] P)
    (x : SeparableNormUnion K L M p) :
    separableNormUnionCongr K L M P p (e.trans f) x =
      separableNormUnionCongr K L N P p f
        (separableNormUnionCongr K L M N p e x) := by
  let := separableNormUnionField K L M p
  let := separableNormUnionField K L N p
  let := separableNormUnionField K L P p
  change separableNormUnionMap K L M p P (f.toAlgHom.comp e.toAlgHom) x =
    separableNormUnionMap K L N p P f.toAlgHom
      (separableNormUnionMap K L M p N e.toAlgHom x)
  exact (DFunLike.congr_fun
    (separableNormUnionMap_comp K L M p N e.toAlgHom P f.toAlgHom) x).symm

/-- The actual union of a universe-lifted original extension is canonically the same field. -/
abbrev separableNormUnionULiftEquiv :
    letI : Algebra.IsSeparable L (ULift.{z} M) :=
      AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
    letI := normLimitField K L p
    letI := separableNormUnionField K L (ULift.{z} M) p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L (ULift.{z} M) p
    letI := separableNormUnionAlgebra K L M p
    SeparableNormUnion K L (ULift.{z} M) p ≃ₐ[NormLimit K L]
      SeparableNormUnion K L M p := by
  letI : Algebra.IsSeparable L (ULift.{z} M) :=
    AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
  exact separableNormUnionCongr K L (ULift.{z} M) M p
    ULift.algEquiv.{v, w, z}

end FontaineWintenberger
