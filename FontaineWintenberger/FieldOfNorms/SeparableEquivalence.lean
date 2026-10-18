/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.SeparableFunctor
public import FontaineWintenberger.FieldOfNorms.SeparableAlgebraicEssentialImage
public import FontaineWintenberger.FieldOfNorms.NormUnionCongr
public import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence of the canonical separable extension categories

The actual original norm-union functor is essentially surjective by the
reconstructed original intermediate fields. Combining this producer with
its full Hom correspondence gives the categorical field-of-norms equivalence.

Reference: Wintenberger, Theorem 3.2.2.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace FontaineWintenberger

variable (K : Type u) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An actual original-union algebra isomorphism gives the same canonical categorical
isomorphism. -/
def separableNormUnionObjectIso
    (M : Type (max u v w)) [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable L M]
    (B : letI := normLimitField K L
      SeparableExtensionCat.{v, max u v w} (NormLimit K L))
    (e : letI := normLimitField K L
      letI := separableNormUnionField K L M
      letI := separableNormUnionAlgebra K L M
      SeparableNormUnion K L M ≃ₐ[NormLimit K L] B.obj) :
    letI := normLimitField K L
    separableNormUnionObjectOf.{u, v, w} K L M ≅ B := by
  letI := normLimitField K L
  letI := separableNormUnionField K L M
  letI := separableNormUnionAlgebra K L M
  dsimp only [separableNormUnionObjectOf]
  exact (separableFieldProperty (NormLimit K L)).isoMk (CommAlgCat.isoMk e)

/-- An actual union isomorphism remains in the same functor's essential image
when the original field is replaced by a universe-lifted isomorphic copy. -/
theorem separableNormUnionFunctor_mem_essImage_of_algEquiv
    {M : Type v} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable L M]
    (B : letI := normLimitField K L
      SeparableExtensionCat.{v, max u v w} (NormLimit K L))
    (e : letI := normLimitField K L
      letI := separableNormUnionField K L M
      letI := separableNormUnionAlgebra K L M
      SeparableNormUnion K L M ≃ₐ[NormLimit K L] B.obj) :
    letI := normLimitField K L
    (separableNormUnionFunctor.{u, v, w} K L).essImage B := by
  let := normLimitField K L
  let : Algebra.IsSeparable L (ULift.{max u v w} M) :=
    AlgEquiv.Algebra.isSeparable
      (ULift.algEquiv.{v, v, max u v w} (R := L) (A := M)).symm
  let A : SeparableExtensionCat.{v, max u v w} L :=
    SeparableExtensionCat.of (R := L) (ULift.{max u v w} M)
  let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  let : Algebra L A.obj := A.obj.algebra
  let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  let : SMul K A.obj := (inferInstance : Algebra K A.obj).toSMul
  let : SMul L A.obj := (inferInstance : Algebra L A.obj).toSMul
  let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable L A.obj := A.property.2
  let a : A.obj ≃ₐ[L] M := ULift.algEquiv.{v, v, max u v w}
  let := separableNormUnionField K L M
  let := separableNormUnionAlgebra K L M
  let := separableNormUnionField K L A.obj
  let := separableNormUnionAlgebra K L A.obj
  let c := separableNormUnionCongr K L A.obj M a
  let d := c.trans e
  let i := separableNormUnionObjectIso.{u, v, w} K L A.obj B d
  refine ⟨A, ?_⟩
  dsimp only [separableNormUnionFunctor, separableNormUnionObj]
  exact ⟨i⟩

/-- Every canonical separable target object is the value of an actual original extension. -/
theorem separableNormUnionFunctorEssSurj :
    letI := normLimitField K L
    (separableNormUnionFunctor.{u, v, w} K L).EssSurj := by
  let := normLimitField K L
  constructor
  intro B
  let : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  let : Algebra.IsSeparable (NormLimit K L) B.obj := B.property.2
  obtain ⟨M, ⟨e⟩⟩ := exists_separableNormUnion_algEquiv K L B.obj
  exact separableNormUnionFunctor_mem_essImage_of_algEquiv.{u, v, w}
    K L B e

/-- Full faithfulness and the constructed original essential image prove equivalence. -/
theorem separableNormUnionFunctorIsEquivalence :
    letI := normLimitField K L
    (separableNormUnionFunctor.{u, v, w} K L).IsEquivalence := by
  let := normLimitField K L
  let ff := separableNormUnionFunctorFullyFaithful.{u, v, w} K L
  exact ⟨ff.faithful, ff.full,
    separableNormUnionFunctorEssSurj.{u, v, w} K L⟩

/-- The field-of-norms equivalence has exactly the original canonical union functor. -/
def separableNormUnionEquivalence :
    letI := normLimitField K L
    SeparableExtensionCat.{v, max u v w} L ≌
      SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI := normLimitField K L
  letI := separableNormUnionFunctorIsEquivalence.{u, v, w} K L
  exact (separableNormUnionFunctor.{u, v, w} K L).asEquivalence

/-- The equivalence retains the literal original induced maps. -/
@[simp]
theorem separableNormUnionEquivalence_functor :
    letI := normLimitField K L
    (separableNormUnionEquivalence.{u, v, w} K L).functor =
      separableNormUnionFunctor.{u, v, w} K L := rfl

end FontaineWintenberger
