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
def RelFieldOfNorms.objectIso
    (M : Type (max u v w)) [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable L M]
    (B :
      SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L))
    (e :
      RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] B.obj) :
    RelFieldOfNorms.objectOf.{u, v, w} K L M ≅ B := by
  dsimp only [RelFieldOfNorms.objectOf]
  exact (separableFieldProperty (FieldOfNorms K L)).isoMk (CommAlgCat.isoMk e)

/-- An actual union isomorphism remains in the same functor's essential image
when the original field is replaced by a universe-lifted isomorphic copy. -/
theorem RelFieldOfNorms.functor_mem_essImage_of_algEquiv
    {M : Type v} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable L M]
    (B :
      SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L))
    (e :
      RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] B.obj) :
    (RelFieldOfNorms.functor.{u, v, w} K L).essImage B := by
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
  let c := RelFieldOfNorms.congr K L A.obj M a
  let d := c.trans e
  let i := RelFieldOfNorms.objectIso.{u, v, w} K L A.obj B d
  refine ⟨A, ?_⟩
  dsimp only [RelFieldOfNorms.functor, RelFieldOfNorms.obj]
  exact ⟨i⟩

/-- Every canonical separable target object is the value of an actual original extension. -/
theorem RelFieldOfNorms.functorEssSurj :
    (RelFieldOfNorms.functor.{u, v, w} K L).EssSurj := by
  constructor
  intro B
  let : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  let : Algebra.IsSeparable (FieldOfNorms K L) B.obj := B.property.2
  obtain ⟨M, ⟨e⟩⟩ := exists_relFieldOfNorms_algEquiv K L B.obj
  exact RelFieldOfNorms.functor_mem_essImage_of_algEquiv.{u, v, w}
    K L B e

/-- Full faithfulness and the constructed original essential image prove equivalence. -/
theorem RelFieldOfNorms.functorIsEquivalence :
    (RelFieldOfNorms.functor.{u, v, w} K L).IsEquivalence := by
  let ff := RelFieldOfNorms.functorFullyFaithful.{u, v, w} K L
  exact ⟨ff.faithful, ff.full,
    RelFieldOfNorms.functorEssSurj.{u, v, w} K L⟩

/-- The field-of-norms equivalence has exactly the original relative field of norms functor. -/
def RelFieldOfNorms.equivalence :
    SeparableExtensionCat.{v, max u v w} L ≌
      SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L) := by
  letI := RelFieldOfNorms.functorIsEquivalence.{u, v, w} K L
  exact (RelFieldOfNorms.functor.{u, v, w} K L).asEquivalence

/-- The equivalence retains the literal original induced maps. -/
@[simp]
theorem RelFieldOfNorms.equivalence_functor :
    (RelFieldOfNorms.equivalence.{u, v, w} K L).functor =
      RelFieldOfNorms.functor.{u, v, w} K L := rfl

end FontaineWintenberger
