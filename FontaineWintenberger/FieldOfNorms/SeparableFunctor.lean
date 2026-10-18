/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Algebra.SeparableExtensionCategory
public import FontaineWintenberger.FieldOfNorms.NormUnionHom
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The actual functor on separable algebraic field extensions

The canonical category of separable field algebras receives the original
norm-union object and morphism maps. Their original identity/composition laws
and the genuine full Hom correspondence give a fully faithful functor.

Reference: Wintenberger, Theorem 3.2.2(ii).
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

/-- Bundle the original norm union of an actual separable field algebra. -/
def separableNormUnionObjectOf (M : Type (max u v w)) [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable L M] :
    letI := normLimitField K L
    SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI := normLimitField K L
  letI := separableNormUnionField K L M
  letI := separableNormUnionAlgebra K L M
  letI : Algebra.IsSeparable (NormLimit K L)
      (SeparableNormUnion K L M) :=
    separableNormUnion_isSeparable K L M
  exact SeparableExtensionCat.of (R := NormLimit K L)
    (SeparableNormUnion K L M)

/-- Bundle the original union embedding of actual field algebras. -/
def separableNormUnionObjectMapOf
    (M N : Type (max u v w)) [Field M] [Field N]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
    (t : M →ₐ[L] N) :
    letI := normLimitField K L
    separableNormUnionObjectOf.{u, v, w} K L M ⟶
      separableNormUnionObjectOf.{u, v, w} K L N := by
  letI := normLimitField K L
  letI := separableNormUnionField K L M
  letI := separableNormUnionField K L N
  letI := separableNormUnionAlgebra K L M
  letI := separableNormUnionAlgebra K L N
  dsimp only [separableNormUnionObjectOf]
  exact ObjectProperty.homMk
    (CommAlgCat.ofHom (separableNormUnionAlgMap K L M N t))

/-- The actual separable norm-field union, as an object of the canonical category. -/
abbrev separableNormUnionObj (A : SeparableExtensionCat.{v, max u v w} L) :
    letI := normLimitField K L
    SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  exact separableNormUnionObjectOf.{u, v, w} K L A.obj

/-- The categorical morphism is exactly the original induced algebra embedding. -/
def separableNormUnionObjMap
    {A B : SeparableExtensionCat.{v, max u v w} L} (f : A ⟶ B) :
    letI := normLimitField K L
    separableNormUnionObj.{u, v, w} K L A ⟶
      separableNormUnionObj.{u, v, w} K L B := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : Algebra K B.obj := Algebra.compHom B.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L B.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  letI : Algebra.IsSeparable L B.obj := B.property.2
  exact separableNormUnionObjectMapOf.{u, v, w} K L A.obj B.obj f.hom.hom

section OriginalFields

variable (M N P : Type (max u v w)) [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra K P] [Algebra L P] [IsScalarTower K L P]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N] [Algebra.IsSeparable L P]

/-- The bundled original union map preserves identities. -/
theorem separableNormUnionObjectMapOf_id :
    letI := normLimitField K L
    separableNormUnionObjectMapOf.{u, v, w} K L M M (AlgHom.id L M) =
      𝟙 (separableNormUnionObjectOf.{u, v, w} K L M) := by
  let := normLimitField K L
  let := separableNormUnionField K L M
  let := separableNormUnionAlgebra K L M
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact congrArg (fun f => f x) (separableNormUnionMap_id K L M)

/-- The bundled original union map preserves composition. -/
theorem separableNormUnionObjectMapOf_comp (t : M →ₐ[L] N) (s : N →ₐ[L] P) :
    letI := normLimitField K L
    separableNormUnionObjectMapOf.{u, v, w} K L M P (s.comp t) =
      separableNormUnionObjectMapOf.{u, v, w} K L M N t ≫
        separableNormUnionObjectMapOf.{u, v, w} K L N P s := by
  let := normLimitField K L
  let := separableNormUnionField K L M
  let := separableNormUnionAlgebra K L M
  let := separableNormUnionField K L N
  let := separableNormUnionAlgebra K L N
  let := separableNormUnionField K L P
  let := separableNormUnionAlgebra K L P
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact (congrArg (fun f => f x)
    (separableNormUnionMap_comp K L M N t P s)).symm

/-- The actual full Hom correspondence remains bijective after canonical bundling. -/
theorem separableNormUnionObjectMapOf_bijective :
    letI := normLimitField K L
    Function.Bijective (separableNormUnionObjectMapOf.{u, v, w}
      K L M N) := by
  let := normLimitField K L
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  exact (SeparableExtensionCat.homEquiv _ _).symm.bijective.comp
    (separableNormUnionAlgMap_bijective K L N M)

/-- Canonical categorical bundling leaves the original union embedding unchanged. -/
theorem separableNormUnionObjectMapOf_apply (t : M →ₐ[L] N)
    (x : SeparableNormUnion K L M) :
    letI := normLimitField K L
    (separableNormUnionObjectMapOf.{u, v, w} K L M N t).hom.hom x =
      separableNormUnionMap K L M N t x := rfl

/-- The original compatible rational valuations are preserved by the categorical map. -/
theorem separableNormUnionObjectMapOf_valuation (t : M →ₐ[L] N)
    (x : SeparableNormUnion K L M) :
    letI := normLimitField K L
    separableNormUnionValuation K L N
        ((separableNormUnionObjectMapOf.{u, v, w} K L M N t).hom.hom x) =
      separableNormUnionValuation K L M x :=
  separableNormUnionMap_valuation K L M N t x

/-- The value on a finite original field is its canonical terminal norm field. -/
def separableNormUnionObjectFiniteAlgEquiv [Module.Finite L M] :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K L
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K M
    letI := (finiteNormLimitRingHom K L M
).toAlgebra
    (separableNormUnionObjectOf.{u, v, w} K L M).obj ≃ₐ[NormLimit K L]
      NormLimit K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K L
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K M
  letI := (finiteNormLimitRingHom K L M
).toAlgebra
  dsimp only [separableNormUnionObjectOf]
  exact separableNormUnionFiniteAlgEquiv K L M

end OriginalFields

/-- The categorical map on each original pair of field algebras is bijective. -/
theorem separableNormUnionObjMap_bijective
    (A B : SeparableExtensionCat.{v, max u v w} L) :
    letI := normLimitField K L
    Function.Bijective (separableNormUnionObjMap.{u, v, w}
      K L (A := A) (B := B)) := by
  let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  let : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  let : Algebra K B.obj := Algebra.compHom B.obj (algebraMap K L)
  let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L B.obj := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable L A.obj := A.property.2
  let : Algebra.IsSeparable L B.obj := B.property.2
  constructor
  · intro f g h
    apply (SeparableExtensionCat.homEquiv A B).injective
    apply (separableNormUnionObjectMapOf_bijective.{u, v, w}
      K L A.obj B.obj).injective
    exact h
  · intro j
    obtain ⟨t, ht⟩ := (separableNormUnionObjectMapOf_bijective.{u, v, w}
      K L A.obj B.obj).surjective j
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom t), ?_⟩
    exact ht

/-- The original norm-union construction is a functor on the canonical categories. -/
def separableNormUnionFunctor :
    let := normLimitField K L
    SeparableExtensionCat.{v, max u v w} L ⥤
      SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI := normLimitField K L
  refine { obj := separableNormUnionObj.{u, v, w} K L
           map := fun f => separableNormUnionObjMap.{u, v, w} K L f
           map_id := ?_
           map_comp := ?_ }
  · intro A
    let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
    let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
    let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L A.obj := A.property.2
    exact separableNormUnionObjectMapOf_id.{u, v, w} K L A.obj
  · intro A B C f g
    let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
    let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
    let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L A.obj := A.property.2
    let : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
    let : Algebra K B.obj := Algebra.compHom B.obj (algebraMap K L)
    let : IsScalarTower K L B.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L B.obj := B.property.2
    let : Field C.obj := { C.property.1.toField with toCommRing := C.obj.commRing }
    let : Algebra K C.obj := Algebra.compHom C.obj (algebraMap K L)
    let : IsScalarTower K L C.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L C.obj := C.property.2
    exact separableNormUnionObjectMapOf_comp.{u, v, w} K L
      A.obj B.obj C.obj f.hom.hom g.hom.hom

/-- Full faithfulness uses the proved original Hom correspondence. -/
def separableNormUnionFunctorFullyFaithful :
    letI := normLimitField K L
    (separableNormUnionFunctor.{u, v, w} K L).FullyFaithful := by
  letI := normLimitField K L
  exact Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (separableNormUnionFunctor.{u, v, w} K L)).2
    (fun A B => separableNormUnionObjMap_bijective.{u, v, w} K L A B))

end FontaineWintenberger
