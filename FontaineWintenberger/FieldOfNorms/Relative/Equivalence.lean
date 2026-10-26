/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Relative.Category
public import FontaineWintenberger.FieldOfNorms.Relative.Defs
public import FontaineWintenberger.FieldOfNorms.Relative.EssImage
public import FontaineWintenberger.FieldOfNorms.Relative.Hom
public import FontaineWintenberger.LocalField.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Equivalence of separable extension categories

## The functor on separable algebraic field extensions

The canonical category of separable field algebras receives the
norm-union object and morphism maps. Their identity/composition laws
and the full Hom correspondence give a fully faithful functor.

Reference: Wintenberger, Theorem 3.2.2(ii).

## Equivalence of the canonical separable extension categories

The norm-union functor is essentially surjective by the
reconstructed intermediate fields. Combining this producer with
its full Hom correspondence gives the categorical field-of-norms equivalence.

Reference: Wintenberger, Theorem 3.2.2.

## Main definitions

* `RelFieldOfNorms.objectOf`: Bundle the norm union of a separable field algebra.
* `RelFieldOfNorms.objectMapOf`: Bundle the union embedding of field algebras.
* `RelFieldOfNorms.obj`: The separable relative field of norms, as an object of the canonical
  category.
* `RelFieldOfNorms.objMap`: The categorical morphism is exactly the induced algebra embedding.
* `RelFieldOfNorms.objectFiniteAlgEquiv`: The value on a finite field is its canonical terminal norm
  field.
* `RelFieldOfNorms.functor`: The norm-union construction is a functor on the canonical categories.
* `RelFieldOfNorms.functorFullyFaithful`: Full faithfulness uses the proved Hom correspondence.
* `RelFieldOfNorms.objectIso`: An original-union algebra isomorphism gives the same canonical
  categorical isomorphism.

## Main results

* `RelFieldOfNorms.objectMapOf_id`: The bundled union map preserves identities.
* `RelFieldOfNorms.objectMapOf_comp`: The bundled union map preserves composition.
* `RelFieldOfNorms.objectMapOf_bijective`: The full Hom correspondence remains bijective after
  canonical bundling.
* `RelFieldOfNorms.objectMapOf_apply`: Canonical categorical bundling leaves the union embedding
  unchanged.
* `RelFieldOfNorms.objectMapOf_valuation`: The compatible rational valuations are preserved by the
  categorical map.
* `RelFieldOfNorms.objMap_bijective`: The categorical map on each pair of field algebras is
  bijective.
* `RelFieldOfNorms.functor_mem_essImage_of_algEquiv`: An union isomorphism remains in the same
  functor's essential image when the field is replaced by an universe-lifted isomorphic copy.
* `RelFieldOfNorms.functorEssSurj`: Every canonical separable target object is the value of an
  extension.

## Notation

The following notation is local to this file.

* `p` denotes the residue characteristic `residueChar K`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
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

/-- Bundle the norm union of a separable field algebra. -/
def RelFieldOfNorms.objectOf (M : Type (max u v w)) [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable L M] :
    SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L) := by
  letI : Algebra.IsSeparable (FieldOfNorms K L)
      (RelFieldOfNorms K L M) :=
    RelFieldOfNorms.isSeparable K L M
  exact SeparableExtensionCat.of (R := FieldOfNorms K L)
    (RelFieldOfNorms K L M)

/-- Bundle the union embedding of field algebras. -/
def RelFieldOfNorms.objectMapOf
    (M N : Type (max u v w)) [Field M] [Field N]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
    (t : M →ₐ[L] N) :
    RelFieldOfNorms.objectOf.{u, v, w} K L M ⟶
      RelFieldOfNorms.objectOf.{u, v, w} K L N := by
  dsimp only [RelFieldOfNorms.objectOf]
  exact ObjectProperty.homMk
    (CommAlgCat.ofHom (RelFieldOfNorms.algMap K L M N t))

/-- The separable relative field of norms, as an object of the canonical category. -/
abbrev RelFieldOfNorms.obj (A : SeparableExtensionCat.{v, max u v w} L) :
    SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L) := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  exact RelFieldOfNorms.objectOf.{u, v, w} K L A.obj

/-- The categorical morphism is exactly the induced algebra embedding. -/
def RelFieldOfNorms.objMap
    {A B : SeparableExtensionCat.{v, max u v w} L} (f : A ⟶ B) :
    RelFieldOfNorms.obj.{u, v, w} K L A ⟶
      RelFieldOfNorms.obj.{u, v, w} K L B := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : Algebra K B.obj := Algebra.compHom B.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L B.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  letI : Algebra.IsSeparable L B.obj := B.property.2
  exact RelFieldOfNorms.objectMapOf.{u, v, w} K L A.obj B.obj f.hom.hom

section Fields

variable (M N P : Type (max u v w)) [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra K P] [Algebra L P] [IsScalarTower K L P]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N] [Algebra.IsSeparable L P]

/-- The bundled union map preserves identities. -/
theorem RelFieldOfNorms.objectMapOf_id :
    RelFieldOfNorms.objectMapOf.{u, v, w} K L M M (AlgHom.id L M) =
      𝟙 (RelFieldOfNorms.objectOf.{u, v, w} K L M) := by
  dsimp only [RelFieldOfNorms.objectMapOf, RelFieldOfNorms.objectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact congrArg (fun f => f x) (RelFieldOfNorms.map_id K L M)

/-- The bundled union map preserves composition. -/
theorem RelFieldOfNorms.objectMapOf_comp (t : M →ₐ[L] N) (s : N →ₐ[L] P) :
    RelFieldOfNorms.objectMapOf.{u, v, w} K L M P (s.comp t) =
      RelFieldOfNorms.objectMapOf.{u, v, w} K L M N t ≫
        RelFieldOfNorms.objectMapOf.{u, v, w} K L N P s := by
  dsimp only [RelFieldOfNorms.objectMapOf, RelFieldOfNorms.objectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact (congrArg (fun f => f x)
    (RelFieldOfNorms.map_comp K L M N t P s)).symm

/-- The full Hom correspondence remains bijective after canonical bundling. -/
theorem RelFieldOfNorms.objectMapOf_bijective :
    Function.Bijective (RelFieldOfNorms.objectMapOf.{u, v, w}
      K L M N) := by
  dsimp only [RelFieldOfNorms.objectMapOf, RelFieldOfNorms.objectOf]
  exact (SeparableExtensionCat.homEquiv _ _).symm.bijective.comp
    (RelFieldOfNorms.algMap_bijective K L N M)

/-- Canonical categorical bundling leaves the union embedding unchanged. -/
theorem RelFieldOfNorms.objectMapOf_apply (t : M →ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    (RelFieldOfNorms.objectMapOf.{u, v, w} K L M N t).hom.hom x =
      RelFieldOfNorms.mapEquiv K L M N t x := rfl

/-- The compatible rational valuations are preserved by the categorical map. -/
theorem RelFieldOfNorms.objectMapOf_valuation (t : M →ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L N
        ((RelFieldOfNorms.objectMapOf.{u, v, w} K L M N t).hom.hom x) =
      RelFieldOfNorms.valuation K L M x :=
  RelFieldOfNorms.map_valuation K L M N t x

/-- The value on a finite field is its canonical terminal norm field. -/
def RelFieldOfNorms.objectFiniteAlgEquiv [Module.Finite L M] :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms.ambient_infinite K L M⟩
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms.ambient_infinite K L M⟩
    letI := (FieldOfNorms.inclusion K L M
).toAlgebra
    (RelFieldOfNorms.objectOf.{u, v, w} K L M).obj ≃ₐ[FieldOfNorms K L]
      FieldOfNorms K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms.ambient_infinite K L M⟩
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms.ambient_infinite K L M⟩
  letI := (FieldOfNorms.inclusion K L M
).toAlgebra
  dsimp only [RelFieldOfNorms.objectOf]
  exact RelFieldOfNorms.finiteAlgEquiv K L M

end Fields

/-- The categorical map on each pair of field algebras is bijective. -/
theorem RelFieldOfNorms.objMap_bijective
    (A B : SeparableExtensionCat.{v, max u v w} L) :
    Function.Bijective (RelFieldOfNorms.objMap.{u, v, w}
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
    apply (RelFieldOfNorms.objectMapOf_bijective.{u, v, w}
      K L A.obj B.obj).injective
    exact h
  · intro j
    obtain ⟨t, ht⟩ := (RelFieldOfNorms.objectMapOf_bijective.{u, v, w}
      K L A.obj B.obj).surjective j
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom t), ?_⟩
    exact ht

/-- The norm-union construction is a functor on the canonical categories. -/
def RelFieldOfNorms.functor :
    SeparableExtensionCat.{v, max u v w} L ⥤
      SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L) := by
  refine { obj := RelFieldOfNorms.obj.{u, v, w} K L
           map := fun f => RelFieldOfNorms.objMap.{u, v, w} K L f
           map_id := ?_
           map_comp := ?_ }
  · intro A
    let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
    let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
    let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L A.obj := A.property.2
    exact RelFieldOfNorms.objectMapOf_id.{u, v, w} K L A.obj
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
    exact RelFieldOfNorms.objectMapOf_comp.{u, v, w} K L
      A.obj B.obj C.obj f.hom.hom g.hom.hom

/-- Full faithfulness uses the proved Hom correspondence. -/
def RelFieldOfNorms.functorFullyFaithful :
    (RelFieldOfNorms.functor.{u, v, w} K L).FullyFaithful := by
  exact Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (RelFieldOfNorms.functor.{u, v, w} K L)).2
    (fun A B => RelFieldOfNorms.objMap_bijective.{u, v, w} K L A B))

end FontaineWintenberger

noncomputable section


open CategoryTheory

namespace FontaineWintenberger

variable (K : Type u) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An original-union algebra isomorphism gives the same canonical categorical
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

/-- An union isomorphism remains in the same functor's essential image
when the field is replaced by an universe-lifted isomorphic copy. -/
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

/-- Every canonical separable target object is the value of an extension. -/
theorem RelFieldOfNorms.functorEssSurj :
    (RelFieldOfNorms.functor.{u, v, w} K L).EssSurj := by
  constructor
  intro B
  let : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  let : Algebra.IsSeparable (FieldOfNorms K L) B.obj := B.property.2
  obtain ⟨M, ⟨e⟩⟩ := exists_relFieldOfNorms_algEquiv K L B.obj
  exact RelFieldOfNorms.functor_mem_essImage_of_algEquiv.{u, v, w}
    K L B e

/-- Full faithfulness and the constructed essential image prove equivalence. -/
theorem RelFieldOfNorms.functorIsEquivalence :
    (RelFieldOfNorms.functor.{u, v, w} K L).IsEquivalence := by
  let ff := RelFieldOfNorms.functorFullyFaithful.{u, v, w} K L
  exact ⟨ff.faithful, ff.full,
    RelFieldOfNorms.functorEssSurj.{u, v, w} K L⟩

/-- The field-of-norms equivalence has exactly the relative field of norms functor. -/
def RelFieldOfNorms.equivalence :
    SeparableExtensionCat.{v, max u v w} L ≌
      SeparableExtensionCat.{v, max u v w} (FieldOfNorms K L) := by
  letI := RelFieldOfNorms.functorIsEquivalence.{u, v, w} K L
  exact (RelFieldOfNorms.functor.{u, v, w} K L).asEquivalence

/-- The equivalence retains the induced maps. -/
@[simp]
theorem RelFieldOfNorms.equivalence_functor :
    (RelFieldOfNorms.equivalence.{u, v, w} K L).functor =
      RelFieldOfNorms.functor.{u, v, w} K L := rfl

end FontaineWintenberger
