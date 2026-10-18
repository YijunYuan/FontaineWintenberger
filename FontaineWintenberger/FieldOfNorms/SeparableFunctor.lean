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

variable (K : Type u) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Bundle the original norm union of an actual separable field algebra. -/
def separableNormUnionObjectOf (M : Type (max u v w)) [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable L M] :
    letI := normLimitField K L p
    SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionAlgebra K L M p
  letI : Algebra.IsSeparable (NormLimit K L)
      (SeparableNormUnion K L M p) :=
    separableNormUnion_isSeparable K L M p
  exact SeparableExtensionCat.of (R := NormLimit K L)
    (SeparableNormUnion K L M p)

/-- Bundle the original union embedding of actual field algebras. -/
def separableNormUnionObjectMapOf
    (M N : Type (max u v w)) [Field M] [Field N]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
    (t : M →ₐ[L] N) :
    letI := normLimitField K L p
    separableNormUnionObjectOf.{u, v, w} K L p M ⟶
      separableNormUnionObjectOf.{u, v, w} K L p N := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionField K L N p
  letI := separableNormUnionAlgebra K L M p
  letI := separableNormUnionAlgebra K L N p
  dsimp only [separableNormUnionObjectOf]
  exact ObjectProperty.homMk
    (CommAlgCat.ofHom (separableNormUnionAlgMap K L M p N t))

/-- The actual separable norm-field union, as an object of the canonical category. -/
abbrev separableNormUnionObj (A : SeparableExtensionCat.{v, max u v w} L) :
    letI := normLimitField K L p
    SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  exact separableNormUnionObjectOf.{u, v, w} K L p A.obj

/-- The categorical morphism is exactly the original induced algebra embedding. -/
def separableNormUnionObjMap
    {A B : SeparableExtensionCat.{v, max u v w} L} (f : A ⟶ B) :
    letI := normLimitField K L p
    separableNormUnionObj.{u, v, w} K L p A ⟶
      separableNormUnionObj.{u, v, w} K L p B := by
  letI : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
  letI : Field B.obj := { B.property.1.toField with toCommRing := B.obj.commRing }
  letI : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
  letI : Algebra K B.obj := Algebra.compHom B.obj (algebraMap K L)
  letI : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L B.obj := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsSeparable L A.obj := A.property.2
  letI : Algebra.IsSeparable L B.obj := B.property.2
  exact separableNormUnionObjectMapOf.{u, v, w} K L p A.obj B.obj f.hom.hom

section OriginalFields

variable (M N P : Type (max u v w)) [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra K P] [Algebra L P] [IsScalarTower K L P]
    [Algebra.IsSeparable L M] [Algebra.IsSeparable L N] [Algebra.IsSeparable L P]

/-- The bundled original union map preserves identities. -/
theorem separableNormUnionObjectMapOf_id :
    letI := normLimitField K L p
    separableNormUnionObjectMapOf.{u, v, w} K L p M M (AlgHom.id L M) =
      𝟙 (separableNormUnionObjectOf.{u, v, w} K L p M) := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact congrArg (fun f => f x) (separableNormUnionMap_id K L M p)

/-- The bundled original union map preserves composition. -/
theorem separableNormUnionObjectMapOf_comp (t : M →ₐ[L] N) (s : N →ₐ[L] P) :
    letI := normLimitField K L p
    separableNormUnionObjectMapOf.{u, v, w} K L p M P (s.comp t) =
      separableNormUnionObjectMapOf.{u, v, w} K L p M N t ≫
        separableNormUnionObjectMapOf.{u, v, w} K L p N P s := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let := separableNormUnionField K L N p
  let := separableNormUnionAlgebra K L N p
  let := separableNormUnionField K L P p
  let := separableNormUnionAlgebra K L P p
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact (congrArg (fun f => f x)
    (separableNormUnionMap_comp K L M p N t P s)).symm

/-- The actual full Hom correspondence remains bijective after canonical bundling. -/
theorem separableNormUnionObjectMapOf_bijective :
    letI := normLimitField K L p
    Function.Bijective (separableNormUnionObjectMapOf.{u, v, w}
      K L p M N) := by
  let := normLimitField K L p
  dsimp only [separableNormUnionObjectMapOf, separableNormUnionObjectOf]
  exact (SeparableExtensionCat.homEquiv _ _).symm.bijective.comp
    (separableNormUnionAlgMap_bijective K L N p M)

/-- Canonical categorical bundling leaves the original union embedding unchanged. -/
theorem separableNormUnionObjectMapOf_apply (t : M →ₐ[L] N)
    (x : SeparableNormUnion K L M p) :
    letI := normLimitField K L p
    (separableNormUnionObjectMapOf.{u, v, w} K L p M N t).hom.hom x =
      separableNormUnionMap K L M p N t x := rfl

/-- The original compatible rational valuations are preserved by the categorical map. -/
theorem separableNormUnionObjectMapOf_valuation (t : M →ₐ[L] N)
    (x : SeparableNormUnion K L M p) :
    letI := normLimitField K L p
    separableNormUnionValuation K L N p
        ((separableNormUnionObjectMapOf.{u, v, w} K L p M N t).hom.hom x) =
      separableNormUnionValuation K L M p x :=
  separableNormUnionMap_valuation K L M p N t x

/-- The value on a finite original field is its canonical terminal norm field. -/
def separableNormUnionObjectFiniteAlgEquiv [Module.Finite L M] :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K L p
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K M p
    letI := (finiteNormLimitRingHom K L M p
      ).toAlgebra
    (separableNormUnionObjectOf.{u, v, w} K L p M).obj ≃ₐ[NormLimit K L]
      NormLimit K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K L p
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K M p
  letI := (finiteNormLimitRingHom K L M p
    ).toAlgebra
  dsimp only [separableNormUnionObjectOf]
  exact separableNormUnionFiniteAlgEquiv K L M p


end OriginalFields

/-- The categorical map on each original pair of field algebras is bijective. -/
theorem separableNormUnionObjMap_bijective
    (A B : SeparableExtensionCat.{v, max u v w} L) :
    letI := normLimitField K L p
    Function.Bijective (separableNormUnionObjMap.{u, v, w}
      K L p (A := A) (B := B)) := by
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
      K L p A.obj B.obj).injective
    exact h
  · intro j
    obtain ⟨t, ht⟩ := (separableNormUnionObjectMapOf_bijective.{u, v, w}
      K L p A.obj B.obj).surjective j
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom t), ?_⟩
    exact ht

/-- The original norm-union construction is a functor on the canonical categories. -/
def separableNormUnionFunctor :
    let := normLimitField K L p
    SeparableExtensionCat.{v, max u v w} L ⥤
      SeparableExtensionCat.{v, max u v w} (NormLimit K L) := by
  letI := normLimitField K L p
  refine { obj := separableNormUnionObj.{u, v, w} K L p
           map := fun f => separableNormUnionObjMap.{u, v, w} K L p f
           map_id := ?_
           map_comp := ?_ }
  · intro A
    let : Field A.obj := { A.property.1.toField with toCommRing := A.obj.commRing }
    let : Algebra K A.obj := Algebra.compHom A.obj (algebraMap K L)
    let : IsScalarTower K L A.obj := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.IsSeparable L A.obj := A.property.2
    exact separableNormUnionObjectMapOf_id.{u, v, w} K L p A.obj
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
    exact separableNormUnionObjectMapOf_comp.{u, v, w} K L p
      A.obj B.obj C.obj f.hom.hom g.hom.hom

/-- Full faithfulness uses the proved original Hom correspondence. -/
def separableNormUnionFunctorFullyFaithful :
    letI := normLimitField K L p
    (separableNormUnionFunctor.{u, v, w} K L p).FullyFaithful := by
  letI := normLimitField K L p
  exact Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective
    (separableNormUnionFunctor.{u, v, w} K L p)).2
    (fun A B => separableNormUnionObjMap_bijective.{u, v, w} K L p A B))

end FontaineWintenberger
