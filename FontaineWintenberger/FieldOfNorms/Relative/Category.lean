/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.Separable

/-!
# The category of separable algebraic field extensions

The category is the canonical full subcategory of commutative algebras whose
underlying rings are fields and whose elements are separable over the base.
Its morphisms are exactly the algebra homomorphisms.

## Main definitions

* `separableFieldProperty`: Separable field algebras form a property of the commutative algebra.
* `SeparableExtensionCat`: The canonical full subcategory of separable algebraic field extensions.
* `of`: Regard a separable field extension as an object of its canonical category.
* `homEquiv`: The morphisms of the full subcategory are exactly the algebra maps.
* `isoOfAlgEquiv`: An algebra isomorphism gives the same categorical field isomorphism.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace FontaineWintenberger

/-- Separable field algebras form a property of the commutative algebra. -/
def separableFieldProperty (R : Type u) [Field R] :
    ObjectProperty (CommAlgCat.{v} R) :=
  fun A => IsField A ∧ Algebra.IsSeparable R A

/-- The canonical full subcategory of separable algebraic field extensions. -/
abbrev SeparableExtensionCat (R : Type u) [Field R] :=
  (separableFieldProperty.{u, v} R).FullSubcategory

namespace SeparableExtensionCat

variable {R : Type u} [Field R]

/-- Regard a separable field extension as an object of its canonical category. -/
abbrev of (E : Type v) [Field E] [Algebra R E] [Algebra.IsSeparable R E] :
    SeparableExtensionCat.{u, v} R :=
  ⟨CommAlgCat.of R E, Field.toIsField E, inferInstance⟩

/-- The morphisms of the full subcategory are exactly the algebra maps. -/
def homEquiv (A B : SeparableExtensionCat.{u, v} R) :
    (A ⟶ B) ≃ (A.obj →ₐ[R] B.obj) where
  toFun f := f.hom.hom
  invFun f := ObjectProperty.homMk (CommAlgCat.ofHom f)
  left_inv _ := rfl
  right_inv _ := rfl

/-- An algebra isomorphism gives the same categorical field isomorphism. -/
def isoOfAlgEquiv {E F : Type v} [Field E] [Field F]
    [Algebra R E] [Algebra R F] [Algebra.IsSeparable R E] [Algebra.IsSeparable R F]
    (e : E ≃ₐ[R] F) : of (R := R) E ≅ of (R := R) F :=
  (separableFieldProperty R).isoMk (CommAlgCat.isoMk e)

end SeparableExtensionCat

end FontaineWintenberger
