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

variable (K : Type u) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type v) (M : Type w) (N : Type w') [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L M] [Algebra L N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An original algebra isomorphism induces the original isomorphism of the same unions. -/
def RelFieldOfNorms.congr (e : M ≃ₐ[L] N) :
    RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L N := by
  refine AlgEquiv.ofAlgHom
    (RelFieldOfNorms.algMap K L M N e.toAlgHom)
    (RelFieldOfNorms.algMap K L N M e.symm.toAlgHom) ?_ ?_
  · apply AlgHom.ext
    intro x
    change RelFieldOfNorms.map K L M N e.toAlgHom
      (RelFieldOfNorms.map K L N M e.symm.toAlgHom x) = x
    have h := congrArg
      (fun f : RelFieldOfNorms K L N →+*
        RelFieldOfNorms K L N => f x)
      (RelFieldOfNorms.map_comp K L N M e.symm.toAlgHom N e.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.comp_symm, RelFieldOfNorms.map_id,
      RingHom.id_apply] using h
  · apply AlgHom.ext
    intro x
    change RelFieldOfNorms.map K L N M e.symm.toAlgHom
      (RelFieldOfNorms.map K L M N e.toAlgHom x) = x
    have h := congrArg
      (fun f : RelFieldOfNorms K L M →+*
        RelFieldOfNorms K L M => f x)
      (RelFieldOfNorms.map_comp K L M N e.toAlgHom M e.symm.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.symm_comp, RelFieldOfNorms.map_id,
      RingHom.id_apply] using h

/-- The comparison has exactly the original induced algebra homomorphism. -/
@[simp]
theorem RelFieldOfNorms.congr_toAlgHom (e : M ≃ₐ[L] N) :
    (RelFieldOfNorms.congr K L M N e).toAlgHom =
      RelFieldOfNorms.algMap K L M N e.toAlgHom := rfl

/-- The comparison acts by the original map on the original union carrier. -/
@[simp]
theorem RelFieldOfNorms.congr_apply (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M N e x =
      RelFieldOfNorms.map K L M N e.toAlgHom x := rfl

/-- The inverse comparison is induced by the original inverse isomorphism. -/
@[simp]
theorem RelFieldOfNorms.congr_symm_apply (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L N) :
    (RelFieldOfNorms.congr K L M N e).symm x =
      RelFieldOfNorms.map K L N M e.symm.toAlgHom x := rfl

/-- The actual union comparison preserves the original rational valuation. -/
theorem RelFieldOfNorms.congr_valuation (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L N
        (RelFieldOfNorms.congr K L M N e x) =
      RelFieldOfNorms.valuation K L M x :=
  RelFieldOfNorms.map_valuation K L M N e.toAlgHom x

/-- The identity original isomorphism acts as the identity on the actual union. -/
@[simp]
theorem RelFieldOfNorms.congr_refl_apply
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M M (AlgEquiv.refl : M ≃ₐ[L] M) x = x := by
  change RelFieldOfNorms.map K L M M (AlgHom.id L M) x = x
  exact DFunLike.congr_fun (RelFieldOfNorms.map_id K L M) x

variable (P : Type w'') [Field P] [Algebra K P] [Algebra L P]
    [IsScalarTower K L P] [Algebra.IsSeparable L P]

/-- The actual comparison of a composite is the composite of the actual comparisons. -/
theorem RelFieldOfNorms.congr_trans_apply (e : M ≃ₐ[L] N) (f : N ≃ₐ[L] P)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M P (e.trans f) x =
      RelFieldOfNorms.congr K L N P f
        (RelFieldOfNorms.congr K L M N e x) := by
  change RelFieldOfNorms.map K L M P (f.toAlgHom.comp e.toAlgHom) x =
    RelFieldOfNorms.map K L N P f.toAlgHom
      (RelFieldOfNorms.map K L M N e.toAlgHom x)
  exact (DFunLike.congr_fun
    (RelFieldOfNorms.map_comp K L M N e.toAlgHom P f.toAlgHom) x).symm

/-- The actual union of a universe-lifted original extension is canonically the same field. -/
abbrev RelFieldOfNorms.uLiftEquiv :
    letI : Algebra.IsSeparable L (ULift.{z} M) :=
      AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
    RelFieldOfNorms K L (ULift.{z} M) ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M := by
  letI : Algebra.IsSeparable L (ULift.{z} M) :=
    AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
  exact RelFieldOfNorms.congr K L (ULift.{z} M) M
    ULift.algEquiv.{v, w, z}

end FontaineWintenberger
