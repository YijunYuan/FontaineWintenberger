/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.SeparableClosedUnion
public import FontaineWintenberger.FieldOfNorms.FiniteSubfieldReconstruction

/-!
# Actual finite essential image of the norm-field functor

The proved separable closure of the original norm field and reconstruction
of its actual finite subfields realize every finite separable target as an
original finite norm field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every actual finite separable extension of the original norm field is
isomorphic over that same field to an original finite norm-field stage in
the prescribed original separable closure. -/
theorem exists_finite_normLimit_algEquiv_of_separableClosure :
    ∀ (F : Type*) [Field F] [Algebra (NormLimit K L) F]
      [Module.Finite (NormLimit K L) F] [Algebra.IsSeparable (NormLimit K L) F],
      ∃ N : FiniteLayer L Ω,
        Nonempty (NormLimit K N.val ≃ₐ[NormLimit K L] F) := by
  intro F _ _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let : IsSepClosed (SeparableNormUnion K L Ω) :=
    separableNormUnion_isSepClosed K L Ω
  let t : F →ₐ[NormLimit K L] SeparableNormUnion K L Ω := IsSepClosed.lift
  let : Module.Finite (NormLimit K L) t.fieldRange :=
    Module.Finite.equiv t.equivFieldRange.toLinearEquiv
  obtain ⟨N, hN, _⟩ := separableNormUnion_existsUnique_finite_subfield_preimage
    K L Ω t.fieldRange
  let i := separableNormUnionOfAlgHom K L Ω N
  refine ⟨N, ⟨i.equivFieldRange.trans ((IntermediateField.equivOfEq hN).trans
    t.equivFieldRange.symm)⟩⟩

/-- Without prescribing an original separable closure, every finite
separable target is still an actual original finite norm-field stage. -/
theorem exists_finite_normLimit_algEquiv :
    ∀ (F : Type*) [Field F] [Algebra (NormLimit K L) F]
      [Module.Finite (NormLimit K L) F] [Algebra.IsSeparable (NormLimit K L) F],
      ∃ N : FiniteLayer L (SeparableClosure L),
        Nonempty (NormLimit K N.val ≃ₐ[NormLimit K L] F) := by
  intro F _ _ _ _
  exact exists_finite_normLimit_algEquiv_of_separableClosure
    K L (SeparableClosure L) F

end FontaineWintenberger
