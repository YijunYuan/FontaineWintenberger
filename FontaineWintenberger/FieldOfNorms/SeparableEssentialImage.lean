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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every actual finite separable extension of the original norm field is
isomorphic over that same field to an original finite norm-field stage in
the prescribed original separable closure. -/
theorem exists_finite_normLimit_algEquiv_of_separableClosure :
    letI := normLimitField K L p
    ∀ (F : Type*) [Field F] [Algebra (NormLimit K L) F]
      [Module.Finite (NormLimit K L) F] [Algebra.IsSeparable (NormLimit K L) F],
      ∃ N : FiniteLayer L Ω,
        letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
        letI := separableNormUnionStageField K L Ω p N
        letI := separableNormUnionStageAlgebra K L Ω p N
        Nonempty (NormLimit K N.val ≃ₐ[NormLimit K L] F) := by
  let := normLimitField K L p
  intro F _ _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let := separableNormUnionField K L Ω p
  let := separableNormUnionAlgebra K L Ω p
  let : Module (NormLimit K L) (SeparableNormUnion K L Ω p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L Ω p)).toDistribMulAction.toMulAction
  let : IsSepClosed (SeparableNormUnion K L Ω p) :=
    separableNormUnion_isSepClosed K L Ω p
  let t : F →ₐ[NormLimit K L] SeparableNormUnion K L Ω p := IsSepClosed.lift
  let : Module.Finite (NormLimit K L) t.fieldRange :=
    Module.Finite.equiv t.equivFieldRange.toLinearEquiv
  obtain ⟨N, hN, _⟩ := separableNormUnion_existsUnique_finite_subfield_preimage
    K L Ω p t.fieldRange
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let := separableNormUnionStageField K L Ω p N
  let := separableNormUnionStageAlgebra K L Ω p N
  let i := separableNormUnionOfAlgHom K L Ω p N
  refine ⟨N, ⟨i.equivFieldRange.trans ((IntermediateField.equivOfEq hN).trans
    t.equivFieldRange.symm)⟩⟩

/-- Without prescribing an original separable closure, every finite
separable target is still an actual original finite norm-field stage. -/
theorem exists_finite_normLimit_algEquiv :
    letI := normLimitField K L p
    ∀ (F : Type*) [Field F] [Algebra (NormLimit K L) F]
      [Module.Finite (NormLimit K L) F] [Algebra.IsSeparable (NormLimit K L) F],
      ∃ N : FiniteLayer L (SeparableClosure L),
        letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
        letI := separableNormUnionStageField K L (SeparableClosure L) p N
        letI := separableNormUnionStageAlgebra K L (SeparableClosure L) p N
        Nonempty (NormLimit K N.val ≃ₐ[NormLimit K L] F) := by
  let := normLimitField K L p
  intro F _ _ _ _
  exact exists_finite_normLimit_algEquiv_of_separableClosure
    K L (SeparableClosure L) p F

end FontaineWintenberger
