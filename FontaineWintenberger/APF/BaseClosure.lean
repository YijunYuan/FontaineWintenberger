/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Basic

/-!
# The actual separable closure after changing the base field

The common closure and its genuine automorphism groups are identified using
Mathlib's separable-closure uniqueness and fixing-subgroup equivalence.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [Field K]
variable (M : IntermediateField K (SeparableClosure K))

/-- The original separable closure is a separable closure over every subextension. -/
theorem isSepClosure_over_subextension : IsSepClosure M (SeparableClosure K) := by
  apply isSepClosure_iff.mpr
  exact ⟨inferInstance, inferInstance⟩

/-- An actual isomorphism of the two separable closures over the new base field. -/
noncomputable def separableClosureBaseChangeEquiv :
    SeparableClosure M ≃ₐ[M] SeparableClosure K := by
  letI := isSepClosure_over_subextension K M
  exact IsSepClosure.equiv M (SeparableClosure M) (SeparableClosure K)

/-- The actual absolute Galois group of the new base is the original fixing subgroup. -/
noncomputable def absoluteGaloisBaseChangeEquiv :
    (SeparableClosure M ≃ₐ[M] SeparableClosure M) ≃* M.fixingSubgroup :=
  (separableClosureBaseChangeEquiv K M).autCongr.trans M.fixingSubgroupEquiv.symm

/-- The fixing-subgroup element is precisely the conjugate field automorphism. -/
theorem coe_absoluteGaloisBaseChangeEquiv
    (g : SeparableClosure M ≃ₐ[M] SeparableClosure M) :
    (absoluteGaloisBaseChangeEquiv K M g).1 =
      ((separableClosureBaseChangeEquiv K M).autCongr g).restrictScalars K := rfl

/-- The automorphism identification commutes with the actual closure isomorphism. -/
theorem absoluteGaloisBaseChangeEquiv_apply
    (g : SeparableClosure M ≃ₐ[M] SeparableClosure M) (x : SeparableClosure M) :
    (absoluteGaloisBaseChangeEquiv K M g).1 (separableClosureBaseChangeEquiv K M x) =
      separableClosureBaseChangeEquiv K M (g x) := by
  change separableClosureBaseChangeEquiv K M
    (g ((separableClosureBaseChangeEquiv K M).symm
      (separableClosureBaseChangeEquiv K M x))) = _
  rw [AlgEquiv.symm_apply_apply]

end FontaineWintenberger
