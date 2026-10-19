/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.FieldTheory.AbsoluteGaloisGroup
public import FontaineWintenberger.APF.Defs
public import FontaineWintenberger.FieldOfNorms.Galois.AbsoluteGroup
public import FontaineWintenberger.FieldOfNorms.Galois.Ambient

/-!
# The main statements transported to Mathlib's `Field.absoluteGaloisGroup`

The library states Wintenberger's results for `Gal(K^sep/K)` (or any separable closure
`[IsSepClosure K Ω]`), which is the absolute Galois group in the sense of the paper. Mathlib's
`Field.absoluteGaloisGroup K = Aut(K^alg/K)` is isomorphic to it through the restriction map
`Field.absoluteGaloisGroup.sepEquiv`, and this file records the transported statements. They have
no downstream use.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, 1.2.1, 3.2.3, 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Field.absoluteGaloisGroup

section APF

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The subgroup `G_K^u · G_L` of the absolute Galois group, for an embedding `i : L → K^sep`. -/
def apfAbsoluteSubgroup (i : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  (apfSubgroup K i.fieldRange u).comap (sepEquiv K).toMonoidHom

/-- Wintenberger 1.2.1 on `Field.absoluteGaloisGroup K`. -/
theorem isAPF_iff_isOpen_absoluteGaloisGroup :
    IsAPF K L ↔ ∀ (i : L →ₐ[K] SeparableClosure K) (u : ℝ), -1 ≤ u →
      IsOpen (apfAbsoluteSubgroup K L i u : Set (Field.absoluteGaloisGroup K)) := by
  rw [isAPF_iff_isOpen_apfSubgroup]
  exact forall₃_congr fun i u _ => (sepEquiv K).toHomeomorph.isOpen_preimage.symm

end APF

section FieldOfNorms

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Corollary 3.2.3 on `Field.absoluteGaloisGroup`. -/
def FieldOfNorms.absoluteGaloisGroupEquiv :
    Field.absoluteGaloisGroup L ≃ₜ* Field.absoluteGaloisGroup (FieldOfNorms K L) :=
  ((sepEquiv L).trans (FieldOfNorms.absoluteGaloisEquiv K L)).trans
    (sepEquiv (FieldOfNorms K L)).symm

end FieldOfNorms

section GaloisAction

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Remark 3.2.4 (ii) on `Field.absoluteGaloisGroup K`. -/
def RelFieldOfNorms.absoluteGaloisGroupAction :
    Field.absoluteGaloisGroup K →* RingAut (RelFieldOfNorms K L (SeparableClosure K)) :=
  (RelFieldOfNorms.absoluteAut K L).comp (sepEquiv K).toMonoidHom

/-- Remark 3.2.4 (iii) on `Field.absoluteGaloisGroup K`. -/
def RelFieldOfNorms.absoluteGaloisGroupEquiv :
    Field.absoluteGaloisGroup K ≃* RelFieldOfNorms.galoisSubgroup K L :=
  (sepEquiv K).toMulEquiv.trans (RelFieldOfNorms.ambientGaloisEquiv K L)

end GaloisAction

end FontaineWintenberger

end
