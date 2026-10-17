/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteDescent
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Original algebraic norms under finite tensor descent

The canonical tensor multiplication maps supplied by finite descent preserve
the original algebraic norms, by base change of multiplication determinants.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

section Rings

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R B] [Module.Finite R B]

/-- The original determinant norm commutes with finite free tensor base change. -/
theorem norm_tensor_includeRight (b : B) :
    Algebra.norm A (1 ⊗ₜ[R] b : A ⊗[R] B) = algebraMap R A (Algebra.norm R b) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]
  rfl

/-- Transporting the canonical tensor multiplication map preserves precisely
the original norms, rather than introducing a new norm on the finite field. -/
theorem norm_eq_of_tensorEquiv {S : Type*} [CommRing S] [Algebra A S]
    (e : A ⊗[R] B ≃ₐ[A] S) (b : B) :
    Algebra.norm A (e (1 ⊗ₜ[R] b)) = algebraMap R A (Algebra.norm R b) :=
  (Algebra.norm_eq_of_algEquiv e _).trans (norm_tensor_includeRight R A B b)

end Rings

section Fields

variable {C M N : Type*} [Field C] [Field M] [Field N]
    [Algebra C M] [Algebra C N] [Algebra M N] [IsScalarTower C M N]

/-- The actual descended primitive field has the original relative norm
under the actual original inclusion in the finite extension. -/
theorem norm_adjoin_of_minpoly_lifts (b : PowerBasis M N)
    (hx : IsIntegral C b.gen)
    (hq : minpoly M b.gen ∈ Polynomial.lifts (algebraMap C M))
    (d : IntermediateField.adjoin C {b.gen}) :
    Algebra.norm M (d : N) = algebraMap C M (Algebra.norm C d) := by
  let : Module.Finite C (IntermediateField.adjoin C {b.gen}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have h := norm_eq_of_tensorEquiv C M (IntermediateField.adjoin C {b.gen})
    (adjoinTensorEquiv b hx hq) d
  rw [adjoinTensorEquiv_tmul, map_one, one_mul] at h
  exact h

end Fields

end FontaineWintenberger
