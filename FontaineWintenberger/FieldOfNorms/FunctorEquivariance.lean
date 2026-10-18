/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteNormPairs
public import FontaineWintenberger.FieldOfNorms.Isomorphism
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Equivariance of the original finite norm-family maps

Commuting isomorphisms transport the original pullback fields and canonical
multiplication maps. Standard semilinear tensor equivalences preserve actual
goodness, providing the coordinate comparisons in the covariant functor laws.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

variable (K : Type*) {M N M' N' : Type*}
    [Field K] [Field M] [Field N] [Field M'] [Field N']
    [Algebra K M] [Algebra K N] [Algebra K M'] [Algebra K N']
    [Algebra M N] [Algebra M' N'] [IsScalarTower K M N] [IsScalarTower K M' N']

/-- Original pullback membership is preserved by a commuting square of
actual ambient and coefficient-field isomorphisms. -/
theorem FiniteIntermediateField.pullback_mem_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (x : M) :
    e x ∈ FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) ↔
      x ∈ FiniteIntermediateField.pullback K M D := by
  change algebraMap M' N' (e x) ∈ D.val.map f.toAlgHom ↔ algebraMap M N x ∈ D.val
  rw [← h x]
  exact D.val.map_mem_map f.toAlgHom

/-- The actual image of the original pullback is the original target pullback. -/
theorem FiniteIntermediateField.pullback_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    (FiniteIntermediateField.pullback K M D).map e.toAlgHom =
      FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (FiniteIntermediateField.pullback_mem_map_iff K e f h D y).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (FiniteIntermediateField.pullback_mem_map_iff K e f h D (e.symm x)).mp
    simpa only [AlgEquiv.apply_symm_apply] using hx

/-- The restriction of the actual coefficient-field isomorphism to the
actual original pullbacks. -/
def FiniteIntermediateField.pullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.pullback K M D ≃ₐ[K]
      FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) :=
  (IntermediateField.equivMap (FiniteIntermediateField.pullback K M D) e.toAlgHom).trans
    (IntermediateField.equivOfEq (FiniteIntermediateField.pullback_map K e f h D))

@[simp]
theorem coe_finiteIntermediateFieldPullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (x : FiniteIntermediateField.pullback K M D) :
    (FiniteIntermediateField.pullbackEquiv K e f h D x : M') = e (x : M) := rfl

/-- The actual semilinear tensor transport, retained as an additive equivalence
so no scalar-structure choices are required by its consumers. -/
def FiniteIntermediateField.tensorAddEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    (M ⊗[FiniteIntermediateField.pullback K M D] D.val) ≃+
      (M' ⊗[FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)]
        (FiniteIntermediateField.map f.toAlgHom D).val) := by
  let ec := FiniteIntermediateField.pullbackEquiv K e f h D
  let : RingHomInvPair ec.toRingHom ec.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv ec.toRingEquiv
  let : RingHomInvPair ec.symm.toRingHom ec.toRingHom := RingHomInvPair.symm _ _
  let em : M ≃ₛₗ[ec.toRingHom] M' :=
    { e.toAddEquiv with
      map_smul' := by
        intro c m
        change e ((c : M) * m) = (ec c : M') * e m
        rw [map_mul]
        rfl }
  have hc (c : FiniteIntermediateField.pullback K M D) :
      FiniteIntermediateField.equivMap f.toAlgHom D
          (algebraMap (FiniteIntermediateField.pullback K M D) D.val c) =
        algebraMap (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom
            D))
          (FiniteIntermediateField.map f.toAlgHom D).val (ec c) := by
    apply Subtype.ext
    change f (algebraMap D.val N (algebraMap (FiniteIntermediateField.pullback K M D) D.val c)) =
      algebraMap (FiniteIntermediateField.map f.toAlgHom D).val N'
        (algebraMap (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom
            D))
          (FiniteIntermediateField.map f.toAlgHom D).val (ec c))
    rw [← IsScalarTower.algebraMap_apply (FiniteIntermediateField.pullback K M D) D.val N,
      IsScalarTower.algebraMap_apply (FiniteIntermediateField.pullback K M D) M N,
      ← IsScalarTower.algebraMap_apply
        (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D))
        (FiniteIntermediateField.map f.toAlgHom D).val N',
      IsScalarTower.algebraMap_apply
        (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)) M' N']
    exact h (c : M)
  let ed : D.val ≃ₛₗ[ec.toRingHom] (FiniteIntermediateField.map f.toAlgHom D).val :=
    { (FiniteIntermediateField.equivMap f.toAlgHom D).toAddEquiv with
      map_smul' := by
        intro c d
        change FiniteIntermediateField.equivMap f.toAlgHom D (c • d) =
          ec c • FiniteIntermediateField.equivMap f.toAlgHom D d
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc] }
  exact (TensorProduct.congr em ed).toAddEquiv

/-- The tensor transport uses the actual two original field isomorphisms
on every original pure tensor. -/
@[simp]
theorem FiniteIntermediateField.tensorAddEquiv_tmul (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (m : M) (d : D.val) :
    FiniteIntermediateField.tensorAddEquiv K e f h D (m ⊗ₜ[FiniteIntermediateField.pullback K M D]
        d) =
      e m ⊗ₜ[FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)]
        FiniteIntermediateField.equivMap f.toAlgHom D d := rfl

/-- The actual original multiplication maps commute with the tensor transport. -/
theorem FiniteIntermediateField.tensorMap_equiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (z : M ⊗[FiniteIntermediateField.pullback K M D] D.val) :
    FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (FiniteIntermediateField.tensorAddEquiv K e f h D z) = f (FiniteIntermediateField.tensorMap
            K M D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m d =>
    rw [FiniteIntermediateField.tensorAddEquiv_tmul]
    change e m • f (d : N) = f (m • (d : N))
    simp only [Algebra.smul_def, map_mul, h]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Bijectivity of the actual original multiplication map is invariant under
the commuting field isomorphisms. -/
theorem isGoodFiniteLayer_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    IsGoodFiniteLayer K M' (FiniteIntermediateField.map f.toAlgHom D) ↔ IsGoodFiniteLayer K M D :=
        by
  let U := FiniteIntermediateField.tensorAddEquiv K e f h D
  constructor
  · intro hD
    constructor
    · intro a b hab
      apply U.injective
      apply hD.1
      rw [FiniteIntermediateField.tensorMap_equiv, FiniteIntermediateField.tensorMap_equiv, hab]
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f y)
      refine ⟨U.symm a, ?_⟩
      apply f.injective
      rw [← FiniteIntermediateField.tensorMap_equiv K e f h D]
      change FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (U (U.symm a)) = f y
      rw [U.apply_symm_apply, ha]
  · intro hD
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := U.surjective a
      obtain ⟨b, rfl⟩ := U.surjective b
      apply congrArg U
      apply hD.1
      apply f.injective
      dsimp only [U] at hab
      simpa only [FiniteIntermediateField.tensorMap_equiv] using hab
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f.symm y)
      refine ⟨U a, ?_⟩
      change FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (FiniteIntermediateField.tensorAddEquiv K e f h D a) = y
      rw [FiniteIntermediateField.tensorMap_equiv, ha, f.apply_symm_apply]

end FontaineWintenberger
