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
theorem finiteLayerPullback_mem_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) (x : M) :
    e x ∈ finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D) ↔
      x ∈ finiteLayerPullback K M D := by
  change algebraMap M' N' (e x) ∈ D.val.map f.toAlgHom ↔ algebraMap M N x ∈ D.val
  rw [← h x]
  exact D.val.map_mem_map f.toAlgHom

/-- The actual image of the original pullback is the original target pullback. -/
theorem finiteLayerPullback_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) :
    (finiteLayerPullback K M D).map e.toAlgHom =
      finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (finiteLayerPullback_mem_map_iff K e f h D y).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (finiteLayerPullback_mem_map_iff K e f h D (e.symm x)).mp
    simpa only [AlgEquiv.apply_symm_apply] using hx

/-- The restriction of the actual coefficient-field isomorphism to the
actual original pullbacks. -/
def finiteLayerPullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) :
    finiteLayerPullback K M D ≃ₐ[K]
      finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D) :=
  (IntermediateField.equivMap (finiteLayerPullback K M D) e.toAlgHom).trans
    (IntermediateField.equivOfEq (finiteLayerPullback_map K e f h D))

@[simp]
theorem coe_finiteLayerPullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) (x : finiteLayerPullback K M D) :
    (finiteLayerPullbackEquiv K e f h D x : M') = e (x : M) := rfl

/-- The actual semilinear tensor transport, retained as an additive equivalence
so no scalar-structure choices are required by its consumers. -/
def finiteLayerTensorAddEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) :
    (M ⊗[finiteLayerPullback K M D] D.val) ≃+
      (M' ⊗[finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D)]
        (FiniteLayer.map f.toAlgHom D).val) := by
  let ec := finiteLayerPullbackEquiv K e f h D
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
  have hc (c : finiteLayerPullback K M D) :
      FiniteLayer.equivMap f.toAlgHom D
          (algebraMap (finiteLayerPullback K M D) D.val c) =
        algebraMap (finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D))
          (FiniteLayer.map f.toAlgHom D).val (ec c) := by
    apply Subtype.ext
    change f (algebraMap D.val N (algebraMap (finiteLayerPullback K M D) D.val c)) =
      algebraMap (FiniteLayer.map f.toAlgHom D).val N'
        (algebraMap (finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D))
          (FiniteLayer.map f.toAlgHom D).val (ec c))
    rw [← IsScalarTower.algebraMap_apply (finiteLayerPullback K M D) D.val N,
      IsScalarTower.algebraMap_apply (finiteLayerPullback K M D) M N,
      ← IsScalarTower.algebraMap_apply
        (finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D))
        (FiniteLayer.map f.toAlgHom D).val N',
      IsScalarTower.algebraMap_apply
        (finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D)) M' N']
    exact h (c : M)
  let ed : D.val ≃ₛₗ[ec.toRingHom] (FiniteLayer.map f.toAlgHom D).val :=
    { (FiniteLayer.equivMap f.toAlgHom D).toAddEquiv with
      map_smul' := by
        intro c d
        change FiniteLayer.equivMap f.toAlgHom D (c • d) =
          ec c • FiniteLayer.equivMap f.toAlgHom D d
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc] }
  exact (TensorProduct.congr em ed).toAddEquiv

/-- The tensor transport uses the actual two original field isomorphisms
on every original pure tensor. -/
@[simp]
theorem finiteLayerTensorAddEquiv_tmul (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) (m : M) (d : D.val) :
    finiteLayerTensorAddEquiv K e f h D (m ⊗ₜ[finiteLayerPullback K M D] d) =
      e m ⊗ₜ[finiteLayerPullback K M' (FiniteLayer.map f.toAlgHom D)]
        FiniteLayer.equivMap f.toAlgHom D d := rfl

/-- The actual original multiplication maps commute with the tensor transport. -/
theorem finiteLayerTensorMap_equiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) (z : M ⊗[finiteLayerPullback K M D] D.val) :
    finiteLayerTensorMap K M' (FiniteLayer.map f.toAlgHom D)
        (finiteLayerTensorAddEquiv K e f h D z) = f (finiteLayerTensorMap K M D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m d =>
    rw [finiteLayerTensorAddEquiv_tmul]
    change e m • f (d : N) = f (m • (d : N))
    simp only [Algebra.smul_def, map_mul, h]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Bijectivity of the actual original multiplication map is invariant under
the commuting field isomorphisms. -/
theorem isGoodFiniteLayer_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteLayer K N) :
    IsGoodFiniteLayer K M' (FiniteLayer.map f.toAlgHom D) ↔ IsGoodFiniteLayer K M D := by
  let U := finiteLayerTensorAddEquiv K e f h D
  constructor
  · intro hD
    constructor
    · intro a b hab
      apply U.injective
      apply hD.1
      rw [finiteLayerTensorMap_equiv, finiteLayerTensorMap_equiv, hab]
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f y)
      refine ⟨U.symm a, ?_⟩
      apply f.injective
      rw [← finiteLayerTensorMap_equiv K e f h D]
      change finiteLayerTensorMap K M' (FiniteLayer.map f.toAlgHom D)
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
      simpa only [finiteLayerTensorMap_equiv] using hab
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f.symm y)
      refine ⟨U a, ?_⟩
      change finiteLayerTensorMap K M' (FiniteLayer.map f.toAlgHom D)
        (finiteLayerTensorAddEquiv K e f h D a) = y
      rw [finiteLayerTensorMap_equiv, ha, f.apply_symm_apply]

end FontaineWintenberger
