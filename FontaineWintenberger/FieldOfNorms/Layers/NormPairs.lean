/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Layers.Descent
public import FontaineWintenberger.FieldOfNorms.Layers.DescentTower

/-!
# Norm identities on good finite fields

The finite fields used in the covariant field-of-norms construction are
finite intermediate fields. Their coefficient fields are their
pullbacks to the base; cofinality is proved by finite tensor descent.

## Main definitions

* `FiniteIntermediateField.pullback`: The pullback of a finite field along the base inclusion.
* `FiniteIntermediateField.pullbackTo`: The inclusion of the pullback into the finite field.
* `FiniteIntermediateField.overPullback`: The finite field, as an intermediate field over its
  pullback.
* `FiniteIntermediateField.tensorMap`: The multiplication map over the pullback field.
* `IsGoodFiniteLayer`: A finite field is good when its canonical multiplication map is bijective.
* `goodFiniteLayerTensorEquiv`: The canonical tensor isomorphism of a good finite field.
* `FiniteIntermediateField.pullbackLayer`: The pullback, as an index in the finite-layer system.
* `goodFinitePairTensorEquiv`: An inclusion of good finite fields is the tensor base change of the
  corresponding inclusion of their pullbacks.

## Main results

* `FiniteIntermediateField.pullback_mono`: Pullbacks preserve inclusions of the finite fields.
* `FiniteIntermediateField.pullback_eq_of_inf`: The coefficient field supplied by finite descent
  equals the pullback; the auxiliary presentation introduces no different finite field.
* `isGoodFiniteLayer_of_descent`: Changing a descended presentation to its equal pullback and finite
  field preserves the canonical tensor bijection.
* `exists_goodFiniteLayer_ge`: Good finite fields are cofinal; goodness is proved from finite tensor
  descent, rather than assumed as part of the interface.
* `exists_goodFiniteLayer_ge_pair`: Two finite fields have a common upper good finite field.
* `finrank_goodFiniteLayer`: Goodness gives the finite relative degree.
* `linearDisjoint_goodFiniteLayer`: Goodness gives linear disjointness over the pullback.
* `goodFinitePairTensorEquiv_tmul`: The pair isomorphism is the multiplication map on elements.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
    {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The pullback of a finite field along the base inclusion. -/
def FiniteIntermediateField.pullback (D : FiniteIntermediateField K N) : IntermediateField K M :=
  D.val.comap (IsScalarTower.toAlgHom K M N)

/-- The inclusion of the pullback into the finite field. -/
def FiniteIntermediateField.pullbackTo (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.pullback K M D →ₐ[K] D.val :=
  ((IsScalarTower.toAlgHom K M N).comp (FiniteIntermediateField.pullback K M D).val).codRestrict
    D.val.toSubalgebra fun x => x.property

instance FiniteIntermediateField.pullback_finite (D : FiniteIntermediateField K N) :
    Module.Finite K (FiniteIntermediateField.pullback K M D) :=
  Module.Finite.of_injective (FiniteIntermediateField.pullbackTo K M D).toLinearMap
    (FiniteIntermediateField.pullbackTo K M D).injective

/-- The finite field, as an intermediate field over its pullback. -/
def FiniteIntermediateField.overPullback (D : FiniteIntermediateField K N) :
    IntermediateField (FiniteIntermediateField.pullback K M D) N where
  __ := D.val.toSubfield
  algebraMap_mem' c := c.property

instance FiniteIntermediateField.pullbackAlgebra (D : FiniteIntermediateField K N) :
    Algebra (FiniteIntermediateField.pullback K M D) D.val :=
  (FiniteIntermediateField.overPullback K M D).algebra

instance FiniteIntermediateField.pullback_scalarTower (D : FiniteIntermediateField K N) :
    IsScalarTower K (FiniteIntermediateField.pullback K M D) D.val :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact IsScalarTower.algebraMap_apply K M N x)

instance FiniteIntermediateField.pullback_scalarTower_top (D : FiniteIntermediateField K N) :
    IsScalarTower (FiniteIntermediateField.pullback K M D) D.val N :=
  IsScalarTower.of_algebraMap_eq' rfl

instance FiniteIntermediateField.overPullback_finite (D : FiniteIntermediateField K N) :
    Module.Finite (FiniteIntermediateField.pullback K M D) D.val :=
  Module.Finite.of_restrictScalars_finite K _ _

/-- The multiplication map over the pullback field. -/
def FiniteIntermediateField.tensorMap (D : FiniteIntermediateField K N) :
    M ⊗[FiniteIntermediateField.pullback K M D] D.val →ₐ[M] N :=
  AlgHom.liftEquiv (FiniteIntermediateField.pullback K M D) M D.val N
    (IsScalarTower.toAlgHom (FiniteIntermediateField.pullback K M D) D.val N)

/-- A finite field is good when its canonical multiplication map is bijective. -/
def IsGoodFiniteLayer (D : FiniteIntermediateField K N) : Prop :=
  Function.Bijective (FiniteIntermediateField.tensorMap K M D)

/-- The canonical tensor isomorphism of a good finite field. -/
def goodFiniteLayerTensorEquiv (D : FiniteIntermediateField K N) (hD : IsGoodFiniteLayer K M D) :
    M ⊗[FiniteIntermediateField.pullback K M D] D.val ≃ₐ[M] N :=
  AlgEquiv.ofBijective (FiniteIntermediateField.tensorMap K M D) hD

@[simp]
theorem goodFiniteLayerTensorEquiv_tmul (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (m : M) (d : D.val) :
    goodFiniteLayerTensorEquiv K M D hD (m ⊗ₜ[FiniteIntermediateField.pullback K M D] d) =
      algebraMap M N m * (d : N) :=
  Algebra.smul_def m (d : N)

/-- Pullbacks preserve inclusions of the finite fields. -/
theorem FiniteIntermediateField.pullback_mono {D D' : FiniteIntermediateField K N} (h : D ≤ D') :
    FiniteIntermediateField.pullback K M D ≤ FiniteIntermediateField.pullback K M D' :=
  fun _ hx => h hx

/-- The coefficient field supplied by finite descent equals the
pullback; the auxiliary presentation introduces no different finite field. -/
theorem FiniteIntermediateField.pullback_eq_of_inf (C : IntermediateField K M)
    (D : IntermediateField C N) (hfin : Module.Finite K (D.restrictScalars K))
    (hinf : D ⊓ (IsScalarTower.toAlgHom C M N).fieldRange = ⊥) :
    FiniteIntermediateField.pullback K M ⟨D.restrictScalars K, hfin⟩ = C := by
  ext x
  constructor
  · intro hx
    have hi : algebraMap M N x ∈ D ⊓ (IsScalarTower.toAlgHom C M N).fieldRange :=
      ⟨hx, ⟨x, rfl⟩⟩
    rw [hinf, IntermediateField.mem_bot] at hi
    obtain ⟨c, hc⟩ := hi
    have heq : (c : M) = x := (algebraMap M N).injective hc
    exact heq ▸ c.property
  · intro hx
    exact D.algebraMap_mem ⟨x, hx⟩

/-- Changing a descended presentation to its equal pullback and
finite field preserves the canonical tensor bijection. -/
theorem isGoodFiniteLayer_of_descent (E : FiniteIntermediateField K N)
    (C : IntermediateField K M) (D : IntermediateField C N)
    (hE : D.restrictScalars K = E.val)
    (hC : FiniteIntermediateField.pullback K M E = C)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D N D.val)) :
    IsGoodFiniteLayer K M E := by
  subst C
  have hDfield : D = FiniteIntermediateField.overPullback K M E := by
    ext x
    exact SetLike.ext_iff.mp hE x
  subst D
  change Function.Bijective (AlgHom.liftEquiv (FiniteIntermediateField.pullback K M E) M
    (FiniteIntermediateField.overPullback K M E) N (FiniteIntermediateField.overPullback K M E).val)
  exact ⟨injective_tensor_lift_of_linearDisjoint (FiniteIntermediateField.overPullback K M E) hD,
      hsurj⟩

/-- Good finite fields are cofinal; goodness is proved from
finite tensor descent, rather than assumed as part of the interface. -/
theorem exists_goodFiniteLayer_ge [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Algebra.IsSeparable M N] (E : FiniteIntermediateField K N) :
    ∃ D : FiniteIntermediateField K N, E ≤ D ∧ IsGoodFiniteLayer K M D := by
  obtain ⟨C, D, hf, hE, hD, hi, e, he⟩ :=
    exists_finiteIntermediateField_tensor_descent K (M := M) E
  let : Module.Finite K D := hf
  let : Module.Finite C.val D := Module.Finite.of_restrictScalars_finite K C.val D
  let E' : FiniteIntermediateField K N := ⟨D.restrictScalars K, hf⟩
  have hC := FiniteIntermediateField.pullback_eq_of_inf K M C.val D hf hi
  have hmap : AlgHom.liftEquiv C.val M D N D.val = e.toAlgHom := by
    ext d
    change (1 : M) • (d : N) = e (1 ⊗ₜ[C.val] d)
    simpa only [one_smul, map_one, one_mul] using (he 1 d).symm
  refine ⟨E', hE, isGoodFiniteLayer_of_descent K M E' C.val D rfl hC hD ?_⟩
  rw [hmap]
  exact e.surjective

/-- Two finite fields have a common upper good finite field. -/
theorem exists_goodFiniteLayer_ge_pair [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Algebra.IsSeparable M N] (E E' : FiniteIntermediateField K N) :
    ∃ D : FiniteIntermediateField K N, E ≤ D ∧ E' ≤ D ∧ IsGoodFiniteLayer K M D := by
  obtain ⟨D, h, hD⟩ := exists_goodFiniteLayer_ge K M (FiniteIntermediateField.sup E E')
  exact ⟨D, (FiniteIntermediateField.le_sup_left E E').trans h,
    (FiniteIntermediateField.le_sup_right E E').trans h, hD⟩

/-- Goodness gives the finite relative degree. -/
theorem finrank_goodFiniteLayer (D : FiniteIntermediateField K N) (hD : IsGoodFiniteLayer K M D) :
    Module.finrank (FiniteIntermediateField.pullback K M D) D.val = Module.finrank M N := by
  rw [← Module.finrank_baseChange (R := M)]
  exact (goodFiniteLayerTensorEquiv K M D hD).toLinearEquiv.finrank_eq

/-- Goodness gives linear disjointness over the pullback. -/
theorem linearDisjoint_goodFiniteLayer (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) :
    (FiniteIntermediateField.overPullback K M D).LinearDisjoint M := by
  have hfield : IsField (M ⊗[FiniteIntermediateField.pullback K M D] D.val) :=
    (goodFiniteLayerTensorEquiv K M D hD).toMulEquiv.isField (Field.toIsField N)
  apply IntermediateField.LinearDisjoint.of_isField
  exact (Algebra.TensorProduct.comm (FiniteIntermediateField.pullback K M D) D.val
      M).toMulEquiv.isField hfield

/-- The pullback, as an index in the finite-layer system. -/
def FiniteIntermediateField.pullbackLayer (D : FiniteIntermediateField K N) :
    FiniteIntermediateField K M :=
  ⟨FiniteIntermediateField.pullback K M D, inferInstance⟩

/-- An inclusion of good finite fields is the tensor base change of
the corresponding inclusion of their pullbacks. -/
def goodFinitePairTensorEquiv (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D') :
    letI : Algebra (FiniteIntermediateField.pullback K M D) (FiniteIntermediateField.pullback K M
        D') :=
      (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M
          h)).toRingHom.toAlgebra
    letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
    D.val ⊗[FiniteIntermediateField.pullback K M D] (FiniteIntermediateField.pullback K M D')
        ≃ₐ[D.val] D'.val := by
  let C := FiniteIntermediateField.pullback K M D
  let C' := FiniteIntermediateField.pullback K M D'
  letI : Algebra C C' :=
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h)).toRingHom.toAlgebra
  letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : Algebra C D'.val := ((IntermediateField.inclusion h).comp
    (FiniteIntermediateField.pullbackTo K M D)).toRingHom.toAlgebra
  have : IsScalarTower C D.val D'.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C C' M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K C C' := IsScalarTower.of_algHom
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h))
  have : IsScalarTower C C' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C C' D'.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K D.val D'.val := IsScalarTower.of_algHom (IntermediateField.inclusion h)
  have : IsScalarTower K C D'.val := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact IsScalarTower.algebraMap_apply K M N x)
  letI : Module.Finite C C' := Module.Finite.of_restrictScalars_finite K C C'
  letI : Module.Finite C D'.val := Module.Finite.of_restrictScalars_finite K C D'.val
  letI : Module.Finite D.val D'.val := Module.Finite.of_restrictScalars_finite K D.val D'.val
  have hld := (linearDisjoint_goodFiniteLayer K M D hD).of_le_right' C'
  have : IsDomain (D.val ⊗[C] C') := hld.isDomain
  letI : Field (D.val ⊗[C] C') :=
    (Algebra.TensorProduct.isField_of_isAlgebraic C D.val C' (.inr inferInstance)).toField
  let f : D.val ⊗[C] C' →ₐ[D.val] D'.val := AlgHom.liftEquiv C D.val C' D'.val
    (IsScalarTower.toAlgHom C C' D'.val)
  have hdegree : Module.finrank C C' = Module.finrank D.val D'.val := by
    have h₁ := Module.finrank_mul_finrank C C' D'.val
    have h₂ := Module.finrank_mul_finrank C D.val D'.val
    rw [finrank_goodFiniteLayer K M D' hD'] at h₁
    rw [finrank_goodFiniteLayer K M D hD] at h₂
    exact Nat.eq_of_mul_eq_mul_right
      (by rw [← finrank_goodFiniteLayer K M D hD]; exact Module.finrank_pos)
      (h₁.trans h₂.symm |>.trans (Nat.mul_comm _ _))
  refine AlgEquiv.ofBijective f ⟨f.toRingHom.injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank D.val (D.val ⊗[C] C') = Module.finrank D.val D'.val from ?_)).mp
    f.toRingHom.injective
  rw [Module.finrank_baseChange]
  exact hdegree

/-- The pair isomorphism is the multiplication map on elements. -/
@[simp]
theorem goodFinitePairTensorEquiv_tmul (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (d : D.val) (a : FiniteIntermediateField.pullback K M D') :
    letI : Algebra (FiniteIntermediateField.pullback K M D) (FiniteIntermediateField.pullback K M
        D') :=
      (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M
          h)).toRingHom.toAlgebra
    letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
    goodFinitePairTensorEquiv K M D D' h hD hD'
      (d ⊗ₜ[FiniteIntermediateField.pullback K M D] a) =
      IntermediateField.inclusion h d * FiniteIntermediateField.pullbackTo K M D' a := by
  let : Algebra (FiniteIntermediateField.pullback K M D) (FiniteIntermediateField.pullback K M D')
      :=
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h)).toRingHom.toAlgebra
  let : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact Algebra.smul_def d (FiniteIntermediateField.pullbackTo K M D' a)

/-- The finite-layer norms commute with the inclusions
on every inclusion of good finite fields. -/
theorem goodFinitePair_norm (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (a : FiniteIntermediateField.pullback K M D') :
    FiniteIntermediateField.norm D D' h (FiniteIntermediateField.pullbackTo K M D' a) =
      FiniteIntermediateField.pullbackTo K M D
        (FiniteIntermediateField.norm (FiniteIntermediateField.pullbackLayer K M D)
          (FiniteIntermediateField.pullbackLayer K M D') (FiniteIntermediateField.pullback_mono K M
              h) a) := by
  let C := FiniteIntermediateField.pullback K M D
  let C' := FiniteIntermediateField.pullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h)).toRingHom.toAlgebra
  let : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K C C' := IsScalarTower.of_algHom
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h))
  let : Module.Finite C C' := Module.Finite.of_restrictScalars_finite K C C'
  have hn := norm_eq_of_tensorEquiv C D.val C'
    (goodFinitePairTensorEquiv K M D D' h hD hD') a
  rw [goodFinitePairTensorEquiv_tmul, map_one, one_mul] at hn
  exact hn

/-- The lower finite field is linearly disjoint from the upper pullback
over the lower pullback, under the inclusions. -/
theorem linearDisjoint_goodFinitePair (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) :
    letI : Algebra (FiniteIntermediateField.pullback K M D) (FiniteIntermediateField.pullback K M
        D') :=
      (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M
          h)).toRingHom.toAlgebra
    letI : IsScalarTower (FiniteIntermediateField.pullback K M D) (FiniteIntermediateField.pullback
        K M D') N :=
      IsScalarTower.of_algebraMap_eq' rfl
    (FiniteIntermediateField.overPullback K M D).LinearDisjoint (FiniteIntermediateField.pullback K
        M D') := by
  let C := FiniteIntermediateField.pullback K M D
  let C' := FiniteIntermediateField.pullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h)).toRingHom.toAlgebra
  let : IsScalarTower C C' M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C C' N := IsScalarTower.of_algebraMap_eq' rfl
  exact (linearDisjoint_goodFiniteLayer K M D hD).of_le_right' C'

/-- The upper good finite field is precisely the compositum
of the lower finite field with the upper pullback. -/
theorem goodFinitePair_sup_eq (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D') :
    D.val ⊔ (FiniteIntermediateField.pullback K M D').map (IsScalarTower.toAlgHom K M N) = D'.val
        := by
  let C := FiniteIntermediateField.pullback K M D
  let C' := FiniteIntermediateField.pullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h)).toRingHom.toAlgebra
  let : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let A := D.val
  let B := C'.map (IsScalarTower.toAlgHom K M N)
  let e := goodFinitePairTensorEquiv K M D D' h hD hD'
  apply le_antisymm
  · apply sup_le h
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  · intro x hx
    obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
    have hmem (z : D.val ⊗[C] C') : (e z : N) ∈ A ⊔ B := by
      induction z using TensorProduct.inductionOn with
      | tmul d a =>
        rw [goodFinitePairTensorEquiv_tmul]
        apply mul_mem
        · exact (show A ≤ A ⊔ B from le_sup_left) d.property
        · exact (show B ≤ A ⊔ B from le_sup_right) ⟨a, a.property, rfl⟩
      | add z w hz hw =>
        simpa only [map_add, IntermediateField.coe_add] using add_mem hz hw
    have heq : (e z : N) = x := congrArg (fun y : D'.val => (y : N)) hz
    exact heq ▸ hmem z

/-- The pullback inclusion is the inclusion on ambient elements. -/
@[simp]
theorem FiniteIntermediateField.pullbackTo_coe (D : FiniteIntermediateField K N) (a :
    FiniteIntermediateField.pullback K M D) :
    (FiniteIntermediateField.pullbackTo K M D a : N) = algebraMap M N (a : M) := rfl

/-- The two inclusion squares commute on each element. -/
@[simp]
theorem FiniteIntermediateField.pullbackTo_inclusion {D D' : FiniteIntermediateField K N} (h : D ≤
    D')
    (a : FiniteIntermediateField.pullback K M D) :
    FiniteIntermediateField.pullbackTo K M D'
        (IntermediateField.inclusion (FiniteIntermediateField.pullback_mono K M h) a) =
      IntermediateField.inclusion h (FiniteIntermediateField.pullbackTo K M D a) := rfl

end FontaineWintenberger
