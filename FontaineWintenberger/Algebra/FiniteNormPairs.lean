module

public import FontaineWintenberger.Algebra.FiniteDescentTower
public import FontaineWintenberger.Algebra.NormBaseChange

/-!
# Original norm identities on good finite fields

The finite fields used in the covariant field-of-norms construction are actual
finite intermediate fields. Their coefficient fields are their original
pullbacks to the base; cofinality is proved by finite tensor descent.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
    {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The original pullback of an actual finite field along the base inclusion. -/
def finiteLayerPullback (D : FiniteLayer K N) : IntermediateField K M :=
  D.val.comap (IsScalarTower.toAlgHom K M N)

/-- The original inclusion of the pullback into the actual finite field. -/
def finiteLayerPullbackTo (D : FiniteLayer K N) :
    finiteLayerPullback K M D →ₐ[K] D.val :=
  ((IsScalarTower.toAlgHom K M N).comp (finiteLayerPullback K M D).val).codRestrict
    D.val.toSubalgebra fun x => x.property

instance finiteLayerPullback_finite (D : FiniteLayer K N) :
    Module.Finite K (finiteLayerPullback K M D) :=
  Module.Finite.of_injective (finiteLayerPullbackTo K M D).toLinearMap
    (finiteLayerPullbackTo K M D).injective

/-- The same original finite field, as an intermediate field over its pullback. -/
def finiteLayerOverPullback (D : FiniteLayer K N) :
    IntermediateField (finiteLayerPullback K M D) N where
  __ := D.val.toSubfield
  algebraMap_mem' c := c.property

instance finiteLayerPullbackAlgebra (D : FiniteLayer K N) :
    Algebra (finiteLayerPullback K M D) D.val :=
  (finiteLayerOverPullback K M D).algebra

instance finiteLayerPullback_scalarTower (D : FiniteLayer K N) :
    IsScalarTower K (finiteLayerPullback K M D) D.val :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact IsScalarTower.algebraMap_apply K M N x)

instance finiteLayerPullback_scalarTower_top (D : FiniteLayer K N) :
    IsScalarTower (finiteLayerPullback K M D) D.val N :=
  IsScalarTower.of_algebraMap_eq' rfl

instance finiteLayerOverPullback_finite (D : FiniteLayer K N) :
    Module.Finite (finiteLayerPullback K M D) D.val :=
  Module.Finite.of_restrictScalars_finite K _ _

/-- The original multiplication map over the original pullback field. -/
def finiteLayerTensorMap (D : FiniteLayer K N) :
    M ⊗[finiteLayerPullback K M D] D.val →ₐ[M] N :=
  AlgHom.liftEquiv (finiteLayerPullback K M D) M D.val N
    (IsScalarTower.toAlgHom (finiteLayerPullback K M D) D.val N)

/-- An actual finite field is good when its canonical multiplication map is bijective. -/
def IsGoodFiniteLayer (D : FiniteLayer K N) : Prop :=
  Function.Bijective (finiteLayerTensorMap K M D)

/-- The canonical tensor isomorphism of a good actual finite field. -/
def goodFiniteLayerTensorEquiv (D : FiniteLayer K N) (hD : IsGoodFiniteLayer K M D) :
    M ⊗[finiteLayerPullback K M D] D.val ≃ₐ[M] N :=
  AlgEquiv.ofBijective (finiteLayerTensorMap K M D) hD

@[simp]
theorem goodFiniteLayerTensorEquiv_tmul (D : FiniteLayer K N)
    (hD : IsGoodFiniteLayer K M D) (m : M) (d : D.val) :
    goodFiniteLayerTensorEquiv K M D hD (m ⊗ₜ[finiteLayerPullback K M D] d) =
      algebraMap M N m * (d : N) :=
  Algebra.smul_def m (d : N)

/-- Original pullbacks preserve inclusions of the original finite fields. -/
theorem finiteLayerPullback_mono {D D' : FiniteLayer K N} (h : D ≤ D') :
    finiteLayerPullback K M D ≤ finiteLayerPullback K M D' :=
  fun _ hx => h hx

/-- The coefficient field supplied by finite descent equals the original
pullback; the auxiliary presentation introduces no different finite field. -/
theorem finiteLayerPullback_eq_of_inf (C : IntermediateField K M)
    (D : IntermediateField C N) (hfin : Module.Finite K (D.restrictScalars K))
    (hinf : D ⊓ (IsScalarTower.toAlgHom C M N).fieldRange = ⊥) :
    finiteLayerPullback K M ⟨D.restrictScalars K, hfin⟩ = C := by
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

/-- Changing a descended presentation to its equal original pullback and
original finite field preserves the canonical tensor bijection. -/
theorem isGoodFiniteLayer_of_descent (E : FiniteLayer K N)
    (C : IntermediateField K M) (D : IntermediateField C N)
    (hE : D.restrictScalars K = E.val)
    (hC : finiteLayerPullback K M E = C)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D N D.val)) :
    IsGoodFiniteLayer K M E := by
  subst C
  have hDfield : D = finiteLayerOverPullback K M E := by
    ext x
    exact SetLike.ext_iff.mp hE x
  subst D
  change Function.Bijective (AlgHom.liftEquiv (finiteLayerPullback K M E) M
    (finiteLayerOverPullback K M E) N (finiteLayerOverPullback K M E).val)
  exact ⟨injective_tensor_lift_of_linearDisjoint (finiteLayerOverPullback K M E) hD, hsurj⟩

/-- Good original finite fields are cofinal; goodness is proved from actual
finite tensor descent, rather than assumed as part of the interface. -/
theorem exists_goodFiniteLayer_ge [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Algebra.IsSeparable M N] (E : FiniteLayer K N) :
    ∃ D : FiniteLayer K N, E ≤ D ∧ IsGoodFiniteLayer K M D := by
  obtain ⟨C, D, hf, hE, hD, hi, e, he⟩ :=
    exists_finiteLayer_tensor_descent K (M := M) E
  let : Module.Finite K D := hf
  let : Module.Finite C.val D := Module.Finite.of_restrictScalars_finite K C.val D
  let E' : FiniteLayer K N := ⟨D.restrictScalars K, hf⟩
  have hC := finiteLayerPullback_eq_of_inf K M C.val D hf hi
  have hmap : AlgHom.liftEquiv C.val M D N D.val = e.toAlgHom := by
    ext d
    change (1 : M) • (d : N) = e (1 ⊗ₜ[C.val] d)
    simpa only [one_smul, map_one, one_mul] using (he 1 d).symm
  refine ⟨E', hE, isGoodFiniteLayer_of_descent K M E' C.val D rfl hC hD ?_⟩
  rw [hmap]
  exact e.surjective

/-- Two original finite fields have a common upper good finite field. -/
theorem exists_goodFiniteLayer_ge_pair [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Algebra.IsSeparable M N] (E E' : FiniteLayer K N) :
    ∃ D : FiniteLayer K N, E ≤ D ∧ E' ≤ D ∧ IsGoodFiniteLayer K M D := by
  obtain ⟨D, h, hD⟩ := exists_goodFiniteLayer_ge K M (FiniteLayer.sup E E')
  exact ⟨D, (FiniteLayer.le_sup_left E E').trans h,
    (FiniteLayer.le_sup_right E E').trans h, hD⟩

/-- Goodness gives the original finite relative degree. -/
theorem finrank_goodFiniteLayer (D : FiniteLayer K N) (hD : IsGoodFiniteLayer K M D) :
    Module.finrank (finiteLayerPullback K M D) D.val = Module.finrank M N := by
  rw [← Module.finrank_baseChange (R := M)]
  exact (goodFiniteLayerTensorEquiv K M D hD).toLinearEquiv.finrank_eq

/-- Goodness gives actual linear disjointness over the original pullback. -/
theorem linearDisjoint_goodFiniteLayer (D : FiniteLayer K N)
    (hD : IsGoodFiniteLayer K M D) :
    (finiteLayerOverPullback K M D).LinearDisjoint M := by
  have hfield : IsField (M ⊗[finiteLayerPullback K M D] D.val) :=
    (goodFiniteLayerTensorEquiv K M D hD).toMulEquiv.isField (Field.toIsField N)
  apply IntermediateField.LinearDisjoint.of_isField
  exact (Algebra.TensorProduct.comm (finiteLayerPullback K M D) D.val M).toMulEquiv.isField hfield

/-- The original pullback, as an index in the original finite-layer system. -/
def finiteLayerPullbackLayer (D : FiniteLayer K N) : FiniteLayer K M :=
  ⟨finiteLayerPullback K M D, inferInstance⟩

/-- An inclusion of good finite fields is the actual tensor base change of
the corresponding inclusion of their original pullbacks. -/
def goodFinitePairTensorEquiv (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D') :
    letI : Algebra (finiteLayerPullback K M D) (finiteLayerPullback K M D') :=
      (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
    letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
    D.val ⊗[finiteLayerPullback K M D] (finiteLayerPullback K M D') ≃ₐ[D.val] D'.val := by
  let C := finiteLayerPullback K M D
  let C' := finiteLayerPullback K M D'
  letI : Algebra C C' :=
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
  letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : Algebra C D'.val := ((IntermediateField.inclusion h).comp
    (finiteLayerPullbackTo K M D)).toRingHom.toAlgebra
  have : IsScalarTower C D.val D'.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower C C' M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K C C' := IsScalarTower.of_algHom
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h))
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

/-- The pair isomorphism is the original multiplication map on original elements. -/
@[simp]
theorem goodFinitePairTensorEquiv_tmul (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (d : D.val) (a : finiteLayerPullback K M D') :
    letI : Algebra (finiteLayerPullback K M D) (finiteLayerPullback K M D') :=
      (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
    letI : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
    goodFinitePairTensorEquiv K M D D' h hD hD'
      (d ⊗ₜ[finiteLayerPullback K M D] a) =
      IntermediateField.inclusion h d * finiteLayerPullbackTo K M D' a := by
  let : Algebra (finiteLayerPullback K M D) (finiteLayerPullback K M D') :=
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
  let : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact Algebra.smul_def d (finiteLayerPullbackTo K M D' a)

/-- The original finite-layer norms commute with the original inclusions
on every inclusion of good finite fields. -/
theorem goodFinitePair_norm (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (a : finiteLayerPullback K M D') :
    FiniteLayer.norm D D' h (finiteLayerPullbackTo K M D' a) =
      finiteLayerPullbackTo K M D
        (FiniteLayer.norm (finiteLayerPullbackLayer K M D)
          (finiteLayerPullbackLayer K M D') (finiteLayerPullback_mono K M h) a) := by
  let C := finiteLayerPullback K M D
  let C' := finiteLayerPullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
  let : Algebra D.val D'.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K C C' := IsScalarTower.of_algHom
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h))
  let : Module.Finite C C' := Module.Finite.of_restrictScalars_finite K C C'
  have hn := norm_eq_of_tensorEquiv C D.val C'
    (goodFinitePairTensorEquiv K M D D' h hD hD') a
  rw [goodFinitePairTensorEquiv_tmul, map_one, one_mul] at hn
  exact hn

/-- The lower finite field is linearly disjoint from the upper pullback
over the lower pullback, under the actual original inclusions. -/
theorem linearDisjoint_goodFinitePair (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) :
    letI : Algebra (finiteLayerPullback K M D) (finiteLayerPullback K M D') :=
      (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
    letI : IsScalarTower (finiteLayerPullback K M D) (finiteLayerPullback K M D') N :=
      IsScalarTower.of_algebraMap_eq' rfl
    (finiteLayerOverPullback K M D).LinearDisjoint (finiteLayerPullback K M D') := by
  let C := finiteLayerPullback K M D
  let C' := finiteLayerPullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
  let : IsScalarTower C C' M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C C' N := IsScalarTower.of_algebraMap_eq' rfl
  exact (linearDisjoint_goodFiniteLayer K M D hD).of_le_right' C'

/-- The actual upper good finite field is precisely the original compositum
of the lower finite field with the upper pullback. -/
theorem goodFinitePair_sup_eq (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D') :
    D.val ⊔ (finiteLayerPullback K M D').map (IsScalarTower.toAlgHom K M N) = D'.val := by
  let C := finiteLayerPullback K M D
  let C' := finiteLayerPullback K M D'
  let : Algebra C C' :=
    (IntermediateField.inclusion (finiteLayerPullback_mono K M h)).toRingHom.toAlgebra
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

/-- The pullback inclusion is the original inclusion on actual ambient elements. -/
@[simp]
theorem finiteLayerPullbackTo_coe (D : FiniteLayer K N) (a : finiteLayerPullback K M D) :
    (finiteLayerPullbackTo K M D a : N) = algebraMap M N (a : M) := rfl

/-- The two original inclusion squares commute on each original element. -/
@[simp]
theorem finiteLayerPullbackTo_inclusion {D D' : FiniteLayer K N} (h : D ≤ D')
    (a : finiteLayerPullback K M D) :
    finiteLayerPullbackTo K M D'
        (IntermediateField.inclusion (finiteLayerPullback_mono K M h) a) =
      IntermediateField.inclusion h (finiteLayerPullbackTo K M D a) := rfl

end FontaineWintenberger
