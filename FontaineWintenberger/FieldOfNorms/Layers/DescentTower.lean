/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Layers.Descent

/-!
# Simultaneous finite descent in a separable tower

Finite coefficient fields in a finite separable tower can be chosen
simultaneously good for both levels, as in Wintenberger, paragraph 3.1.1.

## Main definitions

* `tensorEquivOfLinearDisjoint`: The multiplication map is an isomorphism when linearly disjoint
  finite fields generate the ambient extension.
* `finiteDescentIntersection`: The intersection with an embedded middle field, viewed inside that
  field.
* `finiteDescentIntersectionTo`: The canonical inclusion of the middle intersection into the upper
  field.
* `finiteDescentIntersectionTensorEquiv`: The intersection descends the middle field by the
  canonical map.
* `finiteDescentUpperTensorEquiv`: The upper canonical tensor map is an isomorphism.

## Main results

* `injective_tensor_lift_of_linearDisjoint`: Linear disjointness makes the canonical tensor map
  injective.
* `linearDisjoint_finiteDescentIntersection`: Restricting the disjoint field to the middle
  intersection preserves linear disjointness with the base.
* `surjective_finiteDescentIntersection_tensor_lift`: Containing the middle primitive element makes
  the lower canonical tensor map onto.
* `finrank_finiteDescentIntersection`: The middle field degree is the degree of the finite
  intersection.
* `surjective_finiteDescentUpper_tensor_lift`: The upper canonical multiplication map remains onto
  after replacing the base by the middle field.
* `finrank_finiteDescentUpper`: Equality of lower and total degrees forces the upper degree, as in
  the simultaneous descent argument.
* `finiteDescentUpperTensorEquiv_tmul`: The upper isomorphism uses the multiplication map on
  elements.
* `finiteDescentIntersection_map`: Viewed in the ambient field, the constructed middle field is
  exactly the intersection of the finite field and the middle field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

section Tensor

variable {C M P : Type*} [Field C] [Field M] [Field P]
    [Algebra C M] [Algebra C P] [Algebra M P] [IsScalarTower C M P]

/-- Linear disjointness makes the canonical tensor map injective. -/
theorem injective_tensor_lift_of_linearDisjoint (D : IntermediateField C P)
    [Module.Finite C D] (hD : D.LinearDisjoint M) :
    Function.Injective (AlgHom.liftEquiv C M D P D.val) := by
  have : IsDomain (D ⊗[C] M) := hD.isDomain
  have : IsDomain (M ⊗[C] D) :=
    (Algebra.TensorProduct.comm C M D).toMulEquiv.isDomain
  let : Field (M ⊗[C] D) :=
    (Algebra.TensorProduct.isField_of_isAlgebraic C M D (.inr inferInstance)).toField
  exact (AlgHom.liftEquiv C M D P D.val).toRingHom.injective

/-- The multiplication map is an isomorphism when linearly disjoint
finite fields generate the ambient extension. -/
def tensorEquivOfLinearDisjoint (D : IntermediateField C P)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val)) :
    M ⊗[C] D ≃ₐ[M] P :=
  AlgEquiv.ofBijective (AlgHom.liftEquiv C M D P D.val)
    ⟨injective_tensor_lift_of_linearDisjoint D hD, hsurj⟩

@[simp]
theorem tensorEquivOfLinearDisjoint_tmul (D : IntermediateField C P)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val)) (m : M) (d : D) :
    tensorEquivOfLinearDisjoint D hD hsurj (m ⊗ₜ[C] d) =
      algebraMap M P m * (d : P) :=
  Algebra.smul_def m (d : P)

variable {N : Type*} [Field N] [Algebra C N] [Algebra M N]
    [Algebra N P] [IsScalarTower C M N] [IsScalarTower C N P]
    [IsScalarTower M N P]

/-- The intersection with an embedded middle field, viewed inside that field. -/
def finiteDescentIntersection (D : IntermediateField C P) : IntermediateField C N :=
  D.comap (IsScalarTower.toAlgHom C N P)

/-- The canonical inclusion of the middle intersection into the upper field. -/
def finiteDescentIntersectionTo (D : IntermediateField C P) :
    finiteDescentIntersection (N := N) D →ₐ[C] D :=
  ((IsScalarTower.toAlgHom C N P).comp (finiteDescentIntersection (N := N) D).val).codRestrict
    D.toSubalgebra fun x => x.property

/-- Restricting the disjoint field to the middle intersection
preserves linear disjointness with the base. -/
theorem linearDisjoint_finiteDescentIntersection (D : IntermediateField C P)
    (hD : D.LinearDisjoint M) :
    (finiteDescentIntersection (N := N) D).LinearDisjoint M := by
  let B := finiteDescentIntersection (N := N) D
  let b := Module.Free.chooseBasis C B
  apply IntermediateField.LinearDisjoint.of_basis_left b
  apply LinearIndependent.of_comp (IsScalarTower.toAlgHom M N P).toLinearMap
  have h := hD.linearIndependent_left (b.linearIndependent.map'
    (finiteDescentIntersectionTo (N := N) D).toLinearMap
    (LinearMap.ker_eq_bot.mpr (finiteDescentIntersectionTo (N := N) D).injective))
  exact h

/-- The intersection is finite when the finite field is. -/
instance finite_finiteDescentIntersection (D : IntermediateField C P)
    [Module.Finite C D] : Module.Finite C (finiteDescentIntersection (N := N) D) :=
  Module.Finite.of_injective (finiteDescentIntersectionTo (N := N) D).toLinearMap
    (finiteDescentIntersectionTo (N := N) D).injective

omit [Algebra M P] [IsScalarTower C M P] [IsScalarTower M N P] in
/-- Containing the middle primitive element makes the lower
canonical tensor map onto. -/
theorem surjective_finiteDescentIntersection_tensor_lift (D : IntermediateField C P)
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) :
    Function.Surjective (AlgHom.liftEquiv C M
      (finiteDescentIntersection (N := N) D) N
      (finiteDescentIntersection (N := N) D).val) := by
  let B := finiteDescentIntersection (N := N) D
  let f : M ⊗[C] B →ₐ[M] N := AlgHom.liftEquiv C M B N B.val
  have hr : (⊤ : Subalgebra M N) ≤ f.range := by
    rw [← b.adjoin_gen_eq_top]
    apply Algebra.adjoin_le
    rintro y (rfl : y = b.gen)
    refine ⟨1 ⊗ₜ[C] ⟨b.gen, hgen⟩, ?_⟩
    exact one_smul M b.gen
  intro y
  exact hr trivial

/-- The intersection descends the middle field by the canonical map. -/
def finiteDescentIntersectionTensorEquiv (D : IntermediateField C P)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) :
    M ⊗[C] (finiteDescentIntersection (N := N) D) ≃ₐ[M] N :=
  tensorEquivOfLinearDisjoint _ (linearDisjoint_finiteDescentIntersection D hD)
    (surjective_finiteDescentIntersection_tensor_lift D b hgen)

/-- The middle field degree is the degree of the finite intersection. -/
theorem finrank_finiteDescentIntersection (D : IntermediateField C P)
    [Module.Finite C D] (hD : D.LinearDisjoint M)
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) :
    Module.finrank C (finiteDescentIntersection (N := N) D) = Module.finrank M N := by
  rw [← Module.finrank_baseChange (R := M)]
  exact (finiteDescentIntersectionTensorEquiv D hD b hgen).toLinearEquiv.finrank_eq

/-- The intersection acts on the upper finite field through its inclusion. -/
instance finiteDescentIntersectionAlgebra (D : IntermediateField C P) :
    Algebra (finiteDescentIntersection (N := N) D) D :=
  (finiteDescentIntersectionTo (N := N) D).toRingHom.toAlgebra

instance finiteDescentIntersection_scalarTower (D : IntermediateField C P) :
    IsScalarTower C (finiteDescentIntersection (N := N) D) D :=
  IsScalarTower.of_algHom (finiteDescentIntersectionTo (N := N) D)

instance finiteDescentIntersection_scalarTower_top (D : IntermediateField C P) :
    IsScalarTower (finiteDescentIntersection (N := N) D) D P :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [IsScalarTower C M N] in
/-- The upper canonical multiplication map remains onto after replacing the
base by the middle field. -/
theorem surjective_finiteDescentUpper_tensor_lift (D : IntermediateField C P)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val)) :
    Function.Surjective (AlgHom.liftEquiv (finiteDescentIntersection (N := N) D) N D P
      (IsScalarTower.toAlgHom (finiteDescentIntersection (N := N) D) D P)) := by
  let B := finiteDescentIntersection (N := N) D
  let f : N ⊗[B] D →ₐ[N] P := AlgHom.liftEquiv B N D P (IsScalarTower.toAlgHom B D P)
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  induction z using TensorProduct.inductionOn with
  | tmul m d =>
    refine ⟨algebraMap M N m ⊗ₜ[B] d, ?_⟩
    change algebraMap M N m • (d : P) = m • (d : P)
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply M N P]
  | add z w hz hw =>
    obtain ⟨z', hz'⟩ := hz
    obtain ⟨w', hw'⟩ := hw
    exact ⟨z' + w', by simp only [map_add, hz', hw']⟩

/-- Equality of lower and total degrees forces the upper degree,
as in the simultaneous descent argument. -/
theorem finrank_finiteDescentUpper (D : IntermediateField C P)
    [Module.Finite C D] [Module.Finite M N] [Module.Finite N P]
    (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val))
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) :
    Module.finrank (finiteDescentIntersection (N := N) D) D = Module.finrank N P := by
  let B := finiteDescentIntersection (N := N) D
  have : Module.Finite B D := Module.Finite.of_restrictScalars_finite C B D
  have hCD : Module.finrank C D = Module.finrank M P := by
    rw [← Module.finrank_baseChange (R := M)]
    exact (tensorEquivOfLinearDisjoint D hD hsurj).toLinearEquiv.finrank_eq
  have hCB := finrank_finiteDescentIntersection D hD b hgen
  have hBD := Module.finrank_mul_finrank C B D
  have hNP := Module.finrank_mul_finrank M N P
  rw [hCB, hCD] at hBD
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := M) (M := N))
    (hBD.trans hNP.symm)

/-- Finiteness is retained for the upper extension over the intersection. -/
instance finite_finiteDescentUpper (D : IntermediateField C P) [Module.Finite C D] :
    Module.Finite (finiteDescentIntersection (N := N) D) D :=
  Module.Finite.of_restrictScalars_finite C (finiteDescentIntersection (N := N) D) D

/-- The upper canonical tensor map is an isomorphism. -/
def finiteDescentUpperTensorEquiv (D : IntermediateField C P)
    [Module.Finite C D] [Module.Finite M N] [Module.Finite N P]
    (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val))
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) :
    N ⊗[finiteDescentIntersection (N := N) D] D ≃ₐ[N] P := by
  let B := finiteDescentIntersection (N := N) D
  let f : N ⊗[B] D →ₐ[N] P := AlgHom.liftEquiv B N D P (IsScalarTower.toAlgHom B D P)
  have hf := surjective_finiteDescentUpper_tensor_lift (N := N) D hsurj
  refine AlgEquiv.ofBijective f ⟨?_, hf⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank N (N ⊗[B] D) = Module.finrank N P from ?_)).mpr hf
  rw [Module.finrank_baseChange]
  exact finrank_finiteDescentUpper D hD hsurj b hgen

/-- The upper isomorphism uses the multiplication map on elements. -/
@[simp]
theorem finiteDescentUpperTensorEquiv_tmul (D : IntermediateField C P)
    [Module.Finite C D] [Module.Finite M N] [Module.Finite N P]
    (hD : D.LinearDisjoint M)
    (hsurj : Function.Surjective (AlgHom.liftEquiv C M D P D.val))
    (b : PowerBasis M N) (hgen : algebraMap N P b.gen ∈ D) (n : N) (d : D) :
    finiteDescentUpperTensorEquiv D hD hsurj b hgen
      (n ⊗ₜ[finiteDescentIntersection (N := N) D] d) =
      algebraMap N P n * (d : P) :=
  Algebra.smul_def n (d : P)

/-- Viewed in the ambient field, the constructed middle field is
exactly the intersection of the finite field and the middle field. -/
theorem finiteDescentIntersection_map (D : IntermediateField C P) :
    (finiteDescentIntersection (N := N) D).map (IsScalarTower.toAlgHom C N P) =
      D ⊓ (IsScalarTower.toAlgHom C N P).fieldRange :=
  IntermediateField.map_comap_eq _ _

end Tensor

section CofinalTower

variable (K : Type*) [Field K] {M N P : Type*} [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower M N P] [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]

/-- Simultaneous good finite fields are cofinal in a finite separable
tower. The three tensor isomorphisms are constructed canonical multiplication
maps, and the middle field is the intersection. -/
theorem exists_finiteIntermediateField_tensor_descent_tower (D₀ : FiniteIntermediateField K P) :
    ∃ (C : FiniteIntermediateField K M) (D : IntermediateField C.val P),
      Module.Finite K (D.restrictScalars K) ∧
      D₀.val ≤ D.restrictScalars K ∧
      D.LinearDisjoint M ∧
      D ⊓ (IsScalarTower.toAlgHom C.val M P).fieldRange = ⊥ ∧
      let B := finiteDescentIntersection (N := N) D
      Module.Finite K (B.restrictScalars K) ∧
      B.LinearDisjoint M ∧
      B ⊓ (IsScalarTower.toAlgHom C.val M N).fieldRange = ⊥ ∧
      (∃ e : M ⊗[C.val] D ≃ₐ[M] P,
        ∀ (m : M) (d : D), e (m ⊗ₜ[C.val] d) = algebraMap M P m * (d : P)) ∧
      (∃ e : M ⊗[C.val] B ≃ₐ[M] N,
        ∀ (m : M) (b : B), e (m ⊗ₜ[C.val] b) = algebraMap M N m * (b : N)) ∧
      ∃ e : N ⊗[B] D ≃ₐ[N] P,
        ∀ (n : N) (d : D), e (n ⊗ₜ[B] d) = algebraMap N P n * (d : P) := by
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let : Algebra.IsAlgebraic K P := Algebra.IsAlgebraic.trans K M P
  let b := Field.powerBasisOfFiniteOfSeparable M N
  let A : FiniteIntermediateField K P := ⟨IntermediateField.adjoin K {algebraMap N P b.gen},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩
  obtain ⟨C, D, hfinite, hcontains, hD, hinf, eMP, heMP⟩ :=
    exists_finiteIntermediateField_tensor_descent K (M := M) (FiniteIntermediateField.sup D₀ A)
  let : Module.Finite K D := hfinite
  let : Module.Finite C.val D := Module.Finite.of_restrictScalars_finite K C.val D
  let B := finiteDescentIntersection (N := N) D
  have hgen : algebraMap N P b.gen ∈ D := hcontains
    ((FiniteIntermediateField.le_sup_right D₀ A)
      (IntermediateField.mem_adjoin_simple_self K (algebraMap N P b.gen)))
  have hB : B.LinearDisjoint M := linearDisjoint_finiteDescentIntersection D hD
  have hBinf : B ⊓ (IsScalarTower.toAlgHom C.val M N).fieldRange = ⊥ := by
    apply IntermediateField.LinearDisjoint.inf_eq_bot
    rw [IntermediateField.linearDisjoint_iff']
    simpa only [AlgHom.fieldRange_toSubalgebra] using hB
  have hf : AlgHom.liftEquiv C.val M D P D.val = eMP.toAlgHom := by
    ext d
    change (1 : M) • (d : P) = eMP (1 ⊗ₜ[C.val] d)
    simpa only [one_smul, map_one, one_mul] using (heMP 1 d).symm
  have hsurj : Function.Surjective (AlgHom.liftEquiv C.val M D P D.val) := by
    rw [hf]
    exact eMP.surjective
  have hD₀ : D₀.val ≤ D.restrictScalars K :=
    fun _ hx => hcontains (FiniteIntermediateField.le_sup_left D₀ A hx)
  have hBfinite : Module.Finite K (B.restrictScalars K) := by
    let j : B.restrictScalars K →ₐ[K] D.restrictScalars K :=
      ((IsScalarTower.toAlgHom K N P).comp (B.restrictScalars K).val).codRestrict
        (D.restrictScalars K).toSubalgebra fun x => x.property
    exact Module.Finite.of_injective j.toLinearMap j.injective
  refine ⟨C, D, hfinite, hD₀, hD, hinf,
    hBfinite, hB, hBinf, ⟨eMP, heMP⟩,
    ⟨finiteDescentIntersectionTensorEquiv D hD b hgen, ?_⟩,
    ⟨finiteDescentUpperTensorEquiv D hD hsurj b hgen, ?_⟩⟩
  · intro m d
    exact Algebra.smul_def m (d : N)
  · exact finiteDescentUpperTensorEquiv_tmul D hD hsurj b hgen

/-- Two prescribed finite fields have a common upper field which is good
simultaneously at both levels of the separable tower. -/
theorem exists_common_finiteIntermediateField_tensor_descent_tower
    (D₁ D₂ : FiniteIntermediateField K P) :
    ∃ (C : FiniteIntermediateField K M) (D : IntermediateField C.val P),
      Module.Finite K (D.restrictScalars K) ∧
      D₁.val ≤ D.restrictScalars K ∧ D₂.val ≤ D.restrictScalars K ∧
      D ⊓ (IsScalarTower.toAlgHom C.val M P).fieldRange = ⊥ ∧
      let B := finiteDescentIntersection (N := N) D
      (∃ e : M ⊗[C.val] D ≃ₐ[M] P,
        ∀ (m : M) (d : D), e (m ⊗ₜ[C.val] d) = algebraMap M P m * (d : P)) ∧
      (∃ e : M ⊗[C.val] B ≃ₐ[M] N,
        ∀ (m : M) (b : B), e (m ⊗ₜ[C.val] b) = algebraMap M N m * (b : N)) ∧
      ∃ e : N ⊗[B] D ≃ₐ[N] P,
        ∀ (n : N) (d : D), e (n ⊗ₜ[B] d) = algebraMap N P n * (d : P) := by
  obtain ⟨C, D, hf, hc, _hD, hi, _hBf, _hB, _hBi, eMP, eMN, eNP⟩ :=
    exists_finiteIntermediateField_tensor_descent_tower K (M := M) (N := N)
        (FiniteIntermediateField.sup D₁ D₂)
  exact ⟨C, D, hf, (fun _ hx => hc (FiniteIntermediateField.le_sup_left D₁ D₂ hx)),
    (fun _ hx => hc (FiniteIntermediateField.le_sup_right D₁ D₂ hx)), hi, eMP, eMN, eNP⟩

end CofinalTower

end FontaineWintenberger
