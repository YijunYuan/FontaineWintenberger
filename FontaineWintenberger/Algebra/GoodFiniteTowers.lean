/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteNormPairs

/-!
# Canonical good finite fields in a separable tower

The simultaneous tensor descent of Wintenberger, paragraph 3.1.1, gives
cofinal simultaneous goodness for the original finite fields and their
canonical pullbacks. These are the stages used for covariant composition.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

section CanonicalTensor

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
    {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- An actual multiplication isomorphism over a field equal to the original
pullback proves intrinsic goodness, independently of its scalar presentation. -/
theorem isGoodFiniteLayer_of_original_tensor (E : FiniteLayer K N)
    (C : IntermediateField K M) (hC : finiteLayerPullback K M E = C)
    [aCE : Algebra C E.val]
    (ha : ∀ c : C, (algebraMap C E.val c : N) = algebraMap M N (c : M))
    (e : M ⊗[C] E.val ≃ₐ[M] N)
    (he : ∀ (m : M) (d : E.val), e (m ⊗ₜ[C] d) = algebraMap M N m * (d : N)) :
    IsGoodFiniteLayer K M E := by
  subst C
  have hA : aCE = finiteLayerPullbackAlgebra K M E := by
    apply Algebra.algebra_ext
    intro c
    apply Subtype.ext
    exact ha c
  subst aCE
  have hmap : finiteLayerTensorMap K M E = e.toAlgHom := by
    ext d
    change (1 : M) • (d : N) = e (1 ⊗ₜ[finiteLayerPullback K M E] d)
    simpa only [one_smul, map_one, one_mul] using (he 1 d).symm
  unfold IsGoodFiniteLayer
  rw [hmap]
  exact e.bijective

end CanonicalTensor

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    {P : Type*} [Field P] [Algebra K P] [Algebra M P] [Algebra N P]
    [IsScalarTower K M P] [IsScalarTower K N P] [IsScalarTower M N P]

/-- Iterated original pullback is literally the original composite pullback. -/
theorem finiteLayerPullback_tower (D : FiniteLayer K P) :
    finiteLayerPullback K M (finiteLayerPullbackLayer K N D) = finiteLayerPullback K M D := by
  ext x
  change (algebraMap N P (algebraMap M N x) ∈ D.val) ↔ (algebraMap M P x ∈ D.val)
  rw [← IsScalarTower.algebraMap_apply M N P]

/-- The finite-layer indices themselves agree under iterated original pullback. -/
theorem finiteLayerPullbackLayer_tower (D : FiniteLayer K P) :
    finiteLayerPullbackLayer K M (finiteLayerPullbackLayer K N D) =
      finiteLayerPullbackLayer K M D :=
  Subtype.ext (finiteLayerPullback_tower K M N D)

/-- Both routes around the actual original inclusion square agree on each
original element; equality of pullbacks only changes its membership proof. -/
theorem finiteLayerPullbackTo_tower (D : FiniteLayer K P)
    (a : finiteLayerPullback K M (finiteLayerPullbackLayer K N D)) :
    finiteLayerPullbackTo K N D
        (finiteLayerPullbackTo K M (finiteLayerPullbackLayer K N D) a) =
      finiteLayerPullbackTo K M D
        (IntermediateField.equivOfEq (finiteLayerPullback_tower K M N D) a) := by
  apply Subtype.ext
  change algebraMap N P (algebraMap M N (a : M)) =
    algebraMap M P ((IntermediateField.equivOfEq (finiteLayerPullback_tower K M N D) a) : M)
  exact (IsScalarTower.algebraMap_apply M N P (a : M)).symm

/-- Simultaneous intrinsic good stages are cofinal in the original finite
fields of a finite separable tower. All three goodness statements are
constructed from the actual simultaneous tensor descent. -/
theorem exists_goodFiniteLayer_tower_ge
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P] (E : FiniteLayer K P) :
    ∃ D : FiniteLayer K P, E ≤ D ∧ IsGoodFiniteLayer K N D ∧
      IsGoodFiniteLayer K M D ∧
      IsGoodFiniteLayer K M (finiteLayerPullbackLayer K N D) := by
  obtain ⟨C, D, hDf, hE, _hD, hDi, hBf, _hB, hBi, ⟨eMP, heMP⟩,
    ⟨eMN, heMN⟩, ⟨eNP, heNP⟩⟩ :=
    exists_finiteLayer_tensor_descent_tower K (M := M) (N := N) E
  let B := finiteDescentIntersection (N := N) D
  let D₀ : FiniteLayer K P := ⟨D.restrictScalars K, hDf⟩
  let B₀ : FiniteLayer K N := ⟨B.restrictScalars K, hBf⟩
  have hC : finiteLayerPullback K M D₀ = C.val :=
    finiteLayerPullback_eq_of_inf K M C.val D hDf hDi
  have hBC : finiteLayerPullback K M B₀ = C.val :=
    finiteLayerPullback_eq_of_inf K M C.val B hBf hBi
  have hBD : finiteLayerPullback K N D₀ = B₀.val := by
    ext x
    rfl
  have hB₀ : finiteLayerPullbackLayer K N D₀ = B₀ := Subtype.ext hBD
  let : Algebra C.val D₀.val := D.algebra
  let : Algebra C.val B₀.val := B.algebra
  have hgoodM : IsGoodFiniteLayer K M D₀ :=
    isGoodFiniteLayer_of_original_tensor K M D₀ C.val hC (fun _ => rfl) eMP heMP
  have hgoodB : IsGoodFiniteLayer K M B₀ :=
    isGoodFiniteLayer_of_original_tensor K M B₀ C.val hBC (fun _ => rfl) eMN heMN
  let : Algebra B₀.val D₀.val := finiteDescentIntersectionAlgebra (N := N) D
  have hgoodN : IsGoodFiniteLayer K N D₀ :=
    isGoodFiniteLayer_of_original_tensor K N D₀ B₀.val hBD (fun _ => rfl) eNP heNP
  exact ⟨D₀, hE, hgoodN, hgoodM, hB₀.symm ▸ hgoodB⟩

/-- Any two original finite fields admit a common upper simultaneous good stage. -/
theorem exists_goodFiniteLayer_tower_ge_pair
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P] (E E' : FiniteLayer K P) :
    ∃ D : FiniteLayer K P, E ≤ D ∧ E' ≤ D ∧ IsGoodFiniteLayer K N D ∧
      IsGoodFiniteLayer K M D ∧
      IsGoodFiniteLayer K M (finiteLayerPullbackLayer K N D) := by
  obtain ⟨D, h, hN, hM, hMN⟩ :=
    exists_goodFiniteLayer_tower_ge K M N (FiniteLayer.sup E E')
  exact ⟨D, (FiniteLayer.le_sup_left E E').trans h,
    (FiniteLayer.le_sup_right E E').trans h, hN, hM, hMN⟩

end FontaineWintenberger
