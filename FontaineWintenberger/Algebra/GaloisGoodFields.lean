/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteNormPairs
public import FontaineWintenberger.Algebra.StableFiniteLayers
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Original good finite fields for finite Galois extensions

Actual finite image composita give cofinal stable fields. Their original
relative automorphisms and fixed fields determine the canonical tensor map.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped TensorProduct

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- Restriction of the original relative Galois group to an actual stable
finite field, over its original pullback to the source. -/
def galoisFiniteLayerRestrict (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    (N ≃ₐ[M] N) →* (D.val ≃ₐ[finiteLayerPullback K M D] D.val) where
  toFun σ := by
    let e : D.val ≃ₐ[K] D.val :=
      (IntermediateField.equivMap D.val (σ.restrictScalars K).toAlgHom).trans
        (IntermediateField.equivOfEq (hD σ))
    exact { e.toRingEquiv with
      commutes' := fun c => Subtype.ext (σ.commutes (c : M)) }
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

@[simp]
theorem coe_galoisFiniteLayerRestrict (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (σ : N ≃ₐ[M] N) (x : D.val) :
    (galoisFiniteLayerRestrict K M N D hD σ x : N) = σ (x : N) := rfl

variable [Module.Finite M N] [IsGalois M N]

/-- The fixed field of the actual restriction range is exactly the original
pullback, represented as the bottom field over that very pullback. -/
theorem galoisFiniteLayerRestrict_fixedField (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    IntermediateField.fixedField (galoisFiniteLayerRestrict K M N D hD).range = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hfix : ∀ σ : N ≃ₐ[M] N, σ (x : N) = (x : N) := by
    intro σ
    exact congrArg (fun a : D.val => (a : N))
      ((IntermediateField.mem_fixedField_iff
        (H := (galoisFiniteLayerRestrict K M N D hD).range) x).mp hx _ ⟨σ, rfl⟩)
  obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := M) (x : N)).mpr hfix
  have hmD : algebraMap M N m ∈ D.val := hm.symm ▸ x.property
  rw [IntermediateField.mem_bot]
  refine ⟨⟨m, hmD⟩, ?_⟩
  exact Subtype.ext hm

omit [Module.Finite M N] in
/-- A genuine original primitive element makes the restriction faithful. -/
theorem galoisFiniteLayerRestrict_injective (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin M {α} = ⊤) (hαD : α ∈ D.val) :
    Function.Injective (galoisFiniteLayerRestrict K M N D hD) := by
  have hA : Algebra.adjoin M ({α} : Set N) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hα]
    rfl
  intro σ τ hστ
  have he : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hA
    intro z hz
    have hz' : z = α := Set.mem_singleton_iff.mp hz
    subst z
    exact congrArg (fun s : D.val ≃ₐ[finiteLayerPullback K M D] D.val =>
      (s ⟨α, hαD⟩ : N)) hστ
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun he x)

/-- Finite Artin theory computes the actual degree over the original pullback. -/
theorem finrank_galois_stableFiniteLayer (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin M {α} = ⊤) (hαD : α ∈ D.val) :
    Module.finrank (finiteLayerPullback K M D) D.val = Module.finrank M N := by
  have hf := IntermediateField.finrank_fixedField_eq_card
    (H := (galoisFiniteLayerRestrict K M N D hD).range)
  rw [galoisFiniteLayerRestrict_fixedField, IntermediateField.finrank_bot'] at hf
  exact hf.trans ((Nat.card_congr (MonoidHom.ofInjective
    (galoisFiniteLayerRestrict_injective K M N D hD α hα hαD)).toEquiv).symm.trans
      (IsGalois.card_aut_eq_finrank M N))

/-- Stability and a genuine primitive element prove goodness of the canonical
original tensor map, rather than assuming a descent presentation. -/
theorem isGoodFiniteLayer_of_galois_stable (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin M {α} = ⊤) (hαD : α ∈ D.val) :
    IsGoodFiniteLayer K M D := by
  let C := finiteLayerPullback K M D
  let f := finiteLayerTensorMap K M D
  have hA : Algebra.adjoin M ({α} : Set N) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hα]
    rfl
  have hrange : Algebra.adjoin M ({α} : Set N) ≤ f.range := by
    apply Algebra.adjoin_le_iff.mpr
    intro z hz
    have hz' : z = α := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨1 ⊗ₜ[C] (⟨α, hαD⟩ : D.val), ?_⟩
    change (1 : M) • α = α
    exact one_smul M α
  have hsurj : Function.Surjective f := by
    intro x
    exact hrange (hA ▸ Algebra.mem_top)
  have hdim : Module.finrank M (M ⊗[C] D.val) = Module.finrank M N := by
    rw [Module.finrank_baseChange]
    exact finrank_galois_stableFiniteLayer K M N D hD α hα hαD
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

variable [Algebra.IsAlgebraic K N]

/-- Actual finite image composita containing a genuine primitive element
give cofinal original Galois-stable good fields, without normality over K. -/
theorem exists_galois_stable_goodFiniteLayer_ge (E : FiniteLayer K N) :
    ∃ D : FiniteLayer K N, E ≤ D ∧ IsGoodFiniteLayer K M D ∧
      (∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧
      ∃ α : N, α ∈ D.val ∧ IntermediateField.adjoin M {α} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element M N
  let A : FiniteLayer K N := ⟨IntermediateField.adjoin K {α}, inferInstance⟩
  let D₀ := FiniteLayer.sup E A
  let D : FiniteLayer K N := ⟨IntermediateField.normalClosure K D₀.val N, inferInstance⟩
  have hD₀D : D₀ ≤ D := IntermediateField.le_normalClosure D₀.val
  have hαA : α ∈ A.val := IntermediateField.subset_adjoin K {α} (by simp)
  have hαD : α ∈ D.val := hD₀D (FiniteLayer.le_sup_right E A hαA)
  have hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val :=
    fun σ => IntermediateField.map_normalClosure_eq D₀.val (σ.restrictScalars K)
  exact ⟨D, (FiniteLayer.le_sup_left E A).trans hD₀D,
    isGoodFiniteLayer_of_galois_stable K M N D hD α hα hαD, hD, α, hαD, hα⟩

/-- Two original finite fields have a common actual stable good upper field. -/
theorem exists_galois_stable_goodFiniteLayer_ge_pair (E F : FiniteLayer K N) :
    ∃ D : FiniteLayer K N, E ≤ D ∧ F ≤ D ∧ IsGoodFiniteLayer K M D ∧
      ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val := by
  obtain ⟨D, hD, hg, hs, _⟩ := exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteLayer.sup E F)
  exact ⟨D, (FiniteLayer.le_sup_left E F).trans hD,
    (FiniteLayer.le_sup_right E F).trans hD, hg, hs⟩

end FontaineWintenberger
