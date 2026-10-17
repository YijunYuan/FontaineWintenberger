/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Conjugates
public import FontaineWintenberger.Ramification.Index

/-!
# Tate's scaled identity on actual integral rings

The twisted minimal polynomial is proved to be the product over subgroup
conjugates. Its valuation sum is compared with the intrinsic order using the
proved generator formula and canonical ramification-index scaling.
-/

@[expose] public section

namespace FontaineWintenberger

open Polynomial

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- A generator over the smaller base also generates over an intermediate algebra. -/
theorem adjoin_singleton_eq_top_over_intermediate {x : B}
    (hx : Algebra.adjoin R {x} = ⊤) : Algebra.adjoin A {x} = ⊤ := by
  have hle : Algebra.adjoin R {x} ≤ (Algebra.adjoin A {x}).restrictScalars R :=
    Algebra.adjoin_le (fun _ h => Algebra.subset_adjoin h)
  apply top_unique
  intro z _
  apply hle
  rw [hx]
  trivial

section Twisting

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [FaithfulSMul A B]
variable (H : Type*) [Group H] [Fintype H] [MulSemiringAction H B] [IsGaloisGroup H A B]

/-- Compatibility with a lifted automorphism twists the actual conjugate product. -/
theorem map_minpoly_eq_prod_twisted (τ : A ≃ₐ[R] A) (σ : B ≃ₐ[R] B)
    (hστ : ∀ a : A, algebraMap A B (τ a) = σ (algebraMap A B a))
    {x : B} (hx : Algebra.adjoin R {x} = ⊤) :
    ((minpoly A x).map τ.toRingHom).map (algebraMap A B) =
      ∏ h : H, (X - C (σ (h • x))) := by
  have hc : (algebraMap A B).comp τ.toRingHom = σ.toRingHom.comp (algebraMap A B) := by
    ext a
    exact hστ a
  rw [map_map, hc, ← map_map,
    map_minpoly_eq_prod_conjugates H (adjoin_singleton_eq_top_over_intermediate hx)]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- The actual twisted minimal-polynomial value is the product of the coset displacements. -/
theorem aeval_map_minpoly_eq_prod_displacements (τ : A ≃ₐ[R] A) (σ : B ≃ₐ[R] B)
    (hστ : ∀ a : A, algebraMap A B (τ a) = σ (algebraMap A B a))
    {x : B} (hx : Algebra.adjoin R {x} = ⊤) :
    aeval x ((minpoly A x).map τ.toRingHom) = ∏ h : H, (x - σ (h • x)) := by
  change ((minpoly A x).map τ.toRingHom).eval₂ (algebraMap A B) x = _
  rw [← eval_map, map_minpoly_eq_prod_twisted H τ σ hστ hx]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

/-- Multiplicativity turns the actual twisted product into the sum of displacement values. -/
theorem addVal_aeval_map_minpoly_eq_sum [IsDiscreteValuationRing B]
    (τ : A ≃ₐ[R] A) (σ : B ≃ₐ[R] B)
    (hστ : ∀ a : A, algebraMap A B (τ a) = σ (algebraMap A B a))
    {x : B} (hx : Algebra.adjoin R {x} = ⊤) :
    IsDiscreteValuationRing.addVal B (aeval x ((minpoly A x).map τ.toRingHom)) =
      ∑ h : H, IsDiscreteValuationRing.addVal B (σ (h • x) - x) := by
  rw [aeval_map_minpoly_eq_prod_displacements H τ σ hστ hx]
  calc
    _ = ∑ h : H, IsDiscreteValuationRing.addVal B (x - σ (h • x)) :=
      map_prod (IsDiscreteValuationRing.addVal B).toMonoidHom _ _
    _ = _ := Finset.sum_congr rfl fun h _ => by
      rw [← neg_sub (σ (h • x)) x, AddValuation.map_neg]

end Twisting

section ScaledOrder

variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
    [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
variable (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]
variable (H : Subgroup G) [Fintype H] [IsGaloisGroup H A B]

/-- Tate's scaled average of intrinsic orders, with the actual canonical ramification index. -/
theorem ramificationIdx_mul_order_eq_sum_coset (τ : A ≃ₐ[R] A) (σ : G)
    (hστ : ∀ a : A, algebraMap A B (τ a) = σ • algebraMap A B a)
    {x : B} {y : A} (hx : Algebra.adjoin R {x} = ⊤) (hy : Algebra.adjoin R {y} = ⊤) :
    ((IsLocalRing.maximalIdeal B).ramificationIdx A : ℕ∞) *
        ramificationOrder (R := A) (A ≃ₐ[R] A) τ =
      ∑ h : H, ramificationOrder (R := B) G (σ * h.1) := by
  have := Algebra.IsInvariant.isIntegral A B H
  have hint : IsIntegral A x := Algebra.IsIntegral.isIntegral x
  rw [ramificationOrder_eq_generator (A ≃ₐ[R] A) hy, ← addVal_algebraMap A B]
  change IsDiscreteValuationRing.addVal B (algebraMap A B (τ y - y)) = _
  rw [addVal_generator_sub_eq_aeval_map_minpoly τ hx hy hint,
    addVal_aeval_map_minpoly_eq_sum H τ (MulSemiringAction.toAlgAut G R B σ) hστ hx]
  apply Finset.sum_congr rfl
  intro h _
  change IsDiscreteValuationRing.addVal B (σ • (h.1 • x) - x) = _
  simpa only [mul_smul] using (ramificationOrder_eq_generator G hx (σ * h.1)).symm

end ScaledOrder

end FontaineWintenberger
