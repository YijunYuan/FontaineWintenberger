/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Generator
public import FontaineWintenberger.Ramification.Lower.Index
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Tate's divisibility argument and cosets

## Tate's polynomial divisibility argument

Integral generators turn coefficient displacements into divisibility. Monic
minimal-polynomial division supplies the reverse divisibility needed for the
coset average, before specializing the polynomial to a product of conjugates.

## Conjugates of an integral Galois generator

The invariant orbit polynomial descends to the fixed ring. Its degree
agrees with the degree of the monic minimal polynomial by the integral power
basis and the Galois degree theorem, so no factorization certificate is assumed.

## Tate's scaled identity on integral rings

The twisted minimal polynomial is proved to be the product over subgroup
conjugates. Its valuation sum is compared with the intrinsic order using the
proved generator formula and canonical ramification-index scaling.
-/

@[expose] public section

namespace FontaineWintenberger

open Polynomial

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The displacement of a generator divides every displacement. -/
theorem generator_sub_dvd_aut_sub (τ : A ≃ₐ[R] A) {y : A}
    (hy : Algebra.adjoin R {y} = ⊤) (c : A) : τ y - y ∣ τ c - c := by
  apply Ideal.mem_span_singleton.mp
  have hτ : τ ∈ (Ideal.span {τ y - y}).inertia (A ≃ₐ[R] A) :=
    (mem_inertia_iff_generator (A ≃ₐ[R] A) hy (Ideal.span {τ y - y}) τ).mpr
      (Ideal.subset_span (by simp))
  exact (Ideal.mem_inertia.mp hτ) c

omit [Algebra R B] [IsScalarTower R A B] in
/-- Coefficient displacements give one divisibility in Tate's argument. -/
theorem generator_sub_dvd_aeval_map (τ : A ≃ₐ[R] A) {y : A}
    (hy : Algebra.adjoin R {y} = ⊤) (x : B) (f : A[X]) (hf : aeval x f = 0) :
    algebraMap A B (τ y - y) ∣ aeval x (f.map τ.toRingHom) := by
  have hd : C (algebraMap A B (τ y - y)) ∣
      ((f.map τ.toRingHom - f).map (algebraMap A B)) := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    simp only [coeff_map, coeff_sub]
    exact _root_.map_dvd (algebraMap A B) (generator_sub_dvd_aut_sub τ hy (f.coeff n))
  have he := Polynomial.eval_dvd (x := x) hd
  simpa only [eval_C, eval_map, Polynomial.eval₂_sub, ← aeval_def, hf, sub_zero] using he

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [Module.IsTorsionFree A B]

/-- Monic minimal-polynomial division gives the reverse divisibility in Tate's argument. -/
theorem aeval_map_minpoly_dvd_generator_sub (τ : A ≃ₐ[R] A) {x : B}
    (hx : Algebra.adjoin R {x} = ⊤) (hint : IsIntegral A x) (y : A) :
    aeval x ((minpoly A x).map τ.toRingHom) ∣ algebraMap A B (τ y - y) := by
  have hsurj := hx
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hsurj
  obtain ⟨g, hg⟩ := hsurj (algebraMap A B y)
  have hz : aeval x (g.map (algebraMap R A) - C y) = 0 := by
    rw [map_sub, aeval_map_algebraMap, aeval_C, hg, sub_self]
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hz
  have hfix : (g.map (algebraMap R A)).map τ.toRingHom = g.map (algebraMap R A) := by
    rw [map_map]
    congr 1
    ext r
    exact τ.commutes r
  have h := congrArg (fun p : A[X] => aeval x (p.map τ.toRingHom)) hq
  rw [Polynomial.map_sub, Polynomial.map_C, hfix, map_sub, aeval_map_algebraMap,
    aeval_C, hg, Polynomial.map_mul, map_mul] at h
  have hd : aeval x ((minpoly A x).map τ.toRingHom) ∣
      algebraMap A B y - algebraMap A B (τ y) := ⟨_, h⟩
  have hd' := dvd_neg.mpr hd
  simpa only [neg_sub, map_sub] using hd'

/-- Tate's two integral displacements are associated, including when both vanish. -/
theorem associated_generator_sub_aeval_map_minpoly (τ : A ≃ₐ[R] A) {x : B} {y : A}
    (hx : Algebra.adjoin R {x} = ⊤) (hy : Algebra.adjoin R {y} = ⊤)
    (hint : IsIntegral A x) :
    Associated (algebraMap A B (τ y - y))
      (aeval x ((minpoly A x).map τ.toRingHom)) := by
  exact associated_of_dvd_dvd
    (generator_sub_dvd_aeval_map τ hy x (minpoly A x) (minpoly.aeval A x))
    (aeval_map_minpoly_dvd_generator_sub τ hx hint y)

/-- The two Tate displacements have equal normalized valuation, also at zero. -/
theorem addVal_generator_sub_eq_aeval_map_minpoly [IsDiscreteValuationRing B]
    (τ : A ≃ₐ[R] A) {x : B} {y : A}
    (hx : Algebra.adjoin R {x} = ⊤) (hy : Algebra.adjoin R {y} = ⊤)
    (hint : IsIntegral A x) :
    IsDiscreteValuationRing.addVal B (algebraMap A B (τ y - y)) =
      IsDiscreteValuationRing.addVal B (aeval x ((minpoly A x).map τ.toRingHom)) := by
  have h := associated_generator_sub_aeval_map_minpoly τ hx hy hint
  exact le_antisymm (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h.dvd)
    (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h.symm.dvd)

end FontaineWintenberger

namespace FontaineWintenberger

open Polynomial

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
variable (H : Type*) [Group H] [Fintype H] [MulSemiringAction H B] [IsGaloisGroup H A B]

/-- The ring minimal polynomial of a Galois generator is its conjugate product. -/
theorem map_minpoly_eq_prod_conjugates {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    (minpoly A x).map (algebraMap A B) = ∏ h : H, (X - C (h • x)) := by
  classical
  obtain ⟨p, hp, hdeg, hmon⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B H x) (MulSemiringAction.monic_charpoly H x)
  have hp0 : aeval x p = 0 := by
    change p.eval₂ (algebraMap A B) x = 0
    rw [← eval_map, hp, MulSemiringAction.eval_charpoly]
  have hint : IsIntegral A x := ⟨p, hmon, hp0⟩
  let pb := PowerBasis.ofAdjoinEqTop' hint hx
  have hd : (minpoly A x).natDegree = Fintype.card H := by
    rw [← PowerBasis.ofAdjoinEqTop'_dim hint hx, ← pb.finrank,
      ← IsGaloisGroup.card_eq_finrank' H A B, Nat.card_eq_fintype_card]
  have hchar : (MulSemiringAction.charpoly H x).natDegree = Fintype.card H := by
    rw [MulSemiringAction.charpoly,
      natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C (h • x))]
    simp
  have heq : p = minpoly A x := eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hint) hmon (minpoly.isIntegrallyClosed_dvd hint hp0)
    (by rw [hdeg, hchar, hd])
  rw [← heq, hp, MulSemiringAction.charpoly]

end FontaineWintenberger

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

/-- Compatibility with a lifted automorphism twists the conjugate product. -/
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

/-- The twisted minimal-polynomial value is the product of the coset displacements. -/
theorem aeval_map_minpoly_eq_prod_displacements (τ : A ≃ₐ[R] A) (σ : B ≃ₐ[R] B)
    (hστ : ∀ a : A, algebraMap A B (τ a) = σ (algebraMap A B a))
    {x : B} (hx : Algebra.adjoin R {x} = ⊤) :
    aeval x ((minpoly A x).map τ.toRingHom) = ∏ h : H, (x - σ (h • x)) := by
  change ((minpoly A x).map τ.toRingHom).eval₂ (algebraMap A B) x = _
  rw [← eval_map, map_minpoly_eq_prod_twisted H τ σ hστ hx]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

/-- Multiplicativity turns the twisted product into the sum of displacement values. -/
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

/-- Tate's scaled average of intrinsic orders, with the canonical ramification index. -/
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
