/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Tate
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Conjugates of an integral Galois generator

The invariant orbit polynomial descends to the actual fixed ring. Its degree
agrees with the degree of the monic minimal polynomial by the integral power
basis and the Galois degree theorem, so no factorization certificate is assumed.
-/

@[expose] public section

namespace FontaineWintenberger

open Polynomial

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
variable (H : Type*) [Group H] [Fintype H] [MulSemiringAction H B] [IsGaloisGroup H A B]

/-- The actual ring minimal polynomial of a Galois generator is its conjugate product. -/
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
