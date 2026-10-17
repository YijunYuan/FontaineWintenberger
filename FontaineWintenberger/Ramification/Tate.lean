/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Generator
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Tate's polynomial divisibility argument

Integral generators turn coefficient displacements into divisibility. Monic
minimal-polynomial division supplies the reverse divisibility needed for the
coset average, before specializing the polynomial to a product of conjugates.
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
