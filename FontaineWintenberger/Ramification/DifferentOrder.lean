module

public import FontaineWintenberger.Ramification.Different
public import FontaineWintenberger.Ramification.Conjugates
public import FontaineWintenberger.Ramification.Generator
public import Mathlib.RingTheory.Multiplicity

/-!
# The different and intrinsic ramification orders

Ideal multiplicity agrees with the normalized integral valuation on principal
ideals. The derivative formula for the actual conjugate polynomial then
computes the different as a product of actual displacements.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing Polynomial

/-- Canonical ideal multiplicity is the normalized integral valuation of an
actual principal generator, including zero. -/
theorem maximalIdeal_emultiplicity_span {B : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] (x : B) :
    emultiplicity (IsLocalRing.maximalIdeal B) (Ideal.span {x}) = addVal B x := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← pow_dvd_iff_le_emultiplicity, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem, mem_maximalIdeal_pow_iff_addVal]

section Conjugates

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- The actual minimal-polynomial derivative is the product of nonidentity
conjugate displacements of an actual integral generator. -/
theorem aeval_derivative_minpoly_eq_prod_displacements {θ : B}
    (hθ : Algebra.adjoin A {θ} = ⊤) :
    Polynomial.aeval θ (minpoly A θ).derivative =
      ∏ g ∈ Finset.univ.erase (1 : G), (θ - g • θ) := by
  classical
  let Q : Polynomial B := ∏ g ∈ Finset.univ.erase (1 : G), (X - C (g • θ))
  have hprod : (∏ g : G, (X - C (g • θ))) = (X - C θ) * Q := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : G)), one_smul]
  have h := congrArg (fun f : Polynomial B => f.derivative.eval θ)
    (map_minpoly_eq_prod_conjugates G hθ)
  rw [hprod] at h
  simpa [derivative_map, Q, eval_prod] using h

end Conjugates

section Different

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A B] [FaithfulSMul A B]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    [MulSemiringAction G B] [IsGaloisGroup G A B]

include K L in
/-- The actual different is the principal ideal of the product of nonidentity
conjugate displacements, with no chosen different or polynomial certificate. -/
theorem differentIdeal_eq_span_prod_displacements {θ : B}
    (hθ : Algebra.adjoin A {θ} = ⊤) :
    differentIdeal A B =
      Ideal.span {∏ g ∈ Finset.univ.erase (1 : G), (θ - g • θ)} := by
  rw [differentIdeal_eq_span_derivative_of_adjoin_eq_top A B K L hθ,
    aeval_derivative_minpoly_eq_prod_displacements G hθ]

include K L in
/-- The actual ideal order of the different is the sum of the intrinsic
nonidentity ramification orders. -/
theorem differentIdeal_order_eq_sum_ramificationOrder [SMulCommClass G A B] {θ : B}
    (hθ : Algebra.adjoin A {θ} = ⊤) :
    emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) =
      ∑ g ∈ Finset.univ.erase (1 : G), ramificationOrder (R := B) G g := by
  rw [differentIdeal_eq_span_prod_displacements A B K L G hθ, maximalIdeal_emultiplicity_span]
  have hprod (s : Finset G) :
      addVal B (∏ g ∈ s, (θ - g • θ)) = ∑ g ∈ s, addVal B (θ - g • θ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert g s hg ih => simp only [Finset.prod_insert hg, Finset.sum_insert hg, addVal_mul, ih]
  rw [hprod]
  apply Finset.sum_congr rfl
  intro g _
  rw [ramificationOrder_eq_generator G hθ, ← neg_sub (g • θ) θ, AddValuation.map_neg]

end Different

end FontaineWintenberger
