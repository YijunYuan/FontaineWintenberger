module

public import FontaineWintenberger.Algebra.PolynomialDiscriminant
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# The integer polynomial giving every monic discriminant

The existing free monic polynomial has an actual discriminant over the
integer coefficient ring. Its universal coefficient evaluation gives the
original discriminant over every commutative ring.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

/-- The actual integer polynomial in the nonleading coefficients which
gives the discriminant of a monic polynomial of degree `n`. -/
def monicDiscriminantPolynomial (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  (freeMonic ℤ n).discr

/-- Evaluating the universal integer polynomial at the original coefficients
gives exactly the existing polynomial discriminant, over every commutative ring. -/
theorem monicDiscriminantPolynomial_eval {R : Type*} [CommRing R]
    (f : R[X]) (hf : f.Monic) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun i : Fin f.natDegree => f.coeff i)
      (monicDiscriminantPolynomial f.natDegree) = f.discr := by
  let P : MonicDegreeEq R f.natDegree :=
    ⟨f, by simpa only [coeff_natDegree] using hf.leadingCoeff,
      fun i hi => coeff_eq_zero_of_natDegree_lt hi⟩
  have hmap := congrArg Subtype.val ((MvPolynomial.mapEquivMonic ℤ R f.natDegree).apply_symm_apply P)
  change (freeMonic ℤ f.natDegree).map
    (MvPolynomial.aeval (fun i : Fin f.natDegree => f.coeff i)).toRingHom = f at hmap
  change (MvPolynomial.aeval (fun i : Fin f.natDegree => f.coeff i))
    (monicDiscriminantPolynomial f.natDegree) = f.discr
  have hd := monic_discr_map (freeMonic ℤ f.natDegree) (monic_freeMonic ℤ f.natDegree)
    (MvPolynomial.aeval (fun i : Fin f.natDegree => f.coeff i)).toRingHom
  rw [hmap] at hd
  exact hd.symm

end FontaineWintenberger
