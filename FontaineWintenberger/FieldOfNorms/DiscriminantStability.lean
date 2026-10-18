/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.HighBreakCoordinates
public import FontaineWintenberger.Algebra.PolynomialDiscriminant

/-!
# Discriminants of the original finite-coordinate polynomials

The actual integral coordinates need not be additive. Their polynomial is
formed coefficient by coefficient; only its reduction is compared using the
proved high-break ring homomorphism. The original normalized discriminant
value is then stable as soon as the precision exceeds that value.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring (FieldOfNorms.fieldValuation K L)

/-- Actual integral coordinate evaluation preserves zero. -/
@[simp]
theorem FieldOfNorms.integralCoordinateAt_zero (E : FiniteIntermediateField K L) :
    FieldOfNorms.integralCoordinateAt K L E 0 = 0 := by
  exact Subtype.ext (_root_.map_zero (FieldOfNorms.coord K L E))

/-- Actual integral coordinate evaluation preserves one. -/
@[simp]
theorem FieldOfNorms.integralCoordinateAt_one (E : FiniteIntermediateField K L) :
    FieldOfNorms.integralCoordinateAt K L E 1 = 1 := by
  exact Subtype.ext (_root_.map_one (FieldOfNorms.coord K L E))

/-- The polynomial of actual original coordinates, formed by its finite
coefficient expansion. No additive coordinate homomorphism is presumed. -/
def FieldOfNorms.coordinatePolynomial (E : FiniteIntermediateField K L) :
    Oₓ[X] → (spectralIntegerRing K E.val)[X] := by
  intro f
  exact ∑ i ∈ f.support,
    monomial i (FieldOfNorms.integralCoordinateAt K L E (f.coeff i))

/-- Every coefficient is the original finite coordinate of that same
coefficient of the original polynomial. -/
@[simp]
theorem coeff_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ (f : Oₓ[X]) (i : ℕ),
      (FieldOfNorms.coordinatePolynomial K L E f).coeff i =
        FieldOfNorms.integralCoordinateAt K L E (f.coeff i) := by
  classical
  intro f i
  by_cases hi : f.coeff i = 0
  · simp [FieldOfNorms.coordinatePolynomial, coeff_monomial, mem_support_iff, hi]
  · simp [FieldOfNorms.coordinatePolynomial, coeff_monomial, mem_support_iff, hi]

/-- The original coordinate polynomial has exactly the original monic degree. -/
theorem natDegree_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      (FieldOfNorms.coordinatePolynomial K L E f).natDegree = f.natDegree := by
  intro f hf
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_fieldOfNormsCoordinatePolynomial, coeff_eq_zero_of_natDegree_lt hi,
      FieldOfNorms.integralCoordinateAt_zero]
  · rw [coeff_fieldOfNormsCoordinatePolynomial, hf.coeff_natDegree,
      FieldOfNorms.integralCoordinateAt_one]
    exact one_ne_zero

/-- The same actual coordinate polynomial is monic in the original integers. -/
theorem monic_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      (FieldOfNorms.coordinatePolynomial K L E f).Monic := by
  intro f hf
  change (FieldOfNorms.coordinatePolynomial K L E f).coeff
    (FieldOfNorms.coordinatePolynomial K L E f).natDegree = 1
  rw [natDegree_fieldOfNormsCoordinatePolynomial K L E f hf,
    coeff_fieldOfNormsCoordinatePolynomial, hf.coeff_natDegree,
        FieldOfNorms.integralCoordinateAt_one]

/-- Passing the actual integral coefficient polynomial into its actual finite
field preserves monicity. -/
theorem monic_map_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Monic := by
  intro f hf
  exact (monic_fieldOfNormsCoordinatePolynomial K L E f hf).map _

/-- The actual finite-field polynomial also has precisely the original degree. -/
theorem natDegree_map_fieldOfNormsCoordinatePolynomial (E : FiniteIntermediateField K L) :
    ∀ f : Oₓ[X], f.Monic →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).natDegree = f.natDegree := by
  intro f hf
  rw [(monic_fieldOfNormsCoordinatePolynomial K L E f hf).natDegree_map,
    natDegree_fieldOfNormsCoordinatePolynomial K L E f hf]

variable (E : FiniteIntermediateField K L) {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)

/-- Reduction of the actual coefficient polynomial agrees with mapping the
original polynomial by the actual high-break quotient ring homomorphism. -/
theorem map_fieldOfNormsCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X],
      (FieldOfNorms.coordinatePolynomial K L E f).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)) =
          f.map (FieldOfNorms.highBreakProjection K L hb h r hrb) := by
  intro f
  ext i
  simp only [coeff_map, coeff_fieldOfNormsCoordinatePolynomial,
      FieldOfNorms.highBreakProjection_apply]

/-- The existing discriminant commutes with the original-coordinate reduction;
the unreduced coordinate evaluation is never used as a ring homomorphism. -/
theorem FieldOfNorms.highBreakProjection_discr
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X], f.Monic →
      FieldOfNorms.highBreakProjection K L hb h r hrb f.discr =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)
          (FieldOfNorms.coordinatePolynomial K L E f).discr := by
  intro f hf
  have hd := congrArg Polynomial.discr
    (map_fieldOfNormsCoordinatePolynomial K L E hb h r hrb f)
  rw [monic_discr_map _ (monic_fieldOfNormsCoordinatePolynomial K L E f hf),
    monic_discr_map f hf] at hd
  exact hd.symm

include hb h in
/-- The actual coordinate of the original discriminant and the discriminant
of the actual coordinate polynomial differ by the proved ideal precision. -/
theorem FieldOfNorms.coordinatePolynomial_discr_sub_mem
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ f : Oₓ[X], f.Monic →
      FieldOfNorms.integralCoordinateAt K L E f.discr -
        (FieldOfNorms.coordinatePolynomial K L E f).discr ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  intro f hf
  apply Ideal.Quotient.eq.mp
  rw [← FieldOfNorms.highBreakProjection_apply]
  exact FieldOfNorms.highBreakProjection_discr K L E hb h r hrb f hf

include hb h in
/-- Above the actual discriminant precision, the original finite-coordinate
discriminant has exactly the original stable normalized valuation. -/
theorem FieldOfNorms.coordinatePolynomial_discr_valuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) =
        FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) := by
  intro f hf hr
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  let x := FieldOfNorms.integralCoordinateAt K L E f.discr
  let y := (FieldOfNorms.coordinatePolynomial K L E f).discr
  have hc : v (x : E.val) = FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) :=
    (FieldOfNorms.valuation_eq_coordinate_of_fullUpper K L hb h
      (f.discr : FieldOfNorms K L)).symm
  have hm : y - x ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
    simpa only [neg_sub] using (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r).neg_mem
      (FieldOfNorms.coordinatePolynomial_discr_sub_mem K L E hb h r hrb f hf)
  have hv := (ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) (y - x) r).mp hm
  change v ((y : E.val) - (x : E.val)) ≤ WithZero.exp (-(r : ℤ)) at hv
  exact (v.map_eq_of_sub_lt (hv.trans_lt (hr.trans_eq hc.symm))).trans hc

include hb h in
/-- The equality is also literally equality of the associated normalized
additive valuations on the two original fields. -/
theorem FieldOfNorms.coordinatePolynomial_discr_additiveValuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      (Valuation.toAddValuation
        ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val))
          ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) =
        (Valuation.toAddValuation (FieldOfNorms.fieldValuation K L))
          (f.discr : FieldOfNorms K L) := by
  intro f hf hr
  exact congrArg (fun z ↦ OrderDual.toDual (Additive.ofMul z))
    (FieldOfNorms.coordinatePolynomial_discr_valuation K L E hb h r hrb f hf hr)

include hb h in
/-- At the same proved precision the actual finite-field coordinate polynomial
is separable, because its original discriminant has nonzero valuation. -/
theorem separable_fieldOfNormsCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) →
      ((FieldOfNorms.coordinatePolynomial K L E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Separable := by
  intro f hf hr
  have hfE := monic_fieldOfNormsCoordinatePolynomial K L E f hf
  apply (monic_discr_ne_zero_iff _ (hfE.map
    (algebraMap (spectralIntegerRing K E.val) E.val))).mp
  rw [monic_discr_map _ hfE]
  intro hz
  change ((FieldOfNorms.coordinatePolynomial K L E f).discr : E.val) = 0 at hz
  have hv := FieldOfNorms.coordinatePolynomial_discr_valuation K L E hb h r hrb f hf hr
  rw [hz, map_zero] at hv
  exact (not_lt_of_ge zero_le) (hr.trans_eq hv.symm)

/-- Actual separability supplies a finite precision strictly beyond the
original nonzero discriminant value. -/
theorem exists_fieldOfNorms_discr_precision :
    ∀ (f : Oₓ[X]), f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
      ∃ r : ℕ, WithZero.exp (-(r : ℤ)) <
        FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) := by
  intro f hf hsep
  have hd := (monic_discr_ne_zero_iff _ (hf.map (algebraMap Oₓ (FieldOfNorms K L)))).mpr hsep
  rw [monic_discr_map f hf] at hd
  change (f.discr : FieldOfNorms K L) ≠ 0 at hd
  let w := FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L)
  have hw : w ≠ 0 := fun hz ↦ hd ((FieldOfNorms.valuation_eq_zero_iff K L _).mp hz)
  let r := (-WithZero.log w).toNat + 1
  refine ⟨r, (WithZero.lt_log_iff_exp_lt hw).mp ?_⟩
  dsimp [r]
  omega

/-- Along every original finite-coordinate sequence with actual full products
at depths tending to infinity, the original discriminant value is eventually
constant and the actual coordinate polynomials are separable. -/
theorem eventually_fieldOfNormsCoordinatePolynomial_discr_stable
    (F : ℕ → FiniteIntermediateField K L) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hF : ∀ n, (F n).HasFullUpper K L (c n))
    (hctop : Filter.Tendsto c Filter.atTop Filter.atTop) :
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
      ∀ᶠ n in Filter.atTop,
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
            (F n).val ((FieldOfNorms.coordinatePolynomial K L (F n) f).discr : (F n).val)
                =
          FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) ∧
        ((FieldOfNorms.coordinatePolynomial K L (F n) f).map
          (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  intro f hf hsep
  obtain ⟨r, hr⟩ := exists_fieldOfNorms_discr_precision K L f hf hsep
  have hp : 0 < ((p - 1 : ℕ) : ℝ) / p := by
    have hp' := (Fact.out : Nat.Prime p).two_le
    have h₁ : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
    exact div_pos h₁ (by exact_mod_cast (Fact.out : Nat.Prime p).pos)
  have htop := Filter.Tendsto.const_mul_atTop hp hctop
  filter_upwards [htop.eventually (Filter.eventually_ge_atTop (r : ℝ))] with n hn
  have hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * c n⌉₊ := by
    exact_mod_cast hn.trans (Nat.le_ceil _)
  exact ⟨FieldOfNorms.coordinatePolynomial_discr_valuation K L (F n)
      (hc n) (hF n) r hrb f hf hr,
    separable_fieldOfNormsCoordinatePolynomial K L (F n)
      (hc n) (hF n) r hrb f hf hr⟩

/-- A genuine increasing cofinal sequence of original finite fields has full
upper depths tending to infinity and stabilizes every original monic separable
polynomial's discriminant, with actual eventual finite-field separability. -/
theorem exists_cofinal_fieldOfNormsCoordinatePolynomial_discr_stable :
    ∃ F : ℕ → FiniteIntermediateField K L, Monotone F ∧
      (∀ n, (F n).HasFullUpper K L ((n : ℝ) + 1)) ∧
      (∀ D : FiniteIntermediateField K L, ∃ n, D ≤ F n) ∧
      ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
        ∀ᶠ n in Filter.atTop,
          (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
              (F n).val ((FieldOfNorms.coordinatePolynomial K L (F n) f).discr : (F
                  n).val) =
            FieldOfNorms.valuation K L (f.discr : FieldOfNorms K L) ∧
          ((FieldOfNorms.coordinatePolynomial K L (F n) f).map
            (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  let c (n : ℕ) : ℝ := (n : ℝ) + 1
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  obtain ⟨F, hmono, hF, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_fullUpper_stages K L c (fun n ↦ (hc n).le)
  refine ⟨F, hmono, hF, hcofinal, ?_⟩
  apply eventually_fieldOfNormsCoordinatePolynomial_discr_stable K L F c hc hF
  exact Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
    tendsto_natCast_atTop_atTop

end FontaineWintenberger
