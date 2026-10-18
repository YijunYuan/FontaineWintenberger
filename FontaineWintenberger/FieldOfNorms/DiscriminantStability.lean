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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring (normLimitFieldValuation K L p)

/-- Actual integral coordinate evaluation preserves zero. -/
@[simp]
theorem normLimitIntegralCoordinateAt_zero (E : FiniteLayer K L) :
    letI := normLimitField K L p
    normLimitIntegralCoordinateAt K L p E 0 = 0 := by
  let := normLimitField K L p
  exact Subtype.ext (map_zero (normLimitEval K L E))

/-- Actual integral coordinate evaluation preserves one. -/
@[simp]
theorem normLimitIntegralCoordinateAt_one (E : FiniteLayer K L) :
    letI := normLimitField K L p
    normLimitIntegralCoordinateAt K L p E 1 = 1 := by
  let := normLimitField K L p
  exact Subtype.ext (map_one (normLimitEval K L E))

/-- The polynomial of actual original coordinates, formed by its finite
coefficient expansion. No additive coordinate homomorphism is presumed. -/
def normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    Oₓ[X] → (spectralIntegerRing K E.val)[X] := by
  letI := normLimitField K L p
  intro f
  exact ∑ i ∈ f.support,
    monomial i (normLimitIntegralCoordinateAt K L p E (f.coeff i))

/-- Every coefficient is the original finite coordinate of that same
coefficient of the original polynomial. -/
@[simp]
theorem coeff_normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    ∀ (f : Oₓ[X]) (i : ℕ),
      (normLimitCoordinatePolynomial K L p E f).coeff i =
        normLimitIntegralCoordinateAt K L p E (f.coeff i) := by
  let := normLimitField K L p
  classical
  intro f i
  by_cases hi : f.coeff i = 0
  · simp [normLimitCoordinatePolynomial, coeff_monomial, mem_support_iff, hi]
  · simp [normLimitCoordinatePolynomial, coeff_monomial, mem_support_iff, hi]

/-- The original coordinate polynomial has exactly the original monic degree. -/
theorem natDegree_normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      (normLimitCoordinatePolynomial K L p E f).natDegree = f.natDegree := by
  let := normLimitField K L p
  intro f hf
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_normLimitCoordinatePolynomial, coeff_eq_zero_of_natDegree_lt hi,
      normLimitIntegralCoordinateAt_zero]
  · rw [coeff_normLimitCoordinatePolynomial, hf.coeff_natDegree,
      normLimitIntegralCoordinateAt_one]
    exact one_ne_zero

/-- The same actual coordinate polynomial is monic in the original integers. -/
theorem monic_normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      (normLimitCoordinatePolynomial K L p E f).Monic := by
  let := normLimitField K L p
  intro f hf
  change (normLimitCoordinatePolynomial K L p E f).coeff
    (normLimitCoordinatePolynomial K L p E f).natDegree = 1
  rw [natDegree_normLimitCoordinatePolynomial K L p E f hf,
    coeff_normLimitCoordinatePolynomial, hf.coeff_natDegree, normLimitIntegralCoordinateAt_one]

/-- Passing the actual integral coefficient polynomial into its actual finite
field preserves monicity. -/
theorem monic_map_normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      ((normLimitCoordinatePolynomial K L p E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Monic := by
  let := normLimitField K L p
  intro f hf
  exact (monic_normLimitCoordinatePolynomial K L p E f hf).map _

/-- The actual finite-field polynomial also has precisely the original degree. -/
theorem natDegree_map_normLimitCoordinatePolynomial (E : FiniteLayer K L) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      ((normLimitCoordinatePolynomial K L p E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).natDegree = f.natDegree := by
  let := normLimitField K L p
  intro f hf
  rw [(monic_normLimitCoordinatePolynomial K L p E f hf).natDegree_map,
    natDegree_normLimitCoordinatePolynomial K L p E f hf]

variable (E : FiniteLayer K L) {b : ℝ} (hb : 0 < b) (h : E.HasFullUpper K L b)

/-- Reduction of the actual coefficient polynomial agrees with mapping the
original polynomial by the actual high-break quotient ring homomorphism. -/
theorem map_normLimitCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X],
      (normLimitCoordinatePolynomial K L p E f).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)) =
          f.map (normLimitHighBreakProjection K L p hb h r hrb) := by
  let := normLimitField K L p
  intro f
  ext i
  simp only [coeff_map, coeff_normLimitCoordinatePolynomial, normLimitHighBreakProjection_apply]

/-- The existing discriminant commutes with the original-coordinate reduction;
the unreduced coordinate evaluation is never used as a ring homomorphism. -/
theorem normLimitHighBreakProjection_discr
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      normLimitHighBreakProjection K L p hb h r hrb f.discr =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)
          (normLimitCoordinatePolynomial K L p E f).discr := by
  let := normLimitField K L p
  intro f hf
  have hd := congrArg Polynomial.discr
    (map_normLimitCoordinatePolynomial K L p E hb h r hrb f)
  rw [monic_discr_map _ (monic_normLimitCoordinatePolynomial K L p E f hf),
    monic_discr_map f hf] at hd
  exact hd.symm

include hb h in
/-- The actual coordinate of the original discriminant and the discriminant
of the actual coordinate polynomial differ by the proved ideal precision. -/
theorem normLimitCoordinatePolynomial_discr_sub_mem
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic →
      normLimitIntegralCoordinateAt K L p E f.discr -
        (normLimitCoordinatePolynomial K L p E f).discr ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let := normLimitField K L p
  intro f hf
  apply Ideal.Quotient.eq.mp
  rw [← normLimitHighBreakProjection_apply]
  exact normLimitHighBreakProjection_discr K L p E hb h r hrb f hf

include hb h in
/-- Above the actual discriminant precision, the original finite-coordinate
discriminant has exactly the original stable normalized valuation. -/
theorem normLimitCoordinatePolynomial_discr_valuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < normLimitValuation K L (f.discr : NormLimit K L) →
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          ((normLimitCoordinatePolynomial K L p E f).discr : E.val) =
        normLimitValuation K L (f.discr : NormLimit K L) := by
  let := normLimitField K L p
  intro f hf hr
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  let x := normLimitIntegralCoordinateAt K L p E f.discr
  let y := (normLimitCoordinatePolynomial K L p E f).discr
  have hc : v (x : E.val) = normLimitValuation K L (f.discr : NormLimit K L) :=
    (normLimitValuation_eq_coordinate_of_fullUpper K L hb h
      (f.discr : NormLimit K L)).symm
  have hm : y - x ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
    simpa only [neg_sub] using (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r).neg_mem
      (normLimitCoordinatePolynomial_discr_sub_mem K L p E hb h r hrb f hf)
  have hv := (ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) (y - x) r).mp hm
  change v ((y : E.val) - (x : E.val)) ≤ WithZero.exp (-(r : ℤ)) at hv
  exact (v.map_eq_of_sub_lt (hv.trans_lt (hr.trans_eq hc.symm))).trans hc

include hb h in
/-- The equality is also literally equality of the associated normalized
additive valuations on the two original fields. -/
theorem normLimitCoordinatePolynomial_discr_additiveValuation
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < normLimitValuation K L (f.discr : NormLimit K L) →
      (Valuation.toAddValuation
        ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val))
          ((normLimitCoordinatePolynomial K L p E f).discr : E.val) =
        (Valuation.toAddValuation (normLimitFieldValuation K L p))
          (f.discr : NormLimit K L) := by
  let := normLimitField K L p
  intro f hf hr
  exact congrArg (fun z ↦ OrderDual.toDual (Additive.ofMul z))
    (normLimitCoordinatePolynomial_discr_valuation K L p E hb h r hrb f hf hr)

include hb h in
/-- At the same proved precision the actual finite-field coordinate polynomial
is separable, because its original discriminant has nonzero valuation. -/
theorem separable_normLimitCoordinatePolynomial
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    ∀ (f : Oₓ[X]), f.Monic →
      WithZero.exp (-(r : ℤ)) < normLimitValuation K L (f.discr : NormLimit K L) →
      ((normLimitCoordinatePolynomial K L p E f).map
        (algebraMap (spectralIntegerRing K E.val) E.val)).Separable := by
  let := normLimitField K L p
  intro f hf hr
  have hfE := monic_normLimitCoordinatePolynomial K L p E f hf
  apply (monic_discr_ne_zero_iff _ (hfE.map
    (algebraMap (spectralIntegerRing K E.val) E.val))).mp
  rw [monic_discr_map _ hfE]
  intro hz
  change ((normLimitCoordinatePolynomial K L p E f).discr : E.val) = 0 at hz
  have hv := normLimitCoordinatePolynomial_discr_valuation K L p E hb h r hrb f hf hr
  rw [hz, map_zero] at hv
  exact (not_lt_of_ge zero_le) (hr.trans_eq hv.symm)

/-- Actual separability supplies a finite precision strictly beyond the
original nonzero discriminant value. -/
theorem exists_normLimit_discr_precision :
    letI := normLimitField K L p
    ∀ (f : Oₓ[X]), f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      ∃ r : ℕ, WithZero.exp (-(r : ℤ)) <
        normLimitValuation K L (f.discr : NormLimit K L) := by
  let := normLimitField K L p
  intro f hf hsep
  have hd := (monic_discr_ne_zero_iff _ (hf.map (algebraMap Oₓ (NormLimit K L)))).mpr hsep
  rw [monic_discr_map f hf] at hd
  change (f.discr : NormLimit K L) ≠ 0 at hd
  let w := normLimitValuation K L (f.discr : NormLimit K L)
  have hw : w ≠ 0 := fun hz ↦ hd ((normLimitValuation_eq_zero_iff K L _).mp hz)
  let r := (-WithZero.log w).toNat + 1
  refine ⟨r, (WithZero.lt_log_iff_exp_lt hw).mp ?_⟩
  dsimp [r]
  omega

/-- Along every original finite-coordinate sequence with actual full products
at depths tending to infinity, the original discriminant value is eventually
constant and the actual coordinate polynomials are separable. -/
theorem eventually_normLimitCoordinatePolynomial_discr_stable
    (F : ℕ → FiniteLayer K L) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hF : ∀ n, (F n).HasFullUpper K L (c n))
    (hctop : Filter.Tendsto c Filter.atTop Filter.atTop) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      ∀ᶠ n in Filter.atTop,
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
            (F n).val ((normLimitCoordinatePolynomial K L p (F n) f).discr : (F n).val)
                =
          normLimitValuation K L (f.discr : NormLimit K L) ∧
        ((normLimitCoordinatePolynomial K L p (F n) f).map
          (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  let := normLimitField K L p
  intro f hf hsep
  obtain ⟨r, hr⟩ := exists_normLimit_discr_precision K L p f hf hsep
  have hp : 0 < ((p - 1 : ℕ) : ℝ) / p := by
    have hp' := (Fact.out : p.Prime).two_le
    have h₁ : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
    exact div_pos h₁ (by exact_mod_cast (Fact.out : p.Prime).pos)
  have htop := Filter.Tendsto.const_mul_atTop hp hctop
  filter_upwards [htop.eventually (Filter.eventually_ge_atTop (r : ℝ))] with n hn
  have hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * c n⌉₊ := by
    exact_mod_cast hn.trans (Nat.le_ceil _)
  exact ⟨normLimitCoordinatePolynomial_discr_valuation K L p (F n)
      (hc n) (hF n) r hrb f hf hr,
    separable_normLimitCoordinatePolynomial K L p (F n)
      (hc n) (hF n) r hrb f hf hr⟩

/-- A genuine increasing cofinal sequence of original finite fields has full
upper depths tending to infinity and stabilizes every original monic separable
polynomial's discriminant, with actual eventual finite-field separability. -/
theorem exists_cofinal_normLimitCoordinatePolynomial_discr_stable :
    letI := normLimitField K L p
    ∃ F : ℕ → FiniteLayer K L, Monotone F ∧
      (∀ n, (F n).HasFullUpper K L ((n : ℝ) + 1)) ∧
      (∀ D : FiniteLayer K L, ∃ n, D ≤ F n) ∧
      ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
        ∀ᶠ n in Filter.atTop,
          (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K (F n).val)).valuation
              (F n).val ((normLimitCoordinatePolynomial K L p (F n) f).discr : (F
                  n).val) =
            normLimitValuation K L (f.discr : NormLimit K L) ∧
          ((normLimitCoordinatePolynomial K L p (F n) f).map
            (algebraMap (spectralIntegerRing K (F n).val) (F n).val)).Separable := by
  let := normLimitField K L p
  let c (n : ℕ) : ℝ := (n : ℝ) + 1
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  obtain ⟨F, hmono, hF, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_fullUpper_stages K L c (fun n ↦ (hc n).le)
  refine ⟨F, hmono, hF, hcofinal, ?_⟩
  apply eventually_normLimitCoordinatePolynomial_discr_stable K L p F c hc hF
  exact Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
    tendsto_natCast_atTop_atTop

end FontaineWintenberger
