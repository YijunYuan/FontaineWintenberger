/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Estimates.FiniteLayer
public import FontaineWintenberger.Ramification.Norm.Approximation

/-!
# Truncated wild norms

At the precision supplied by the finite ramification bound, the
integer norm descends to a ring homomorphism on the
maximal-ideal quotients. Perfect-residue digits prove its surjectivity.

## Main definitions

* `truncatedAddVal`: The canonical normalized additive value, truncated at the quotient precision.
* `truncatedNorm`: The integer norm descends to the maximal-ideal quotients at every precision
  proved by the finite ramification bound.

## Main results

* `exists_integerNorm_sub_mem_of_le_apfRamificationBound`: Finite perfect-residue digits approximate
  every integer by the norm at the supplied ramification precision.
* `truncatedNorm_surjective`: Finite perfect-residue digits supply a preimage of every class under
  the truncated norm.
* `addVal_integerNorm_of_totallyRamified`: Total ramification makes the integer norm preserve the
  exact canonical normalized additive valuation, including at zero.
* `truncatedNorm_truncatedAddVal_mk`: The image of every integral representative has its exact
  truncated normalized valuation under the truncated norm.
* `truncatedNorm_truncatedAddVal`: Across the two precisions, the quotient norm preserves exactly
  the normalized valuation truncated at the target precision.
* `truncatedNorm_comp`: Norm transitivity gives exact composition of the truncated ring maps across
  every tower of the stated precisions.
* `truncatedNorm_self`: For the identity inclusion the quotient norm is the ordinary canonical
  reduction of precision.
* `exists_surjective_truncatedNorm_self`: Every equal-field norm gives a surjective quotient
  reduction at arbitrary precisions, without any numerical hypothesis on the infinite first bound.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

attribute [local instance] FractionRing.liftAlgebra

section TruncatedValuation

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem min_addVal_eq_of_sub_mem_pow (r : ℕ) (x y : R)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R ^ r) :
    min (IsDiscreteValuationRing.addVal R x) (r : ℕ∞) =
      min (IsDiscreteValuationRing.addVal R y) (r : ℕ∞) := by
  have h₁ := (mem_maximalIdeal_pow_iff_addVal (x - y) r).mp hxy
  have h₂ := (mem_maximalIdeal_pow_iff_addVal (y - x) r).mp
    (by simpa only [neg_sub] using (IsLocalRing.maximalIdeal R ^ r).neg_mem hxy)
  apply le_antisymm
  · apply le_min _ (min_le_right _ _)
    calc
      _ ≤ min (IsDiscreteValuationRing.addVal R x)
          (IsDiscreteValuationRing.addVal R (y - x)) := min_le_min_left _ h₂
      _ ≤ IsDiscreteValuationRing.addVal R (x + (y - x)) :=
        IsDiscreteValuationRing.addVal_add
      _ = IsDiscreteValuationRing.addVal R y := congrArg _ (by ring)
  · apply le_min _ (min_le_right _ _)
    calc
      _ ≤ min (IsDiscreteValuationRing.addVal R y)
          (IsDiscreteValuationRing.addVal R (x - y)) := min_le_min_left _ h₁
      _ ≤ IsDiscreteValuationRing.addVal R (y + (x - y)) :=
        IsDiscreteValuationRing.addVal_add
      _ = IsDiscreteValuationRing.addVal R x := congrArg _ (by ring)

/-- The canonical normalized additive value, truncated at the quotient
precision. It is well defined on the maximal-ideal quotient. -/
def truncatedAddVal (r : ℕ) : R ⧸ IsLocalRing.maximalIdeal R ^ r → ℕ∞ :=
  Quotient.lift (fun x => min (IsDiscreteValuationRing.addVal R x) (r : ℕ∞))
    (by
      intro x y hxy
      exact min_addVal_eq_of_sub_mem_pow R r x y
        (Ideal.Quotient.eq.mp (Quotient.sound hxy)))

@[simp]
theorem truncatedAddVal_mk (r : ℕ) (x : R) :
    truncatedAddVal R r (Ideal.Quotient.mk _ x) =
      min (IsDiscreteValuationRing.addVal R x) (r : ℕ∞) := rfl

end TruncatedValuation

namespace FiniteIntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local notation "p" => residueChar K

/-- Ramification, degree and first-bound assumptions for the truncated norm of an inclusion. -/
structure TruncatedNormConditions {E F : FiniteIntermediateField K L}
    (hEF : E ≤ F) (d : ℕ) (b : ℝ) : Prop where
  totallyRamified : IsTotallyRamifiedInclusion hEF
  degree : E.val.relfinrank F.val = p ^ d
  bound : (b : EReal) ≤ relativeRamificationBound hEF

/-- Assemble the conditions from the degree of the extension over its smaller field. -/
theorem TruncatedNormConditions.of_finrank {E F : FiniteIntermediateField K L} {hEF : E ≤ F}
    {d : ℕ} {b : ℝ} (he : IsTotallyRamifiedInclusion hEF)
    (hd : Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ d)
    (hb : (b : EReal) ≤ relativeRamificationBound hEF) : TruncatedNormConditions hEF d b :=
  ⟨he, (IntermediateField.relfinrank_eq_finrank_of_le hEF).trans hd, hb⟩

theorem TruncatedNormConditions.finrank_eq {E F : FiniteIntermediateField K L} {hEF : E ≤ F}
    {d : ℕ} {b : ℝ} (h : TruncatedNormConditions hEF d b) :
    Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ d :=
  (IntermediateField.relfinrank_eq_finrank_of_le hEF).symm.trans h.degree

section HighBreak

variable (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
variable (d : ℕ) (b : ℝ)
variable (conditions : TruncatedNormConditions hEF d b)
variable (he : IsTotallyRamifiedInclusion hEF)
variable (hd : Module.finrank E.val (IntermediateField.extendScalars hEF) = residueChar K ^ d)

/-- The integer norm descends to the maximal-ideal quotients
at every precision proved by the finite ramification bound. -/
def truncatedNorm (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  have hadd (x y : spectralIntegerRing K F.val) :
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r :=
    Ideal.pow_le_pow_right hrb
      (integerNorm_add_congruence_of_le_apfRamificationBound E F hEF
        conditions.totallyRamified d conditions.degree b conditions.bound x y)
  let N : spectralIntegerRing K F.val →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r :=
    { toFun := fun x => Ideal.Quotient.mk _ (integerNorm E F hEF x)
      map_one' := by simp
      map_mul' := fun x y => by simp
      map_zero' := by
        have hzero : integerNorm E F hEF 0 = 0 := by
          apply Subtype.ext
          rw [coe_integerNorm]
          exact (norm_eq_zero_iff E F hEF 0).mpr rfl
        simp only [hzero, map_zero]
      map_add' := fun x y => by
        change Ideal.Quotient.mk _ (integerNorm E F hEF (x + y)) =
          Ideal.Quotient.mk _ (integerNorm E F hEF x) +
            Ideal.Quotient.mk _ (integerNorm E F hEF y)
        rw [← map_add]
        exact Ideal.Quotient.eq.mpr (by simpa only [sub_add_eq_sub_sub] using hadd x y) }
  exact Ideal.Quotient.lift _ N (fun x hx => by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_le_pow_right hrs (integerNorm_mem_maximalIdeal_pow E F hEF hx))

@[simp]
theorem truncatedNorm_mk (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val) :
    truncatedNorm E F hEF d b conditions r s hrs hrb (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (integerNorm E F hEF x) := rfl

include he hd in
private theorem exists_integerNorm_sub_mem_of_add_congruence (r : ℕ)
    (hadd : ∀ x y : spectralIntegerRing K F.val,
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)
    (a : spectralIntegerRing K E.val) :
    ∃ x : spectralIntegerRing K F.val, integerNorm E F hEF x - a ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  let R := spectralIntegerRing K E.val
  let S := spectralIntegerRing K F.val
  let R₀ := 𝒪[K]
  have : Module.Finite R₀ R := extensionValuationSubring_moduleFinite K E.val
    (spectralValuation K E.val)
  have : Module.Finite R S := Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower R E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower R S F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R E.val).symm.toRingEquiv
      (FractionRing.algEquiv S F.val).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv R E.val).symm (FractionRing.algEquiv S F.val).symm y
  have : Module.Finite (IsLocalRing.ResidueField R₀) (IsLocalRing.ResidueField R) :=
    inferInstance
  let : PerfectField (IsLocalRing.ResidueField R) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R₀)
  let : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField R₀) (IsLocalRing.ResidueField R)).injective p
  have he' : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank R S := by
    rw [← IsFractionRing.finrank_eq R E.val S F.val]
    exact he
  have hd' : Module.finrank R S = p ^ d := by
    rw [← IsFractionRing.finrank_eq R E.val S F.val]
    exact hd
  have hN (x : S) : Algebra.intNorm R S x = integerNorm E F hEF x := by
    apply Subtype.ext
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm (A := R) (B := S) (K := E.val) (L := F.val) x
  have hadd' (x y : S) :
      Algebra.intNorm R S (x + y) - Algebra.intNorm R S x - Algebra.intNorm R S y ∈
        IsLocalRing.maximalIdeal R ^ r := by
    rw [hN, hN, hN]
    exact hadd x y
  obtain ⟨x, hx⟩ := exists_intNorm_sub_mem_maximalIdeal_pow R S p d r he' hd' hadd' a
  rw [hN] at hx
  exact ⟨x, hx⟩

include conditions in
/-- Finite perfect-residue digits approximate every integer
by the norm at the supplied ramification precision. -/
theorem exists_integerNorm_sub_mem_of_le_apfRamificationBound (r : ℕ)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (a : spectralIntegerRing K E.val) :
    ∃ x : spectralIntegerRing K F.val, integerNorm E F hEF x - a ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  exact exists_integerNorm_sub_mem_of_add_congruence E F hEF d
    conditions.totallyRamified conditions.finrank_eq r
    (fun x y => Ideal.pow_le_pow_right hrb
      (integerNorm_add_congruence_of_le_apfRamificationBound E F hEF
        conditions.totallyRamified d conditions.degree b conditions.bound x y)) a

/-- Finite perfect-residue digits supply a preimage of every class
under the truncated norm. -/
theorem truncatedNorm_surjective (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (truncatedNorm E F hEF d b conditions r s hrs hrb) := by
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, hx⟩ := exists_integerNorm_sub_mem_of_le_apfRamificationBound
    E F hEF d b conditions r hrb a
  refine ⟨Ideal.Quotient.mk _ x, ?_⟩
  rw [truncatedNorm_mk]
  exact Ideal.Quotient.eq.mpr hx

include he in
/-- Total ramification makes the integer norm preserve the exact
canonical normalized additive valuation, including at zero. -/
theorem addVal_integerNorm_of_totallyRamified (x : spectralIntegerRing K F.val) :
    IsDiscreteValuationRing.addVal (spectralIntegerRing K E.val) (integerNorm E F hEF x) =
      IsDiscreteValuationRing.addVal (spectralIntegerRing K F.val) x := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  let R := spectralIntegerRing K E.val
  let S := spectralIntegerRing K F.val
  let R₀ := 𝒪[K]
  have : Module.Finite R S := Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower R E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower R S F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R E.val).symm.toRingEquiv
      (FractionRing.algEquiv S F.val).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv R E.val).symm (FractionRing.algEquiv S F.val).symm y
  have he' : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank R S := by
    rw [← IsFractionRing.finrank_eq R E.val S F.val]
    exact he
  have hf : (IsLocalRing.maximalIdeal S).inertiaDeg R = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (local_ramificationIdx_pos R S)
    simpa only [mul_one, he'] using local_ramificationIdx_mul_inertiaDeg R S
  have hN : Algebra.intNorm R S x = integerNorm E F hEF x := by
    apply Subtype.ext
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm (A := R) (B := S) (K := E.val) (L := F.val) x
  have hv := addVal_intNorm R S x
  rw [hf, Nat.cast_one, one_mul, hN] at hv
  exact hv

/-- The image of every integral representative has its exact truncated
normalized valuation under the truncated norm. -/
theorem truncatedNorm_truncatedAddVal_mk (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val) :
    truncatedAddVal (spectralIntegerRing K E.val) r
        (truncatedNorm E F hEF d b conditions r s hrs hrb (Ideal.Quotient.mk _ x)) =
      min (IsDiscreteValuationRing.addVal (spectralIntegerRing K F.val) x) (r : ℕ∞) := by
  rw [truncatedNorm_mk, truncatedAddVal_mk,
    addVal_integerNorm_of_totallyRamified E F hEF conditions.totallyRamified]

/-- Across the two precisions, the quotient norm preserves exactly
the normalized valuation truncated at the target precision. -/
theorem truncatedNorm_truncatedAddVal (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) :
    truncatedAddVal (spectralIntegerRing K E.val) r
        (truncatedNorm E F hEF d b conditions r s hrs hrb x) =
      min (truncatedAddVal (spectralIntegerRing K F.val) s x) (r : ℕ∞) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncatedNorm_truncatedAddVal_mk, truncatedAddVal_mk, min_assoc]
  rw [min_eq_right (show (r : ℕ∞) ≤ s by exact_mod_cast hrs)]

/-- Norm transitivity gives exact composition of the
truncated ring maps across every tower of the stated precisions. -/
theorem truncatedNorm_comp (G : FiniteIntermediateField K L) (hFG : F ≤ G)
    (dFG dEG : ℕ) (bFG bEG : ℝ)
    (conditionsFG : TruncatedNormConditions hFG dFG bFG)
    (conditionsEG : TruncatedNormConditions (hEF.trans hFG) dEG bEG)
    (r s t : ℕ) (hrs : r ≤ s) (hst : s ≤ t)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (hsbFG : s ≤ ⌈((p - 1 : ℕ) : ℝ) / p * bFG⌉₊)
    (hrbEG : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * bEG⌉₊) :
    (truncatedNorm E F hEF d b conditions r s hrs hrb).comp
        (truncatedNorm F G hFG dFG bFG conditionsFG s t hst hsbFG) =
      truncatedNorm E G (hEF.trans hFG) dEG bEG conditionsEG r t
        (hrs.trans hst) hrbEG := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, truncatedNorm_mk]
  rw [integerNorm_integerNorm]

/-- For the identity inclusion the quotient norm is the
ordinary canonical reduction of precision. -/
theorem truncatedNorm_self
    (conditionsSelf : TruncatedNormConditions (E := E) (F := E) le_rfl d b)
    (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    truncatedNorm E E le_rfl d b conditionsSelf r s hrs hrb =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk]
  simpa only [integerNorm_self] using
    truncatedNorm_mk E E le_rfl d b conditionsSelf r s hrs hrb x

end HighBreak

/-- Every equal-field norm gives a surjective quotient reduction at arbitrary
precisions, without any numerical hypothesis on the infinite first bound. -/
theorem exists_surjective_truncatedNorm_self (E : FiniteIntermediateField K L) (r s : ℕ) (hrs : r ≤
    s) :
    ∃ N : (spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s)
        →+*
        spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r,
      Function.Surjective N ∧ ∀ x : spectralIntegerRing K E.val,
        N (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (integerNorm E E le_rfl x) := by
  refine ⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs), ?_, fun x => ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.factor_mk _ x⟩
  · simp only [Ideal.Quotient.factor_mk, integerNorm_self]

end FiniteIntermediateField

end FontaineWintenberger
