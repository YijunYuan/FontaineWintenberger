module

public import FontaineWintenberger.FieldOfNorms.FiniteLayerNormEstimates
public import FontaineWintenberger.Ramification.NormApproximation

/-!
# Actual truncated wild norms

At the precision supplied by the actual finite ramification bound, the
original integer norm descends to a ring homomorphism on the original
maximal-ideal quotients. Perfect-residue digits prove its surjectivity.
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

/-- The canonical normalized additive value, truncated at the actual quotient
precision. It is well defined on the actual maximal-ideal quotient. -/
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

namespace FiniteLayer

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

section HighBreak

variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]
variable (E F : FiniteLayer K L) (hEF : E ≤ F) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (d : ℕ) (b : ℝ)
variable (he :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
      (spectralIntegerRing K E.val) =
        Module.finrank E.val (IntermediateField.extendScalars hEF))
variable (hd : Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ d)
variable (hb :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    (b : EReal) ≤ apfRamificationBound E.val F')

/-- The original integer norm descends to the actual maximal-ideal quotients
at every precision proved by the actual finite ramification bound. -/
def truncatedNorm (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    (spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) →+*
      spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
  have hadd (x y : spectralIntegerRing K F.val) :
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r :=
    Ideal.pow_le_pow_right hrb
      (integerNorm_add_congruence_of_le_apfRamificationBound E F hEF p
        he d hd b hb x y)
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
    truncatedNorm E F hEF p d b he hd hb r s hrs hrb (Ideal.Quotient.mk _ x) =
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
  let R₀ := (NormedField.valuation (K := K)).valuationSubring
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

include he hd hb in
/-- Actual finite perfect-residue digits approximate every original integer
by the original norm at the supplied actual ramification precision. -/
theorem exists_integerNorm_sub_mem_of_le_apfRamificationBound (r : ℕ)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (a : spectralIntegerRing K E.val) :
    ∃ x : spectralIntegerRing K F.val, integerNorm E F hEF x - a ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  exact exists_integerNorm_sub_mem_of_add_congruence E F hEF p d he hd r
    (fun x y => Ideal.pow_le_pow_right hrb
      (integerNorm_add_congruence_of_le_apfRamificationBound E F hEF p
        he d hd b hb x y)) a

/-- Actual finite perfect-residue digits supply a preimage of every class
under the actual truncated norm. -/
theorem truncatedNorm_surjective (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    Function.Surjective (truncatedNorm E F hEF p d b he hd hb r s hrs hrb) := by
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, hx⟩ := exists_integerNorm_sub_mem_of_le_apfRamificationBound
    E F hEF p d b he hd hb r hrb a
  refine ⟨Ideal.Quotient.mk _ x, ?_⟩
  rw [truncatedNorm_mk]
  exact Ideal.Quotient.eq.mpr hx

include he in
omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Total ramification makes the original integer norm preserve the exact
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
  let R₀ := (NormedField.valuation (K := K)).valuationSubring
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
normalized valuation under the actual truncated norm. -/
theorem truncatedNorm_truncatedAddVal_mk (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val) :
    truncatedAddVal (spectralIntegerRing K E.val) r
        (truncatedNorm E F hEF p d b he hd hb r s hrs hrb (Ideal.Quotient.mk _ x)) =
      min (IsDiscreteValuationRing.addVal (spectralIntegerRing K F.val) x) (r : ℕ∞) := by
  rw [truncatedNorm_mk, truncatedAddVal_mk,
    addVal_integerNorm_of_totallyRamified E F hEF he]

/-- Across the two actual precisions, the quotient norm preserves exactly
the normalized valuation truncated at the target precision. -/
theorem truncatedNorm_truncatedAddVal (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (x : spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) :
    truncatedAddVal (spectralIntegerRing K E.val) r
        (truncatedNorm E F hEF p d b he hd hb r s hrs hrb x) =
      min (truncatedAddVal (spectralIntegerRing K F.val) s x) (r : ℕ∞) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncatedNorm_truncatedAddVal_mk, truncatedAddVal_mk, min_assoc]
  rw [min_eq_right (show (r : ℕ∞) ≤ s by exact_mod_cast hrs)]

/-- Original norm transitivity gives exact composition of the actual
truncated ring maps across every tower of the stated precisions. -/
theorem truncatedNorm_comp (G : FiniteLayer K L) (hFG : F ≤ G)
    (dFG dEG : ℕ) (bFG bEG : ℝ)
    (heFG : letI : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
      letI : IsScalarTower K F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralValuation_hasExtension_tower K (E := F.val) (L := G.val)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K G.val)).ramificationIdx
        (spectralIntegerRing K F.val) =
          Module.finrank F.val (IntermediateField.extendScalars hFG))
    (hdFG : Module.finrank F.val (IntermediateField.extendScalars hFG) = p ^ dFG)
    (hbFG : letI : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
      letI : IsScalarTower K F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralNorm.nontriviallyNormedField K F.val
      letI := spectralNorm.normedAlgebra K F.val
      letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := F.val))
      letI := spectralNorm.completeSpace K F.val
      letI := normedAlgebra_unitBall_isDiscreteValuationRing K F.val
      let B' := IntermediateField.extendScalars hFG
      letI : FiniteDimensional K B' := G.property
      letI : FiniteDimensional F.val B' := Module.Finite.right K F.val B'
      (bFG : EReal) ≤ apfRamificationBound F.val B')
    (heEG : letI : Algebra E.val G.val := (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
      letI : IsScalarTower K E.val G.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralValuation_hasExtension_tower K (E := E.val) (L := G.val)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K G.val)).ramificationIdx
        (spectralIntegerRing K E.val) =
          Module.finrank E.val (IntermediateField.extendScalars (hEF.trans hFG)))
    (hdEG : Module.finrank E.val (IntermediateField.extendScalars (hEF.trans hFG)) = p ^ dEG)
    (hbEG : letI : Algebra E.val G.val := (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
      letI : IsScalarTower K E.val G.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralNorm.nontriviallyNormedField K E.val
      letI := spectralNorm.normedAlgebra K E.val
      letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := E.val))
      letI := spectralNorm.completeSpace K E.val
      letI := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
      let B' := IntermediateField.extendScalars (hEF.trans hFG)
      letI : FiniteDimensional K B' := G.property
      letI : FiniteDimensional E.val B' := Module.Finite.right K E.val B'
      (bEG : EReal) ≤ apfRamificationBound E.val B')
    (r s t : ℕ) (hrs : r ≤ s) (hst : s ≤ t)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊)
    (hsbFG : s ≤ ⌈((p - 1 : ℕ) : ℝ) / p * bFG⌉₊)
    (hrbEG : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * bEG⌉₊) :
    (truncatedNorm E F hEF p d b he hd hb r s hrs hrb).comp
        (truncatedNorm F G hFG p dFG bFG heFG hdFG hbFG s t hst hsbFG) =
      truncatedNorm E G (hEF.trans hFG) p dEG bEG heEG hdEG hbEG r t
        (hrs.trans hst) hrbEG := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, truncatedNorm_mk]
  rw [integerNorm_integerNorm]

/-- For the original identity inclusion the actual quotient norm is the
ordinary canonical reduction of precision. -/
theorem truncatedNorm_self
    (heSelf : letI : Algebra E.val E.val := (IntermediateField.inclusion le_rfl).toRingHom.toAlgebra
      letI : IsScalarTower K E.val E.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralValuation_hasExtension_tower K (E := E.val) (L := E.val)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val)).ramificationIdx
        (spectralIntegerRing K E.val) =
          Module.finrank E.val
            (IntermediateField.extendScalars (show E.val ≤ E.val from le_rfl)))
    (hdSelf : Module.finrank E.val
      (IntermediateField.extendScalars (show E.val ≤ E.val from le_rfl)) = p ^ d)
    (hbSelf : letI : Algebra E.val E.val := (IntermediateField.inclusion (show E.val ≤ E.val from le_rfl)).toRingHom.toAlgebra
      letI : IsScalarTower K E.val E.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralNorm.nontriviallyNormedField K E.val
      letI := spectralNorm.normedAlgebra K E.val
      letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := E.val))
      letI := spectralNorm.completeSpace K E.val
      letI := normedAlgebra_unitBall_isDiscreteValuationRing K E.val
      let B' := IntermediateField.extendScalars (show E.val ≤ E.val from le_rfl)
      letI : FiniteDimensional K B' := E.property
      letI : FiniteDimensional E.val B' := Module.Finite.right K E.val B'
      (b : EReal) ≤ apfRamificationBound E.val B')
    (r s : ℕ) (hrs : r ≤ s)
    (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    truncatedNorm E E le_rfl p d b heSelf hdSelf hbSelf r s hrs hrb =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk]
  simpa only [integerNorm_self] using
    truncatedNorm_mk E E le_rfl p d b heSelf hdSelf hbSelf r s hrs hrb x

end HighBreak

/-- Every equal-field norm gives a surjective quotient reduction at arbitrary
precisions, without any numerical hypothesis on the infinite first bound. -/
theorem exists_surjective_truncatedNorm_self (E : FiniteLayer K L) (r s : ℕ) (hrs : r ≤ s) :
    ∃ N : (spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s) →+*
        spectralIntegerRing K E.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r,
      Function.Surjective N ∧ ∀ x : spectralIntegerRing K E.val,
        N (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (integerNorm E E le_rfl x) := by
  refine ⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs), ?_, fun x => ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.factor_mk _ x⟩
  · simp only [Ideal.Quotient.factor_mk, integerNorm_self]

end FiniteLayer

end FontaineWintenberger
