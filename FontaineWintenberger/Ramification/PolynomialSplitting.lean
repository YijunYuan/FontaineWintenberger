/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.PolynomialRootDiscriminant
public import FontaineWintenberger.Ramification.AbsoluteGalois
public import FontaineWintenberger.Ramification.NormValuation
public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Splitting degrees and discriminant cutoffs for actual upper groups

The faithful action on the original root set bounds the actual splitting
degree by the degree factorial. Integral root separation then bounds the
upper ramification groups of the actual splitting field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

/-- The actual splitting degree is at most the degree factorial, by the
faithful permutation action on the original root set. -/
theorem finrank_splittingField_le_factorial {E : Type*} [Field E]
    (f : E[X]) (hsep : f.Separable) :
    Module.finrank E f.SplittingField ≤ f.natDegree.factorial := by
  let : Fact ((f.map (algebraMap E f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  rw [← Polynomial.Gal.card_of_separable hsep]
  calc
    Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
      Nat.card_le_card_of_injective (Polynomial.Gal.galActionHom f f.SplittingField)
        (Polynomial.Gal.galActionHom_injective f f.SplittingField)
    _ = f.natDegree.factorial := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card,
        card_rootSet_eq_natDegree hsep (SplittingField.splits f)]

/-- The factorial bound applies to every actual splitting field, with its
original base-field algebra. -/
theorem finrank_le_factorial_of_isSplittingField {E P : Type*} [Field E] [Field P]
    [Algebra E P] (f : E[X]) [IsSplittingField E P f] (hsep : f.Separable) :
    Module.finrank E P ≤ f.natDegree.factorial := by
  rw [(IsSplittingField.algEquiv P f).toLinearEquiv.finrank_eq]
  exact finrank_splittingField_le_factorial f hsep

section HerbrandBound

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

/-- Every actual lower-cardinality ratio is at most one, so the original
Herbrand integral lies below its argument. -/
theorem herbrandFunction_le_self (t : ℝ) : herbrandFunction (R := R) G t ≤ t := by
  by_cases ht : t ≤ 0
  · exact (herbrandFunction_of_nonpos G ht).le
  · have ht0 : 0 ≤ t := (not_le.mp ht).le
    rw [herbrandFunction, ite_eq_right ht]
    have hi := intervalIntegral.integral_mono_on ht0
      ((intervalIntegrable_card_lowerRamificationGroupReal (R := R) G 0 t).div_const _)
      (intervalIntegrable_const (c := (1 : ℝ)))
      (fun s hs => (div_le_one
        (show (0 : ℝ) < Nat.card (lowerRamificationGroup G
          (IsLocalRing.maximalIdeal R) 0) from Nat.cast_pos.mpr Nat.card_pos)).mpr
        (by simpa only [lowerRamificationGroupReal, Int.ceil_zero] using
          antitone_card_lowerRamificationGroupReal (R := R) G hs.1))
    simpa using hi

/-- The inverse of the actual Herbrand integral lies above every source index. -/
theorem le_inverseHerbrandFunction {u : ℝ} (hu : -1 ≤ u) :
    u ≤ inverseHerbrandFunction (R := R) G u := by
  simpa only [herbrandFunction_inverseHerbrandFunction G hu] using
    herbrandFunction_le_self (R := R) G (inverseHerbrandFunction (R := R) G u)

end HerbrandBound

section ValuedRoots

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (P : Type*) [Field P] [Algebra K P] [FiniteDimensional K P]
    [Algebra.IsSeparable K P]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OP" => spectralIntegerRing K P

/-- The canonical ramification index is at most the actual extension degree. -/
theorem spectral_ramificationIdx_le_finrank :
    (IsLocalRing.maximalIdeal OP).ramificationIdx OK ≤ Module.finrank K P := by
  rw [← local_ramificationIdx_mul_residueDegree_eq_finrank OK OP K P]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

omit [CompleteSpace K] in
/-- A separable monic integral polynomial has finite original DVR
discriminant value. -/
theorem addVal_discr_ne_top (f : OK[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap OK K)).Separable) :
    IsDiscreteValuationRing.addVal OK f.discr ≠ ⊤ := by
  apply IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
  intro hz
  have hd := (monic_discr_ne_zero_iff _ (hf.map (algebraMap OK K))).mpr hsep
  rw [monic_discr_map f hf (algebraMap OK K), hz, map_zero] at hd
  exact hd rfl

/-- At an index above the original discriminant value times the actual
ramification index, every actual upper automorphism fixes every original root.
Root integrality and the lower displacement bound are derived internally. -/
theorem upperRamificationGroup_fixes_integral_polynomial_root
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : ((IsLocalRing.maximalIdeal OP).ramificationIdx OK : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (g : P ≃ₐ[K] P) (hg : g ∈ upperRamificationGroup (R := OP) (P ≃ₐ[K] P) b)
    (a : P) (ha : aeval a f = 0) : g a = a := by
  let e := (IsLocalRing.maximalIdeal OP).ramificationIdx OK
  let d := (IsDiscreteValuationRing.addVal OK f.discr).toNat
  have hd : IsDiscreteValuationRing.addVal OK f.discr = (d : ℕ∞) :=
    (ENat.natCast_toNat (addVal_discr_ne_top K f hf hsep)).symm
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  let t := inverseHerbrandFunction (R := OP) (P ≃ₐ[K] P) b
  have hbt : b ≤ t := le_inverseHerbrandFunction _ (by linarith)
  let n := (⌈t⌉ + 1).toNat
  have hn : b < (n : ℝ) := by
    have ht0 : 0 ≤ t := hb0.trans hbt
    have hceil : (0 : ℤ) ≤ ⌈t⌉ := Int.ceil_nonneg ht0
    have hcast : (n : ℝ) = (⌈t⌉ : ℝ) + 1 := by
      have hc : (n : ℤ) = ⌈t⌉ + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hc
    rw [hcast]
    linarith [Int.le_ceil t]
  let a₀ : OP := ⟨a, (isIntegral_iff_spectralNorm_le_one K a).mp ⟨f, hf, ha⟩⟩
  let fP := f.map (algebraMap OK OP)
  have hcomm : (algebraMap OP P).comp (algebraMap OK OP) = algebraMap OK P := by
    ext x
    rfl
  have haP : fP.IsRoot a₀ := by
    apply Subtype.val_injective
    change algebraMap OP P (fP.eval a₀) = 0
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact (aeval_eq_aeval_map hcomm f a).symm.trans ha
  have hgroot : aeval (g a) f = 0 := by
    rw [show g a = (g.restrictScalars OK) a from rfl, aeval_algHom_apply, ha, map_zero]
  have hgaP : fP.IsRoot (g • a₀) := by
    apply Subtype.val_injective
    change algebraMap OP P (fP.eval (g • a₀)) = 0
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact (aeval_eq_aeval_map hcomm f (g a)).symm.trans hgroot
  by_contra hga
  have hne : g • a₀ ≠ a₀ := fun h => hga (congrArg Subtype.val h)
  have hpair := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr
    (sq_sub_dvd_discr fP (hf.map _) (g • a₀) a₀ hgaP haP hne)
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, monic_discr_map f hf,
    addVal_algebraMap OK OP, hd] at hpair
  have hlower : (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal OP (g • a₀ - a₀) := by
    exact (mem_lowerRamificationGroup_iff_addVal (P ≃ₐ[K] P) ⌈t⌉ g).mp hg a₀
  have hsmall : (n : ℕ∞) ≤ (e : ℕ∞) * d := by
    have hdouble : (n : ℕ∞) ≤ 2 * n := by
      rw [two_mul]
      exact le_add_of_nonneg_right zero_le
    have hmul : 2 * (n : ℕ∞) ≤ 2 * IsDiscreteValuationRing.addVal OP (g • a₀ - a₀) := by
      gcongr
    exact hdouble.trans (hmul.trans hpair)
  have hn' : n ≤ e * d := by exact_mod_cast hsmall
  have hnreal : (n : ℝ) ≤ (e : ℝ) * d := by exact_mod_cast hn'
  exact (not_lt_of_ge (hnreal.trans hb)) hn

end ValuedRoots

section SplittingCutoff

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (P : Type*) [Field P] [Algebra K P]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The actual splitting field has trivial upper group above the degree
factorial times the original normalized discriminant value. Finiteness and
separability of this actual field are consequences of its splitting property. -/
theorem upperRamificationGroup_splittingField_eq_bot
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    [IsSplittingField K P (f.map (algebraMap OK K))]
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b) :
    letI : FiniteDimensional K P := IsSplittingField.finiteDimensional P (f.map (algebraMap OK K))
    letI : IsGalois K P := IsGalois.of_separable_splitting_field hsep
    upperRamificationGroup (R := spectralIntegerRing K P) (P ≃ₐ[K] P) b = ⊥ := by
  let : FiniteDimensional K P := IsSplittingField.finiteDimensional P (f.map (algebraMap OK K))
  let : IsGalois K P := IsGalois.of_separable_splitting_field hsep
  have he : (IsLocalRing.maximalIdeal (spectralIntegerRing K P)).ramificationIdx OK ≤
      f.natDegree.factorial := by
    apply (spectral_ramificationIdx_le_finrank K P).trans
    simpa only [hf.natDegree_map] using
      finrank_le_factorial_of_isSplittingField (P := P) (f.map (algebraMap OK K)) hsep
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  have hroots : ∀ a ∈ (f.map (algebraMap OK K)).rootSet P, g a = a := by
    intro a ha
    apply upperRamificationGroup_fixes_integral_polynomial_root K P f hf hsep
      (le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (Nat.cast_nonneg _)) hb)
      g hg a
    have hcomm : (algebraMap K P).comp (algebraMap OK K) = algebraMap OK P := by
      ext x
      rfl
    exact (aeval_eq_aeval_map hcomm f a).trans (aeval_eq_zero_of_mem_rootSet ha)
  apply AlgEquiv.ext
  intro x
  change g x = x
  apply (AlgHom.mem_equalizer g.toAlgHom (1 : P ≃ₐ[K] P).toAlgHom x).mp
  have htop : AlgHom.equalizer g.toAlgHom (1 : P ≃ₐ[K] P).toAlgHom = ⊤ := by
    rw [eq_top_iff, ← IsSplittingField.adjoin_rootSet P (f.map (algebraMap OK K)),
      Algebra.adjoin_le_iff]
    exact hroots
  rw [htop]
  exact Algebra.mem_top

end SplittingCutoff

section AbsoluteRoots

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- Above the factorial-discriminant cutoff, the original absolute upper
group fixes every original root in the actual separable closure. The finite
Galois stage is the field generated by these same roots. -/
theorem absoluteUpperRamificationGroup_fixes_integral_polynomial_root
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (g : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hg : g ∈ absoluteUpperRamificationGroup K b)
    (a : SeparableClosure K) (ha : aeval a f = 0) : g a = a := by
  let fK := f.map (algebraMap OK K)
  have hs : (fK.map (algebraMap K (SeparableClosure K))).Splits :=
    IsSepClosed.splits_codomain fK hsep
  let P := IntermediateField.adjoin K (fK.rootSet (SeparableClosure K))
  let : IsSplittingField K P fK := IntermediateField.adjoin_rootSet_isSplittingField hs
  let : FiniteDimensional K P := IsSplittingField.finiteDimensional P fK
  let : IsGalois K P := IsGalois.of_separable_splitting_field hsep
  let PG : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := P }
  have hgP := (mem_upperRamificationGroupInfinite K (SeparableClosure K) b g).mp hg PG
  have hbot := upperRamificationGroup_splittingField_eq_bot K P f hf hsep hb
  have hg1 : g.restrictNormal P = 1 := by
    change g.restrictNormal P ∈ upperRamificationGroup (R := spectralIntegerRing K P)
      (P ≃ₐ[K] P) b at hgP
    rw [hbot] at hgP
    exact hgP
  have haK : a ∈ fK.rootSet (SeparableClosure K) := by
    apply (hf.map (algebraMap OK K)).mem_rootSet.mpr
    rwa [aeval_map_algebraMap K]
  let aP : P := ⟨a, IntermediateField.subset_adjoin K _ haK⟩
  have hc := congrArg (fun s : P ≃ₐ[K] P => algebraMap P (SeparableClosure K) (s aP)) hg1
  rw [AlgEquiv.restrictNormal_commutes] at hc
  exact hc

end AbsoluteRoots

end FontaineWintenberger
