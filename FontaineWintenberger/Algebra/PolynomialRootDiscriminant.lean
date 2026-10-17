/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.PolynomialDiscriminant
public import Mathlib.RingTheory.Valuation.Extension

/-!
# Discriminant bounds for two original roots

Integral monic division and multiplicativity of the existing resultant
isolate the squared difference of two specified roots. The remaining factor
is integral, so the original discriminant has at least twice their distance's
additive valuation.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Monic division at two distinct original roots gives an integral monic
residual polynomial, without selecting any of the other roots. -/
theorem exists_monic_two_root_factor (f : R[X]) (hf : f.Monic)
    (a b : R) (ha : f.IsRoot a) (hb : f.IsRoot b) (hab : a ≠ b) :
    ∃ g : R[X], g.Monic ∧ f = (X - C a) * ((X - C b) * g) := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
  have hqmonic : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hf)
  have hqb : q.IsRoot b := by
    have ht := hb
    rw [IsRoot, hq, eval_mul, eval_sub, eval_X, eval_C] at ht
    exact (mul_eq_zero.mp ht).resolve_left (sub_ne_zero.mpr hab.symm)
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hqb
  exact ⟨g, (monic_X_sub_C b).of_mul_monic_left (hg ▸ hqmonic), by rw [hq, hg]⟩

/-- The square of any distinct integral-root difference divides the existing
discriminant in the original coefficient domain. -/
theorem sq_sub_dvd_discr (f : R[X]) (hf : f.Monic)
    (a b : R) (ha : f.IsRoot a) (hb : f.IsRoot b) (hab : a ≠ b) :
    (a - b) ^ 2 ∣ f.discr := by
  obtain ⟨g, hg, heq⟩ := exists_monic_two_root_factor f hf a b ha hb hab
  let A : R[X] := X - C a
  let B : R[X] := X - C b
  have hA : A.Monic := monic_X_sub_C a
  have hB : B.Monic := monic_X_sub_C b
  have hdeg : f.natDegree = A.natDegree + (B * g).natDegree := by
    rw [heq]
    exact hA.natDegree_mul (hB.mul hg)
  have hderA : f.derivative.eval a = (a - b) * g.eval a := by
    rw [heq]
    simp [derivative_mul]
  have hderB : f.derivative.eval b = (b - a) * g.eval b := by
    rw [heq]
    simp [derivative_mul]
  let n := f.natDegree - 1
  have hn : f.derivative.natDegree ≤ n := natDegree_derivative_le f
  have hres : f.resultant f.derivative f.natDegree n =
      f.derivative.eval a * (f.derivative.eval b *
        g.resultant f.derivative g.natDegree n) := by
    calc
      _ = (A * (B * g)).resultant f.derivative
          (A.natDegree + (B * g).natDegree) n := by
        rw [← heq, hdeg]
      _ = A.resultant f.derivative A.natDegree n *
          (B * g).resultant f.derivative (B * g).natDegree n :=
        resultant_mul_left A (B * g) f.derivative n hn
      _ = _ := by
        rw [hB.natDegree_mul hg, resultant_mul_left B g f.derivative n hn]
        simp only [A, B, natDegree_X_sub_C, resultant_X_sub_C_left _ n _ hn]
  let s : R := (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)
  let c : R := -(g.eval a * g.eval b * g.resultant f.derivative g.natDegree n)
  have hs : s * f.discr = (a - b) ^ 2 * c := by
    rw [show s * f.discr = f.resultant f.derivative f.natDegree n from
      monic_discr_resultant f hf, hres, hderA, hderB]
    dsimp [c]
    ring
  have hss : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow]
    simp
  refine ⟨s * c, ?_⟩
  calc
    f.discr = s * (s * f.discr) := by rw [← mul_assoc, hss, one_mul]
    _ = (a - b) ^ 2 * (s * c) := by rw [hs]; ring

section Valuation

variable {C Γ : Type*} [Field C] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation C Γ)

/-- Two specified roots of a monic integral polynomial satisfy the exact
squared-difference discriminant bound on the original valued field. Root
integrality is proved, rather than assumed. The zero-discriminant case is
included, so no separability hypothesis is needed for this stronger bound. -/
theorem valuation_discr_le_sub_sq (f : v.valuationSubring[X]) (hf : f.Monic)
    (a b : C) (ha : aeval a f = 0) (hb : aeval b f = 0) (hab : a ≠ b) :
    v (f.discr : C) ≤ v (a - b) ^ 2 := by
  let a₀ : v.valuationSubring := ⟨a, monic_root_valuation_le_one v f hf a ha⟩
  let b₀ : v.valuationSubring := ⟨b, monic_root_valuation_le_one v f hf b hb⟩
  have ha₀ : f.IsRoot a₀ := by
    apply Subtype.val_injective
    change algebraMap v.valuationSubring C (f.eval a₀) = 0
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact ha
  have hb₀ : f.IsRoot b₀ := by
    apply Subtype.val_injective
    change algebraMap v.valuationSubring C (f.eval b₀) = 0
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact hb
  have hab₀ : a₀ ≠ b₀ := fun h ↦ hab (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := sq_sub_dvd_discr f hf a₀ b₀ ha₀ hb₀ hab₀
  have he : (f.discr : C) = (a - b) ^ 2 * (c : C) :=
    congrArg (fun x : v.valuationSubring ↦ (x : C)) hc
  rw [he, map_mul, map_pow]
  exact mul_le_of_le_one_right' c.property

/-- The same bound in Mathlib's associated additive valuation is literally
twice the root-difference value, with the original discriminant value. -/
theorem additiveValuation_two_nsmul_sub_le_discr
    (f : v.valuationSubring[X]) (hf : f.Monic)
    (a b : C) (ha : aeval a f = 0) (hb : aeval b f = 0) (hab : a ≠ b) :
    (2 : ℕ) • (Valuation.toAddValuation v) (a - b) ≤
      (Valuation.toAddValuation v) (f.discr : C) := by
  rw [two_nsmul]
  change v (f.discr : C) ≤ v (a - b) * v (a - b)
  simpa only [pow_two] using valuation_discr_le_sub_sq v f hf a b ha hb hab

omit [IsDomain R] in
/-- Coefficient maps to the original valuation ring preserve the discriminant
and the pair-root bound. This applies directly to a polynomial from the base
field evaluated in any actual valued splitting field. -/
theorem valuation_mapped_discr_le_sub_sq
    (f : R[X]) (hf : f.Monic) (φ : R →+* v.valuationSubring)
    (a b : C) (ha : aeval a (f.map φ) = 0) (hb : aeval b (f.map φ) = 0)
    (hab : a ≠ b) :
    v (φ f.discr : C) ≤ v (a - b) ^ 2 := by
  rw [← monic_discr_map f hf φ]
  exact valuation_discr_le_sub_sq v (f.map φ) (hf.map φ) a b ha hb hab

/-- The discriminant's additive value is nonnegative in the original
valuation ring, with no residue-field cardinality assumption. -/
theorem additiveValuation_discr_nonneg (f : v.valuationSubring[X]) :
    0 ≤ (Valuation.toAddValuation v) (f.discr : C) := by
  change v (f.discr : C) ≤ 1
  exact f.discr.property

/-- The separable monic polynomial's discriminant has finite original
additive value, as a consequence of its actual nonvanishing in the field. -/
theorem additiveValuation_discr_ne_top (f : v.valuationSubring[X]) (hf : f.Monic)
    (hsep : (f.map (algebraMap v.valuationSubring C)).Separable) :
    (Valuation.toAddValuation v) (f.discr : C) ≠ ⊤ := by
  apply (AddValuation.ne_top_iff _).mpr
  have hd := (monic_discr_ne_zero_iff _ (hf.map (algebraMap v.valuationSubring C))).mpr hsep
  rw [monic_discr_map f hf (algebraMap v.valuationSubring C)] at hd
  exact hd

section Extension

variable {K ΓK : Type*} [Field K] [Algebra K C] [LinearOrderedCommGroupWithZero ΓK]
variable (vK : Valuation K ΓK) [vK.HasExtension v]

/-- For an actual extension valuation, the bound uses the original base
polynomial's original discriminant mapped into the original extension field.
The canonical map of actual valuation rings supplies integral coefficients. -/
theorem valuation_discr_le_sub_sq_of_extension
    (f : vK.valuationSubring[X]) (hf : f.Monic)
    (a b : C) (ha : aeval a f = 0) (hb : aeval b f = 0) (hab : a ≠ b) :
    v (algebraMap K C (f.discr : K)) ≤ v (a - b) ^ 2 := by
  let φ := algebraMap vK.valuationSubring v.valuationSubring
  have hcomm : (algebraMap v.valuationSubring C).comp φ =
      algebraMap vK.valuationSubring C := by
    ext x
    rfl
  have ha' : aeval a (f.map φ) = 0 := by rw [← aeval_eq_aeval_map hcomm]; exact ha
  have hb' : aeval b (f.map φ) = 0 := by rw [← aeval_eq_aeval_map hcomm]; exact hb
  exact valuation_mapped_discr_le_sub_sq v f hf φ a b ha' hb' hab

/-- The original valued-extension bound in additive form: twice the value
of any distinct root difference is at most the actual base discriminant value. -/
theorem additiveValuation_two_nsmul_sub_le_discr_of_extension
    (f : vK.valuationSubring[X]) (hf : f.Monic)
    (a b : C) (ha : aeval a f = 0) (hb : aeval b f = 0) (hab : a ≠ b) :
    (2 : ℕ) • (Valuation.toAddValuation v) (a - b) ≤
      (Valuation.toAddValuation v) (algebraMap K C (f.discr : K)) := by
  rw [two_nsmul]
  change v (algebraMap K C (f.discr : K)) ≤ v (a - b) * v (a - b)
  simpa only [pow_two] using valuation_discr_le_sub_sq_of_extension v vK f hf a b ha hb hab

end Extension

end Valuation

end FontaineWintenberger
