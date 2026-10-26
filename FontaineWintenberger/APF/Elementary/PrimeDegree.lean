/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.APF.Finite.Galois
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Different.TraceIdeal
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Norm.Congruence
public import FontaineWintenberger.Ramification.Upper.PrimeOrder

/-!
# Ramification of prime-degree extensions

Every subgroup of a prime-order Galois group is trivial or full. The
lower groups consequently give the same order to every nonidentity element.

The different and total ramification determine the unique finite
upper break of an arbitrary separable prime-degree extension.

The finite upper orbit index equals the intrinsic APF inertia index
with its residue-degree factor. The different therefore determines
the full intrinsic profile of a totally ramified prime-degree subextension.

The middle subsets in the product expansion form free orbits under left
translation. Each orbit contributes a trace of an integral element.

## Main results

* `spectralIntegerRing_lower_zero_eq_top_of_totallyRamified`: Total ramification makes the full
  Galois action inertial.
* `spectralIntegerRing_exists_common_break_of_prime_degree`: The common break is produced from prime
  field degree and total ramification.
* `spectralIntegerRing_different_order_of_common_order`: Hilbert's different formula specializes to
  the common-order formula.
* `apfRamificationBound_eq_common_break`: The public extended APF bound is the common upper break.
* `spectralIntegerRing_intTraceIdeal_of_common_break`: The trace ideal at a common break, with its
  exact floor exponent.
* `spectralIntegerRing_intTrace_order_bound`: The trace bound in normalized additive valuation,
  after clearing its positive denominator.
* `spectralIntegerRing_prime_degree_ramification`: Prime degree and total ramification produce the
  break, public APF bound, different, trace ideal, and trace valuation estimate together.
* `spectral_ramificationIdx_algEquiv`: Field isomorphisms preserve the canonical ramification index.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable [PerfectField 𝓀[K]]

local notation "OL" => spectralIntegerRing K L
local notation "GL" => L ≃ₐ[K] L

/-- Total ramification makes the full Galois action inertial. -/
theorem spectralIntegerRing_lower_zero_eq_top_of_totallyRamified
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    lowerRamificationGroup GL (IsLocalRing.maximalIdeal OL) 0 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [spectralIntegerRing_card_lower_zero K L, he, IsGalois.card_aut_eq_finrank K L]

/-- The common break is produced from prime field degree and total ramification. -/
theorem spectralIntegerRing_exists_common_break_of_prime_degree
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ t : ℕ, ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ) := by
  have : Fact (Nat.card GL).Prime := ⟨by rwa [IsGalois.card_aut_eq_finrank K L]⟩
  exact exists_common_ramificationOrder_succ_of_prime_card GL
    (spectralIntegerRing_lower_zero_eq_top_of_totallyRamified K L he)

/-- Hilbert's different formula specializes to the common-order formula. -/
theorem spectralIntegerRing_different_order_of_common_order {m : ℕ}
    (hm : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = m) :
    emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal 𝒪[K] OL) =
      (((Module.finrank K L - 1) * m : ℕ) : ℕ∞) := by
  classical
  rw [spectralIntegerRing_different_order_eq_sum_ramificationOrder K L,
    sum_ramificationOrder_of_common_order GL hm, IsGalois.card_aut_eq_finrank K L]

/-- The public extended APF bound is the common upper break. -/
theorem apfRamificationBound_eq_common_break [Nontrivial GL] {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ)) :
    apfRamificationBound K L = ((t : ℝ) : EReal) := by
  have ht0 : (-1 : ℝ) ≤ t := by have := Nat.cast_nonneg (α := ℝ) t; linarith
  rw [apfRamificationBound_eq_sSup_finite_upper K L]
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨u, hu, hg, rfl⟩
    have hut : u ≤ t := by
      by_contra h
      rw [upperRamificationGroup_of_common_order GL ht hu, ite_eq_right h] at hg
      exact bot_ne_top hg
    exact EReal.coe_le_coe_iff.mpr hut
  · apply le_sSup
    exact ⟨t, ht0, by rw [upperRamificationGroup_of_common_order GL ht ht0, ite_eq_left le_rfl],
        rfl⟩

/-- The trace ideal at a common break, with its exact floor exponent. -/
theorem spectralIntegerRing_intTraceIdeal_of_common_break {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ))
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    intTraceIdeal 𝒪[K] OL ⊤ = IsLocalRing.maximalIdeal 𝒪[K] ^
      (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) := by
  have h := intTraceIdeal_pow 𝒪[K] OL K L 0
  simpa only [pow_zero, Ideal.one_eq_top, spectralIntegerRing_different_order_of_common_order K L
      ht,
    ENat.toNat_natCast, Nat.add_zero, he] using h

private theorem trace_exponent_mul_le (p t : ℕ) (hp : 0 < p) :
    (p - 1) * t ≤ p * (((p - 1) * (t + 1)) / p) := by
  have hmod := Nat.mod_lt ((p - 1) * (t + 1)) hp
  have hdiv := Nat.mod_add_div ((p - 1) * (t + 1)) p
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel hp
  nlinarith

/-- The trace bound in normalized additive valuation, after clearing its
positive denominator. This includes zero traces with infinite valuation. -/
theorem spectralIntegerRing_intTrace_order_bound {t : ℕ}
    (ht : ∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ))
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L)
    (x : OL) :
    (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
      (Module.finrank K L : ℕ∞) *
        IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.intTrace 𝒪[K] OL x) := by
  have hmem : Algebra.intTrace 𝒪[K] OL x ∈ IsLocalRing.maximalIdeal 𝒪[K] ^
      (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) := by
    apply (intTraceIdeal_le_iff 𝒪[K] OL ⊤ _).mp
      (spectralIntegerRing_intTraceIdeal_of_common_break K L ht he).le x
    trivial
  have hval := (mem_maximalIdeal_pow_iff_addVal _ _).mp hmem
  have harith := trace_exponent_mul_le (Module.finrank K L) t (Module.finrank_pos (R := K) (M := L))
  exact (show (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
      (Module.finrank K L : ℕ∞) *
        (((Module.finrank K L - 1) * (t + 1) / Module.finrank K L : ℕ) : ℕ∞) by
      exact_mod_cast harith).trans (by gcongr)

/-- Prime degree and total ramification produce the break, public APF
bound, different, trace ideal, and trace valuation estimate together. -/
theorem spectralIntegerRing_prime_degree_ramification
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ t : ℕ,
      (∀ g : GL, g ≠ 1 → ramificationOrder (R := OL) GL g = (t + 1 : ℕ)) ∧
      apfRamificationBound K L = ((t : ℝ) : EReal) ∧
      emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal 𝒪[K] OL) =
        (((Module.finrank K L - 1) * (t + 1) : ℕ) : ℕ∞) ∧
      intTraceIdeal 𝒪[K] OL ⊤ = IsLocalRing.maximalIdeal 𝒪[K] ^
        (((Module.finrank K L - 1) * (t + 1)) / Module.finrank K L) ∧
      ∀ x : OL, (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
        (Module.finrank K L : ℕ∞) *
          IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.intTrace 𝒪[K] OL x) := by
  have : Nontrivial GL := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [IsGalois.card_aut_eq_finrank K L] using hp.one_lt)
  obtain ⟨t, ht⟩ := spectralIntegerRing_exists_common_break_of_prime_degree K L hp he
  exact ⟨t, ht, apfRamificationBound_eq_common_break K L ht,
    spectralIntegerRing_different_order_of_common_order K L ht,
    spectralIntegerRing_intTraceIdeal_of_common_break K L ht he,
    spectralIntegerRing_intTrace_order_bound K L ht he⟩

end Spectral

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

open IsDiscreteValuationRing Polynomial

section FieldEquiv

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

local notation "B" => spectralIntegerRing K L
local notation "C" => spectralIntegerRing K M

/-- Field isomorphisms preserve the canonical ramification index. -/
theorem spectral_ramificationIdx_algEquiv (e : L ≃ₐ[K] M) :
    (IsLocalRing.maximalIdeal C).ramificationIdx 𝒪[K] =
      (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] := by
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪[K]
  apply ENat.natCast_inj.mp
  rw [ramificationIdx_eq_addVal_uniformizer 𝒪[K] C hπ,
    ramificationIdx_eq_addVal_uniformizer 𝒪[K] B hπ,
    ← (spectralIntegerRingEquiv K e).commutes π, spectralIntegerRingEquiv_addVal]

variable [PerfectField 𝓀[K]]

/-- Field isomorphisms preserve the order of the different ideal. -/
theorem spectral_different_order_algEquiv (e : L ≃ₐ[K] M) :
    emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal 𝒪[K] C) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B) := by
  let f := spectralIntegerRingEquiv K e
  obtain ⟨θ, hθ⟩ := extensionValuationSubring_exists_generator K L (spectralValuation K L)
  have hθ' : Algebra.adjoin 𝒪[K] {f θ} = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y ∈ Algebra.adjoin 𝒪[K] {θ} := by rw [hθ]; trivial
    have hm : f y ∈ (Algebra.adjoin 𝒪[K] {θ}).map f.toAlgHom :=
      Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom] using hm
  rw [differentIdeal_eq_span_derivative_of_adjoin_eq_top 𝒪[K] C K M hθ',
    differentIdeal_eq_span_derivative_of_adjoin_eq_top 𝒪[K] B K L hθ,
    maximalIdeal_emultiplicity_span, maximalIdeal_emultiplicity_span,
    minpoly.algEquiv_eq f θ]
  have hf : aeval (f θ) (minpoly 𝒪[K] θ).derivative =
      f (aeval θ (minpoly 𝒪[K] θ).derivative) := by
    exact Polynomial.aeval_algHom_apply f θ _
  rw [hf]
  exact addVal_ringEquiv f.toRingEquiv _

end FieldEquiv

section ChosenValuation

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w]

local notation "B" => spectralIntegerRing K L

/-- Replacing the spectral valuation by any compatible valuation
preserves the canonical ramification index on the field. -/
theorem extensionValuationSubring_ramificationIdx_eq_spectral :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[K] =
      (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  let f := IsIntegralClosure.equiv 𝒪[K] B L w.valuationSubring
  obtain ⟨π, hπ⟩ := exists_irreducible 𝒪[K]
  apply ENat.natCast_inj.mp
  rw [ramificationIdx_eq_addVal_uniformizer 𝒪[K] w.valuationSubring hπ,
    ramificationIdx_eq_addVal_uniformizer 𝒪[K] B hπ, ← f.commutes π]
  exact addVal_ringEquiv f.toRingEquiv _

variable [PerfectField 𝓀[K]]

/-- The order of the different is independent of the chosen
compatible valuation on the finite separable extension. -/
theorem extensionValuationSubring_different_order_eq_spectral :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
        (differentIdeal 𝒪[K] w.valuationSubring) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B) := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  let f := IsIntegralClosure.equiv 𝒪[K] B L w.valuationSubring
  obtain ⟨θ, hθ⟩ := extensionValuationSubring_exists_generator K L (spectralValuation K L)
  have hθ' : Algebra.adjoin 𝒪[K] {f θ} = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y ∈ Algebra.adjoin 𝒪[K] {θ} := by rw [hθ]; trivial
    have hm : f y ∈ (Algebra.adjoin 𝒪[K] {θ}).map f.toAlgHom :=
      Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom] using hm
  rw [differentIdeal_eq_span_derivative_of_adjoin_eq_top 𝒪[K] w.valuationSubring K L hθ',
    differentIdeal_eq_span_derivative_of_adjoin_eq_top 𝒪[K] B K L hθ,
    maximalIdeal_emultiplicity_span, maximalIdeal_emultiplicity_span,
    minpoly.algEquiv_eq f θ, Polynomial.aeval_algHom_apply]
  exact addVal_ringEquiv f.toRingEquiv _

end ChosenValuation

section FiniteOverfield

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "B" => spectralIntegerRing K M
local notation "C" => spectralIntegerRing K L

/-- The intrinsic APF index and different of any totally ramified
prime-degree intermediate field have the same single finite break. -/
theorem intermediate_apfIndex_prime_degree_different_profile
    (hp : (Module.finrank K M).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K M) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K M u = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) := by
  let w := (spectralValuation K L).comap (algebraMap M L)
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have he' : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx 𝒪[K] =
      Module.finrank K M := by
    rw [extensionValuationSubring_ramificationIdx_eq_spectral K M w, he]
  obtain ⟨b, hb, hprofile, hd⟩ :=
    intermediate_spectral_prime_degree_different_profile K L M hp he'
  have hf : Module.finrank (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
    have h := local_ramificationIdx_mul_residueDegree_eq_finrank 𝒪[K] w.valuationSubring K M
    rw [he'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by simpa only [mul_one] using h)
  have hzero : (M.fixingSubgroup ⊔
      lowerRamificationGroup (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal C) 0).index = 1 := by
    rw [intermediate_spectral_zeroOrbitIndex_eq_residueDegree K L M, hf]
  refine ⟨b, hb, ?_, ?_⟩
  · intro u hu
    rw [← hprofile u hu, upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex
      (R := C) (L ≃ₐ[K] L) M.fixingSubgroup hu, hzero, one_mul,
      apfIndex_eq_subgroupRelIndex_of_finiteGalois K L M hu,
      upperRamificationGroup_zero, lowerRamificationGroup_zero]
  · have hdiff := extensionValuationSubring_different_order_eq_spectral K M w
    change emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
      (differentIdeal 𝒪[K] w.valuationSubring) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B) at hdiff
    rw [hdiff] at hd
    exact hd

end FiniteOverfield

section AbstractExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "B" => spectralIntegerRing K L

/-- An arbitrary finite separable, totally ramified extension of prime
degree has one intrinsic APF break, determined by its different.
The extension need not be normal. -/
theorem apfIndex_prime_degree_different_profile
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K L : ℝ) - 1) * (b + 1) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E := IntermediateField.normalClosure K L (SeparableClosure K)
  let i : L →ₐ[K] E :=
    j.codRestrict E.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let M := i.fieldRange
  let e : L ≃ₐ[K] M := i.equivFieldRange
  let : FiniteDimensional K M := Module.Finite.equiv e.toLinearEquiv
  have hn : Module.finrank K M = Module.finrank K L := e.toLinearEquiv.finrank_eq.symm
  have heM : (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx 𝒪[K] =
      Module.finrank K M := by
    rw [spectral_ramificationIdx_algEquiv K e, he, hn]
  obtain ⟨b, hb, hprofile, hd⟩ :=
    intermediate_apfIndex_prime_degree_different_profile K E M (hn ▸ hp) heM
  refine ⟨b, hb, ?_, ?_⟩
  · intro u hu
    rw [apfIndex_algEquiv K L e, hprofile u hu, hn]
  · rw [spectral_different_order_algEquiv K e, hn] at hd
    exact hd

end AbstractExtension

section OneBreakFunctions

open MeasureTheory

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

/-- Integrating an one-break APF index gives its affine formulas
on both sides of the break, including the prescribed negative continuation. -/
theorem apfPsi_eq_of_index_profile {b : ℝ} (hb : 0 ≤ b)
    (hprofile : ∀ u : ℝ, 0 ≤ u →
      apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) (u : ℝ) :
    apfPsi K L u = if u ≤ b then u else b + (Module.finrank K L : ℝ) * (u - b) := by
  have hlow (v : ℝ) (hv : v ≤ b) : apfPsi K L v = v := by
    by_cases hv₀ : v ≤ 0
    · exact apfPsi_of_nonpos K L hv₀
    · rw [apfPsi_eq_integral_index K L (le_of_not_ge hv₀)]
      have heq : (∫ x in (0 : ℝ)..v, (apfIndex K L x : ℝ)) =
          ∫ _ in (0 : ℝ)..v, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (le_of_not_ge hv₀)]
        intro x hx
        dsimp only
        rw [hprofile x hx.1, ite_eq_left (hx.2.trans hv), Nat.cast_one]
      rw [heq]
      simp
  by_cases hu : u ≤ b
  · rw [ite_eq_left hu, hlow u hu]
  · have hbu : b < u := lt_of_not_ge hu
    have hint : (∫ x in b..u, apfHerbrandSlope K L x) =
        (u - b) * (Module.finrank K L : ℝ) := by
      calc
        _ = ∫ _ in b..u, (Module.finrank K L : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hbu.le
          intro x hx
          rw [apfHerbrandSlope, max_eq_left (hb.trans hx.1.le),
            hprofile x (hb.trans hx.1.le), ite_eq_right (not_le.mpr hx.1)]
        _ = _ := by simp
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 b)
      (IsAPF.intervalIntegrable_apfHerbrandSlope K L b u)
    change apfPsi K L b + _ = apfPsi K L u at hadd
    rw [hlow b le_rfl, hint] at hadd
    rw [ite_eq_right hu, ← hadd, mul_comm]

/-- Inverting the one-break Herbrand function gives the intrinsic
forward change of parameter, for every real argument. -/
theorem apfPhi_eq_of_index_profile {b : ℝ} (hb : 0 ≤ b)
    (hprofile : ∀ u : ℝ, 0 ≤ u →
      apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) (v : ℝ) :
    apfPhi K L v =
      if v ≤ b then v else b + (v - b) / (Module.finrank K L : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank K L :=
    Nat.cast_pos.mpr (Module.finrank_pos : 0 < Module.finrank K L)
  apply (IsAPF.strictMono_apfPsi K L).injective
  rw [apfPsi_apfPhi]
  by_cases hv : v ≤ b
  · rw [ite_eq_left hv, apfPsi_eq_of_index_profile K L hb hprofile, ite_eq_left hv]
  · have hvb : b < v := lt_of_not_ge hv
    have hy : b < b + (v - b) / (Module.finrank K L : ℝ) :=
      lt_add_of_pos_right b (div_pos (sub_pos.mpr hvb) hn)
    rw [ite_eq_right hv, apfPsi_eq_of_index_profile K L hb hprofile,
      ite_eq_right (not_le.mpr hy)]
    field_simp
    ring

end OneBreakFunctions

section PrimeDegreeFunctions

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "B" => spectralIntegerRing K L

/-- The different determines the full intrinsic one-break APF
profile of an arbitrary totally ramified separable prime-degree extension. -/
theorem apf_prime_degree_different_profile
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) ∧
      (∀ u : ℝ, apfPsi K L u =
        if u ≤ b then u else b + (Module.finrank K L : ℝ) * (u - b)) ∧
      (∀ v : ℝ, apfPhi K L v =
        if v ≤ b then v else b + (v - b) / (Module.finrank K L : ℝ)) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K L : ℝ) - 1) * (b + 1) := by
  obtain ⟨b, hb, hprofile, hd⟩ := apfIndex_prime_degree_different_profile K L hp he
  exact ⟨b, hb, hprofile, apfPsi_eq_of_index_profile K L hb hprofile,
    apfPhi_eq_of_index_profile K L hb hprofile, hd⟩

/-- An explicit break read directly from the different gives
the intrinsic APF index, including the right endpoint. -/
theorem apfIndex_prime_degree_eq_different
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K L) :
    let b := ((emultiplicity (IsLocalRing.maximalIdeal B)
        (differentIdeal 𝒪[K] B)).toNat : ℝ) / ((Module.finrank K L : ℝ) - 1) - 1
    0 ≤ b ∧ ∀ u : ℝ, 0 ≤ u →
      apfIndex K L u = if u ≤ b then 1 else Module.finrank K L := by
  obtain ⟨b, hb, hprofile, hd⟩ := apfIndex_prime_degree_different_profile K L hp he
  have hn : (Module.finrank K L : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hp.two_le
    linarith
  have hbreak : ((emultiplicity (IsLocalRing.maximalIdeal B)
      (differentIdeal 𝒪[K] B)).toNat : ℝ) / ((Module.finrank K L : ℝ) - 1) - 1 = b := by
    rw [hd, mul_div_cancel_left₀ (b + 1) hn]
    ring
  dsimp only
  rw [hbreak]
  exact ⟨hb, hprofile⟩

end PrimeDegreeFunctions

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField 𝓀[K]]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
variable (M : IntermediateField K E)

local notation "H" => M.fixingSubgroup
local notation "U" => upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E)

/-- The finite upper orbit index retains the zero-index residue factor. -/
theorem finite_upperOrbitIndex_eq_zeroIndex_mul_apfIndex {u : ℝ} (hu : 0 ≤ u) :
    (H ⊔ U u).index = (H ⊔ U 0).index * apfIndex K M u := by
  rw [apfIndex_eq_subgroupRelIndex K E M hu]
  simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
    upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex
      (R := spectralIntegerRing K E) (E ≃ₐ[K] E) H hu

local notation "B" => Valuation.valuationSubring (Valuation.comap (algebraMap M E)
    (spectralValuation K E))

/-- The different determines the intrinsic APF profile of every
prime-degree totally ramified intermediate field; normality is not required. -/
theorem apfIndex_prime_degree_different_profile_of_finiteGaloisIntermediateField
    (hp : (Module.finrank K M).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K M) :
    letI := intermediate_spectral_isDiscreteValuationRing K E M
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K M u = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) := by
  have := intermediate_spectral_isDiscreteValuationRing K E M
  have hfinite : ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → (H ⊔ U u).index = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) :=
    intermediate_spectral_prime_degree_different_profile K E M hp he
  obtain ⟨b, hb, hprofile, hd⟩ := hfinite
  have hz : (H ⊔ U 0).index = 1 := by
    simpa only [ite_eq_left hb] using hprofile 0 le_rfl
  refine ⟨b, hb, ?_, hd⟩
  intro u hu
  have hfactor := finite_upperOrbitIndex_eq_zeroIndex_mul_apfIndex K E M hu
  rw [hz, one_mul] at hfactor
  rw [← hfactor]
  exact hprofile u hu

end FontaineWintenberger

namespace FontaineWintenberger

noncomputable section

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "OL" => spectralIntegerRing K L
local notation "GL" => L ≃ₐ[K] L

variable [PerfectField 𝓀[K]]

/-- The prime-degree norm estimate with the public APF bound;
the positive denominator is cleared to retain infinite valuations faithfully. -/
theorem spectralIntegerRing_prime_degree_norm_estimate
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K] = Module.finrank K L) :
    ∃ t : ℕ, apfRamificationBound K L = ((t : ℝ) : EReal) ∧
      ∀ α β : OL, (((Module.finrank K L - 1) * t : ℕ) : ℕ∞) ≤
        (Module.finrank K L : ℕ∞) * IsDiscreteValuationRing.addVal 𝒪[K]
          (Algebra.intNorm 𝒪[K] OL (α + β) - Algebra.intNorm 𝒪[K] OL α -
            Algebra.intNorm 𝒪[K] OL β) := by
  obtain ⟨t, _ht, hbound, _hdiff, _htrace, hval⟩ :=
    spectralIntegerRing_prime_degree_ramification K L hp he
  refine ⟨t, hbound, fun α β => ?_⟩
  obtain ⟨z, hz⟩ := spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace K L hp α β
  rw [hz]
  exact hval z

end Spectral

end

end FontaineWintenberger
