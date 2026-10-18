/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteGaloisOverfield
public import FontaineWintenberger.Ramification.OrbitDifferent
public import FontaineWintenberger.LocalField.SpectralMaps
public import FontaineWintenberger.APF.CofinalBase

/-!
# Intrinsic ramification of prime-degree extensions

The actual different and total ramification determine the unique finite
upper break of an arbitrary separable prime-degree extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open IsDiscreteValuationRing Polynomial

section FieldEquiv

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L
local notation "C" => spectralIntegerRing K M

/-- Field isomorphisms preserve the actual canonical ramification index. -/
theorem spectral_ramificationIdx_algEquiv (e : L ≃ₐ[K] M) :
    (IsLocalRing.maximalIdeal C).ramificationIdx A =
      (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  apply ENat.natCast_inj.mp
  rw [ramificationIdx_eq_addVal_uniformizer A C hπ,
    ramificationIdx_eq_addVal_uniformizer A B hπ,
    ← (spectralIntegerRingEquiv K e).commutes π, spectralIntegerRingEquiv_addVal]

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

/-- Field isomorphisms preserve the order of the actual different ideal. -/
theorem spectral_different_order_algEquiv (e : L ≃ₐ[K] M) :
    emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) := by
  let f := spectralIntegerRingEquiv K e
  obtain ⟨θ, hθ⟩ := extensionValuationSubring_exists_generator K L (spectralValuation K L)
  have hθ' : Algebra.adjoin A {f θ} = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y ∈ Algebra.adjoin A {θ} := by rw [hθ]; trivial
    have hm : f y ∈ (Algebra.adjoin A {θ}).map f.toAlgHom :=
      Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom] using hm
  rw [differentIdeal_eq_span_derivative_of_adjoin_eq_top A C K M hθ',
    differentIdeal_eq_span_derivative_of_adjoin_eq_top A B K L hθ,
    maximalIdeal_emultiplicity_span, maximalIdeal_emultiplicity_span,
    minpoly.algEquiv_eq f θ]
  have hf : aeval (f θ) (minpoly A θ).derivative =
      f (aeval θ (minpoly A θ).derivative) := by
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

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L

/-- Replacing the spectral valuation by any compatible actual valuation
preserves the canonical ramification index on the same original field. -/
theorem extensionValuationSubring_ramificationIdx_eq_spectral :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx A =
      (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  let f := IsIntegralClosure.equiv A B L w.valuationSubring
  obtain ⟨π, hπ⟩ := exists_irreducible A
  apply ENat.natCast_inj.mp
  rw [ramificationIdx_eq_addVal_uniformizer A w.valuationSubring hπ,
    ramificationIdx_eq_addVal_uniformizer A B hπ, ← f.commutes π]
  exact addVal_ringEquiv f.toRingEquiv _

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

/-- The order of the actual different is independent of the chosen
compatible valuation on the same original finite separable extension. -/
theorem extensionValuationSubring_different_order_eq_spectral :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    emultiplicity (IsLocalRing.maximalIdeal w.valuationSubring)
        (differentIdeal A w.valuationSubring) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  let f := IsIntegralClosure.equiv A B L w.valuationSubring
  obtain ⟨θ, hθ⟩ := extensionValuationSubring_exists_generator K L (spectralValuation K L)
  have hθ' : Algebra.adjoin A {f θ} = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y ∈ Algebra.adjoin A {θ} := by rw [hθ]; trivial
    have hm : f y ∈ (Algebra.adjoin A {θ}).map f.toAlgHom :=
      Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom] using hm
  rw [differentIdeal_eq_span_derivative_of_adjoin_eq_top A w.valuationSubring K L hθ',
    differentIdeal_eq_span_derivative_of_adjoin_eq_top A B K L hθ,
    maximalIdeal_emultiplicity_span, maximalIdeal_emultiplicity_span,
    minpoly.algEquiv_eq f θ, Polynomial.aeval_algHom_apply]
  exact addVal_ringEquiv f.toRingEquiv _

end ChosenValuation

section FiniteOverfield

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K M
local notation "C" => spectralIntegerRing K L

/-- The intrinsic APF index and actual different of any totally ramified
prime-degree intermediate field have the same single finite break. -/
theorem intermediate_apfIndex_prime_degree_different_profile
    (hp : (Module.finrank K M).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K M) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K M u = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) := by
  let w := (spectralValuation K L).comap (algebraMap M L)
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have he' : (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx A =
      Module.finrank K M := by
    rw [extensionValuationSubring_ramificationIdx_eq_spectral K M w, he]
  obtain ⟨b, hb, hprofile, hd⟩ :=
    intermediate_spectral_prime_degree_different_profile K L M hp he'
  have hf : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField w.valuationSubring) = 1 := by
    have h := local_ramificationIdx_mul_residueDegree_eq_finrank A w.valuationSubring K M
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
      (differentIdeal A w.valuationSubring) =
      emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) at hdiff
    rw [hdiff] at hd
    exact hd

end FiniteOverfield

section AbstractExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L

/-- An arbitrary finite separable, totally ramified extension of prime
degree has one intrinsic APF break, determined by its actual different.
The original extension need not be normal. -/
theorem apfIndex_prime_degree_different_profile
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((Module.finrank K L : ℝ) - 1) * (b + 1) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E := IntermediateField.normalClosure K L (SeparableClosure K)
  let i : L →ₐ[K] E :=
    j.codRestrict E.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let M := i.fieldRange
  let e : L ≃ₐ[K] M := i.equivFieldRange
  let : FiniteDimensional K M := Module.Finite.equiv e.toLinearEquiv
  have hn : Module.finrank K M = Module.finrank K L := e.toLinearEquiv.finrank_eq.symm
  have heM : (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx A =
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

/-- Integrating an actual one-break APF index gives its affine formulas
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
      (IsAPF.intervalIntegrable_apfHerbrandSlope K L (isAPF_of_finite K L) 0 b)
      (IsAPF.intervalIntegrable_apfHerbrandSlope K L (isAPF_of_finite K L) b u)
    change apfPsi K L b + _ = apfPsi K L u at hadd
    rw [hlow b le_rfl, hint] at hadd
    rw [ite_eq_right hu, ← hadd, mul_comm]

/-- Inverting the actual one-break Herbrand function gives the intrinsic
forward change of parameter, for every real argument. -/
theorem apfPhi_eq_of_index_profile {b : ℝ} (hb : 0 ≤ b)
    (hprofile : ∀ u : ℝ, 0 ≤ u →
      apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) (v : ℝ) :
    apfPhi K L (isAPF_of_finite K L) v =
      if v ≤ b then v else b + (v - b) / (Module.finrank K L : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank K L :=
    Nat.cast_pos.mpr (Module.finrank_pos : 0 < Module.finrank K L)
  apply (IsAPF.strictMono_apfPsi K L (isAPF_of_finite K L)).injective
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
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "A" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L

/-- The actual different determines the full intrinsic one-break APF
profile of an arbitrary totally ramified separable prime-degree extension. -/
theorem apf_prime_degree_different_profile
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → apfIndex K L u = if u ≤ b then 1 else Module.finrank K L) ∧
      (∀ u : ℝ, apfPsi K L u =
        if u ≤ b then u else b + (Module.finrank K L : ℝ) * (u - b)) ∧
      (∀ v : ℝ, apfPhi K L (isAPF_of_finite K L) v =
        if v ≤ b then v else b + (v - b) / (Module.finrank K L : ℝ)) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((Module.finrank K L : ℝ) - 1) * (b + 1) := by
  obtain ⟨b, hb, hprofile, hd⟩ := apfIndex_prime_degree_different_profile K L hp he
  exact ⟨b, hb, hprofile, apfPsi_eq_of_index_profile K L hb hprofile,
    apfPhi_eq_of_index_profile K L hb hprofile, hd⟩

/-- An explicit break read directly from the actual different gives
the actual intrinsic APF index, including the right endpoint. -/
theorem apfIndex_prime_degree_eq_different
    (hp : (Module.finrank K L).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K L) :
    let b := ((emultiplicity (IsLocalRing.maximalIdeal B)
        (differentIdeal A B)).toNat : ℝ) / ((Module.finrank K L : ℝ) - 1) - 1
    0 ≤ b ∧ ∀ u : ℝ, 0 ≤ u →
      apfIndex K L u = if u ≤ b then 1 else Module.finrank K L := by
  obtain ⟨b, hb, hprofile, hd⟩ := apfIndex_prime_degree_different_profile K L hp he
  have hn : (Module.finrank K L : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hp.two_le
    linarith
  have hbreak : ((emultiplicity (IsLocalRing.maximalIdeal B)
      (differentIdeal A B)).toNat : ℝ) / ((Module.finrank K L : ℝ) - 1) - 1 = b := by
    rw [hd, mul_div_cancel_left₀ (b + 1) hn]
    ring
  dsimp only
  rw [hbreak]
  exact ⟨hb, hprofile⟩

end PrimeDegreeFunctions

end FontaineWintenberger
