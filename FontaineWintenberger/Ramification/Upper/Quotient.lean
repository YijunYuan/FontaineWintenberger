/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.CosetMax
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Herbrand's quotient theorem

## Herbrand's lower quotient theorem

Restriction sends the real lower groups onto the lower groups of
the fixed-field integers at the relative Herbrand parameter.

## Herbrand functions in a normal fixed-field tower

The lower quotient theorem and subgroup compatibility give exact finite
cardinality identities. These supply the slopes in Herbrand transitivity.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal

section GroupAction

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R]

/-- Finite intrinsic order gives the source's weak real lower-index bound. -/
theorem mem_lowerRamificationGroupReal_iff_le_toNat {g : G}
    (hg : ramificationOrder (R := R) G g ≠ ⊤) (t : ℝ) :
    g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t ↔
      t ≤ ((ramificationOrder (R := R) G g).toNat : ℝ) - 1 := by
  rw [mem_lowerRamificationGroupReal_iff_le_order, ← ENat.natCast_toNat hg,
    ENat.toENNReal_coe, ENNReal.ofReal_le_natCast]
  simp only [ENat.toNat_natCast]
  constructor <;> intro h <;> linarith

end GroupAction

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
variable [PerfectField 𝓀[K]]

local notation "G₀" => L ≃ₐ[K] L
local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- Herbrand's lower quotient formula, for normal fixed-field restriction. -/
theorem fixedField_map_lowerRamificationGroupReal (t : ℝ) (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    (lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t).map ρ =
      lowerRamificationGroupReal D₀ (IsLocalRing.maximalIdeal A₀)
        (herbrandFunction (R := B₀) H t) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  ext τ
  by_cases hτ : τ = 1
  · subst τ
    simp
  obtain ⟨s, hs, hsfinite, hmax, hformula⟩ :=
    exists_fixedField_order_eq_herbrand K L H τ hτ
  have hτfinite : ramificationOrder (R := A₀) D₀ τ ≠ ⊤ :=
    (ramificationOrder_eq_top_iff D₀ τ).not.mpr hτ
  have hm : -1 ≤ ((ramificationOrder (R := B₀) G₀ s).toNat : ℝ) - 1 := by
    have : (0 : ℝ) ≤ (ramificationOrder (R := B₀) G₀ s).toNat := Nat.cast_nonneg _
    linarith
  have himage : τ ∈ (lowerRamificationGroupReal G₀
      (IsLocalRing.maximalIdeal B₀) t).map ρ ↔
      t ≤ ((ramificationOrder (R := B₀) G₀ s).toNat : ℝ) - 1 := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, hρr⟩
      have hbound := (mem_lowerRamificationGroupReal_iff_le_order G₀ t r).mp hr
      have hle := hbound.trans (ENat.toENNReal_mono (hmax r hρr))
      rw [← ENat.natCast_toNat hsfinite, ENat.toENNReal_coe,
        ENNReal.ofReal_le_natCast] at hle
      linarith
    · intro h
      exact ⟨s, (mem_lowerRamificationGroupReal_iff_le_toNat G₀ hsfinite t).mpr h, hs⟩
  rw [himage, mem_lowerRamificationGroupReal_iff_le_toNat D₀ hτfinite]
  change t ≤ ((ramificationOrder (R := B₀) G₀ s).toNat : ℝ) - 1 ↔
    herbrandFunction (R := B₀) H t ≤ (((A₀).ramificationOrder K τ).toNat : ℝ) - 1
  rw [hformula]
  exact ((strictMonoOn_herbrandFunction (R := B₀) H).le_iff_le ht hm).symm

/-- The same lower quotient formula through the canonical Galois quotient equivalence. -/
theorem fixedField_quotient_lowerRamificationGroupReal (t : ℝ) (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ((lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t).map
      (QuotientGroup.mk' H)).map (fixedFieldDecompositionQuotientEquiv K L H).toMonoidHom =
      lowerRamificationGroupReal D₀ (IsLocalRing.maximalIdeal A₀)
        (herbrandFunction (R := B₀) H t) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  rw [Subgroup.map_map]
  have hcomp : (fixedFieldDecompositionQuotientEquiv K L H).toMonoidHom.comp
      (QuotientGroup.mk' H) = ρ := by
    ext s
    rfl
  rw [hcomp, fixedField_map_lowerRamificationGroupReal K L H t ht]

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
variable [PerfectField 𝓀[K]]

local notation "G₀" => L ≃ₐ[K] L
local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- Exact cardinalities of lower groups under fixed-field restriction. -/
theorem fixedField_card_lowerRamificationGroupReal (t : ℝ) (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    Nat.card (lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t) =
      Nat.card (lowerRamificationGroupReal H (IsLocalRing.maximalIdeal B₀) t) *
        Nat.card (lowerRamificationGroupReal D₀ (IsLocalRing.maximalIdeal A₀)
          (herbrandFunction (R := B₀) H t)) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  let P := lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t
  have h := (ρ).ker.relIndex_mul_card P
  rw [Subgroup.relIndex_ker, fixedFieldDecompositionRestriction_ker,
    fixedField_map_lowerRamificationGroupReal K L H t ht] at h
  have hmem (g : H) :
      g ∈ lowerRamificationGroupReal H (IsLocalRing.maximalIdeal B₀) t ↔ g.1 ∈ P := by
    rw [← lowerRamificationGroupReal_subgroupOf G₀ (IsLocalRing.maximalIdeal B₀) t H]
    rfl
  let e : lowerRamificationGroupReal H (IsLocalRing.maximalIdeal B₀) t ≃ ↥(H ⊓ P) :=
    { toFun := fun g => ⟨g.1.1, ⟨g.1.2, (hmem g.1).mp g.2⟩⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem ⟨g.1, g.2.1⟩).mpr g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, mul_comm] at h
  exact h.symm

/-- The inertia cardinalities in the normal fixed-field tower multiply. -/
theorem fixedField_card_lowerRamificationGroup_zero :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    Nat.card (lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal B₀) 0) =
      Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) *
        Nat.card (lowerRamificationGroup D₀ (IsLocalRing.maximalIdeal A₀) 0) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  simpa [herbrandFunction, lowerRamificationGroupReal] using
    fixedField_card_lowerRamificationGroupReal K L H 0 (by norm_num)

/-- The chain-rule slope is the ambient lower-group cardinality ratio. -/
theorem fixedField_herbrand_slope_mul (t : ℝ) (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ((Nat.card (lowerRamificationGroupReal D₀ (IsLocalRing.maximalIdeal A₀)
        (herbrandFunction (R := B₀) H t)) : ℝ) /
        Nat.card (lowerRamificationGroup D₀ (IsLocalRing.maximalIdeal A₀) 0)) *
      ((Nat.card (lowerRamificationGroupReal H (IsLocalRing.maximalIdeal B₀) t) : ℝ) /
        Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0)) =
      (Nat.card (lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t) : ℝ) /
        Nat.card (lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal B₀) 0) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  rw [fixedField_card_lowerRamificationGroupReal K L H t ht,
    fixedField_card_lowerRamificationGroup_zero K L H]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The composite has the ambient Herbrand slope outside finitely many points. -/
theorem fixedField_exists_herbrand_comp_derivative_breaks :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ∃ S : Finset ℝ, ∀ t : ℝ, 0 < t → t ∉ S →
      HasDerivAt
        ((herbrandFunction (R := A₀) D₀) ∘ (herbrandFunction (R := B₀) H))
        ((Nat.card (lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) t) : ℝ) /
          Nat.card (lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal B₀) 0)) t := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  obtain ⟨S₁, hS₁⟩ := exists_herbrandFunction_finite_derivative_breaks (R := B₀) H
  obtain ⟨S₂, hS₂⟩ := exists_herbrandFunction_finite_derivative_breaks (R := A₀) D₀
  refine ⟨S₁ ∪ S₂.image (inverseHerbrandFunction (R := B₀) H), ?_⟩
  intro t ht hS
  have hnot₁ : t ∉ S₁ := fun h => hS (Finset.mem_union_left _ h)
  have hnot₂ : herbrandFunction (R := B₀) H t ∉ S₂ := by
    intro h
    apply hS
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨_, h,
      inverseHerbrandFunction_herbrandFunction H (by linarith)⟩
  have hpos : 0 < herbrandFunction (R := B₀) H t := by
    have h := strictMonoOn_herbrandFunction (R := B₀) H
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ t) ht
    simpa only [herbrandFunction_of_nonpos H le_rfl] using h
  have hderiv := (hS₂ _ hpos hnot₂).comp t (hS₁ t ht hnot₁)
  rw [fixedField_herbrand_slope_mul K L H t (by linarith)] at hderiv
  exact hderiv

/-- Herbrand transitivity, also for the identity extension below the half-line. -/
theorem fixedField_herbrandFunction_transitivity (t : ℝ) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    herbrandFunction (R := B₀) G₀ t =
      herbrandFunction (R := A₀) D₀ (herbrandFunction (R := B₀) H t) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  by_cases ht0 : t ≤ 0
  · rw [herbrandFunction_of_nonpos G₀ ht0, herbrandFunction_of_nonpos H ht0,
      herbrandFunction_of_nonpos D₀ ht0]
  obtain ⟨S, hS⟩ := fixedField_exists_herbrand_comp_derivative_breaks K L H
  have hcont : ContinuousOn
      ((herbrandFunction (R := A₀) D₀) ∘ (herbrandFunction (R := B₀) H))
      (Set.Icc 0 t) := by
    apply (continuousOn_herbrandFunction (R := A₀) D₀).comp
      ((continuousOn_herbrandFunction (R := B₀) H).mono (by
        intro x hx
        exact le_trans (by norm_num) hx.1))
    intro x hx
    exact herbrandFunction_mem_Ici H (by linarith [hx.1])
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    ((herbrandFunction (R := A₀) D₀) ∘ (herbrandFunction (R := B₀) H)) _
    (le_of_lt (lt_of_not_ge ht0)) S.countable_toSet hcont
    (fun x hx => hS x hx.1.1 hx.2)
    ((intervalIntegrable_card_lowerRamificationGroupReal (R := B₀) G₀ 0 t).div_const _)
  have hg : herbrandFunction (R := B₀) G₀ t =
      ∫ s in (0 : ℝ)..t,
        (Nat.card (lowerRamificationGroupReal G₀ (IsLocalRing.maximalIdeal B₀) s) : ℝ) /
          Nat.card (lowerRamificationGroup G₀ (IsLocalRing.maximalIdeal B₀) 0) := by
    rw [herbrandFunction, ite_eq_right ht0]
  rw [hg]
  simpa only [Function.comp_apply,
    herbrandFunction_of_nonpos H le_rfl, herbrandFunction_of_nonpos D₀ le_rfl,
    sub_zero] using h

/-- The inverse Herbrand functions compose in reverse tower order. -/
theorem fixedField_inverseHerbrandFunction_transitivity (u : ℝ) (hu : -1 ≤ u) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    inverseHerbrandFunction (R := B₀) G₀ u =
      inverseHerbrandFunction (R := B₀) H (inverseHerbrandFunction (R := A₀) D₀ u) := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  have hv := inverseHerbrandFunction_mem_Ici (R := A₀) D₀ u
  have hw := inverseHerbrandFunction_mem_Ici (R := B₀) H
    (inverseHerbrandFunction (R := A₀) D₀ u)
  have h := fixedField_herbrandFunction_transitivity K L H
    (inverseHerbrandFunction (R := B₀) H (inverseHerbrandFunction (R := A₀) D₀ u))
  rw [herbrandFunction_inverseHerbrandFunction H hv,
    herbrandFunction_inverseHerbrandFunction D₀ hu] at h
  have h' := congrArg (inverseHerbrandFunction (R := B₀) G₀) h
  rw [inverseHerbrandFunction_herbrandFunction G₀ hw] at h'
  exact h'.symm

end FontaineWintenberger
