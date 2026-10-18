/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.CosetMax

/-!
# Herbrand's lower quotient theorem

Restriction sends the actual real lower groups onto the lower groups of
the actual fixed-field integers at the relative Herbrand parameter.
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
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "G₀" => L ≃ₐ[K] L
local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- Herbrand's lower quotient formula, for actual normal fixed-field restriction. -/
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

/-- The same lower quotient formula through the canonical actual Galois quotient equivalence. -/
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
