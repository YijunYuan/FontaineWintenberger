/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.HerbrandQuotient

/-!
# Quotients by an actual lower ramification group

The relative Herbrand function is the identity up to the defining lower
index. Herbrand's actual fixed-field quotient theorem therefore gives
unchanged lower numbering there, and the quotient has a trivial tail.

Reference: Serre, *Local Fields*, Chapter IV, §1, corollary to Proposition 3.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal

section GroupAction

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- A subgroup contained in a lower group has its entire relative lower
group at every earlier real index. -/
theorem lowerRamificationGroupReal_subgroup_eq_top_of_le (I : Ideal R)
    (H : Subgroup G) {r : ℤ} (hH : H ≤ lowerRamificationGroup G I r)
    {t : ℝ} (ht : t ≤ r) : lowerRamificationGroupReal H I t = ⊤ := by
  apply top_unique
  intro h _
  change h.val ∈ lowerRamificationGroup G I ⌈t⌉
  exact lowerRamificationGroup_antitone G I (Int.ceil_le.mpr ht) (hH h.property)

variable [IsDomain R] [IsDiscreteValuationRing R] [Finite G]

/-- Containment in a nonnegative lower group makes the relative Herbrand
function exactly the identity throughout the earlier interval. -/
theorem herbrandFunction_eq_self_of_subgroup_le_lower (H : Subgroup G)
    {r : ℤ} (hr : 0 ≤ r)
    (hH : H ≤ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) r)
    {t : ℝ} (ht : -1 ≤ t) (htr : t ≤ r) :
    herbrandFunction (R := R) H t = t := by
  classical
  let := Fintype.ofFinite H
  have h0 : lowerRamificationGroup H (IsLocalRing.maximalIdeal R) 0 = ⊤ := by
    simpa only [lowerRamificationGroupReal_zero, lowerRamificationGroup_zero] using
      lowerRamificationGroupReal_subgroup_eq_top_of_le G (IsLocalRing.maximalIdeal R) H hH
        (t := 0) (by exact_mod_cast hr)
  have hc : Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal R) 0) =
      Nat.card H := by rw [h0, Subgroup.card_top]
  have hcap (h : H) : truncatedRamificationOrder (R := R) H h t = t + 1 := by
    have hm : h ∈ lowerRamificationGroupReal H (IsLocalRing.maximalIdeal R) t := by
      rw [lowerRamificationGroupReal_subgroup_eq_top_of_le G
        (IsLocalRing.maximalIdeal R) H hH htr]
      trivial
    have hv := (mem_lowerRamificationGroupReal_iff_le_order H t h).mp hm
    rw [truncatedRamificationOrder, min_eq_right hv,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ t + 1)]
  rw [herbrandFunction_eq_sum H ht, herbrandSum]
  simp_rw [hcap]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
  have hn : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

end GroupAction

section FixedField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (r : ℤ)

local notation "G" => L ≃ₐ[K] L
local notation "B" => spectralIntegerRing K L
local notation "H" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) r
local notation "F" => IntermediateField.fixedField H
local notation "A" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F L) (spectralValuation K L))
local notation "D" => ValuationSubring.decompositionSubgroup K A
local notation "ρ" => fixedFieldDecompositionRestriction K L H

/-- Original restriction preserves lower numbering up to the index of the
actual lower subgroup by which one takes the quotient. -/
theorem lowerFixedField_map_lowerRamificationGroupReal (hr : 0 ≤ r)
    {t : ℝ} (ht : -1 ≤ t) (htr : t ≤ r) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal B) t).map ρ =
      lowerRamificationGroupReal D (IsLocalRing.maximalIdeal A) t := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  have hφ : herbrandFunction (R := B) H t = t :=
    herbrandFunction_eq_self_of_subgroup_le_lower G H hr le_rfl ht htr
  simpa only [hφ] using fixedField_map_lowerRamificationGroupReal K L H t ht

/-- The actual fixed-field lower filtration is trivial from the defining
integer index onward, including that index and the case zero. -/
theorem lowerFixedField_lowerRamificationGroupReal_eq_bot (hr : 0 ≤ r)
    {t : ℝ} (hrt : (r : ℝ) ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    lowerRamificationGroupReal D (IsLocalRing.maximalIdeal A) t = ⊥ := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  have hzero : lowerRamificationGroupReal D (IsLocalRing.maximalIdeal A) (r : ℝ) = ⊥ := by
    rw [← lowerFixedField_map_lowerRamificationGroupReal K L r hr
      (by exact_mod_cast (show (-1 : ℤ) ≤ r by omega)) le_rfl,
      lowerRamificationGroupReal_intCast, Subgroup.map_eq_bot_iff,
      fixedFieldDecompositionRestriction_ker K L H]
  exact bot_unique ((lowerRamificationGroupReal_antitone D
    (IsLocalRing.maximalIdeal A) hrt).trans_eq hzero)

/-- With a lower group as kernel, unchanged numbering describes the actual
restriction image at every real index in the source domain. -/
theorem lowerFixedField_map_lowerRamificationGroupReal_all (hr : 0 ≤ r)
    {t : ℝ} (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal B) t).map ρ =
      lowerRamificationGroupReal D (IsLocalRing.maximalIdeal A) t := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  by_cases htr : t ≤ (r : ℝ)
  · exact lowerFixedField_map_lowerRamificationGroupReal K L r hr ht htr
  · have hrt : (r : ℝ) ≤ t := by linarith
    rw [lowerFixedField_lowerRamificationGroupReal_eq_bot K L r hr hrt,
      Subgroup.map_eq_bot_iff, fixedFieldDecompositionRestriction_ker K L H]
    simpa only [lowerRamificationGroupReal_intCast] using
      lowerRamificationGroupReal_antitone G (IsLocalRing.maximalIdeal B) hrt

/-- The literal canonical Galois quotient equivalence identifies the actual
image in `G/H` with the same-index original fixed-field lower group. -/
theorem lowerFixedField_quotient_lowerRamificationGroupReal (hr : 0 ≤ r)
    {t : ℝ} (ht : -1 ≤ t) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    ((lowerRamificationGroupReal G (IsLocalRing.maximalIdeal B) t).map
      (QuotientGroup.mk' H)).map (fixedFieldDecompositionQuotientEquiv K L H).toMonoidHom =
      lowerRamificationGroupReal D (IsLocalRing.maximalIdeal A) t := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  rw [Subgroup.map_map]
  have hcomp : (fixedFieldDecompositionQuotientEquiv K L H).toMonoidHom.comp
      (QuotientGroup.mk' H) = ρ := by
    ext s
    rfl
  rw [hcomp, lowerFixedField_map_lowerRamificationGroupReal_all K L r hr ht]

/-- In particular the original integer lower groups have exactly the
same-index images under actual fixed-field restriction. -/
theorem lowerFixedField_map_lowerRamificationGroup (hr : 0 ≤ r)
    {n : ℤ} (hn : -1 ≤ n) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n).map ρ =
      lowerRamificationGroup D (IsLocalRing.maximalIdeal A) n := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  simpa only [lowerRamificationGroupReal_intCast] using
    lowerFixedField_map_lowerRamificationGroupReal_all K L r hr
      (t := (n : ℝ)) (by exact_mod_cast hn)

/-- The same original integer filtration is trivial from the defining
integer onward, with the endpoint included. -/
theorem lowerFixedField_lowerRamificationGroup_eq_bot (hr : 0 ≤ r)
    {n : ℤ} (hrn : r ≤ n) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    lowerRamificationGroup D (IsLocalRing.maximalIdeal A) n = ⊥ := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  simpa only [lowerRamificationGroupReal_intCast] using
    lowerFixedField_lowerRamificationGroupReal_eq_bot K L r hr
      (t := (n : ℝ)) (by exact_mod_cast hrn)

end FixedField

end FontaineWintenberger
