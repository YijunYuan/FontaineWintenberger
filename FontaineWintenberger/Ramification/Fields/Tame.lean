/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.Tame
public import FontaineWintenberger.Ramification.Lower.Wild
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Herbrand.Inverse
public import FontaineWintenberger.Ramification.Upper.FixedField

/-!
# The field fixed by wild inertia

Positive upper groups lie in the first lower group. Its fixed field
has trivial positive upper groups and prime-to-p ramification index.

## Main results

* `upperRamificationGroup_le_lower_one`: Every positive upper group lies in the first lower group.
* `lowerRamificationGroup_subgroup_zero_eq_top`: Restricting the inertia action to any subgroup of
  inertia gives full inertia for that restricted action.
* `inverseHerbrandFunction_eq_card_inertia_mul`: Trivial positive upper groups give the linear
  inverse Herbrand function, by its proved integral formula.
* `wild_fixedField_top_ramificationIdx_eq_finrank`: The restricted integers witness total
  ramification above the wild fixed field; the relative field degree is the fixed-field degree.
* `wild_fixedField_upper_eq_bot`: The wild fixed field has trivial positive upper groups.
* `wild_fixedField_ramificationIdx_eq_relIndex`: Its ramification index is the index of wild inertia
  in inertia.
* `wild_fixedField_inverseHerbrandFunction`: The inverse Herbrand function of the tame field is
  multiplication by its ramification index on the nonnegative half-line.
* `wild_fixedField_ramificationIdx_coprime`: The tame field has prime-to-p ramification index even
  when its unramified degree has a p-part.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

section Groups

variable (G : Type*) {B : Type*} [Group G] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [MulSemiringAction G B] [Finite G]

/-- Every positive upper group lies in the first lower group. -/
theorem upperRamificationGroup_le_lower_one {u : ℝ} (hu : 0 < u) :
    upperRamificationGroup (R := B) G u ≤
      lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1 := by
  have hpos : 0 < inverseHerbrandFunction (R := B) G u := by
    have h := strictMonoOn_inverseHerbrandFunction (R := B) G
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
    simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl] using h
  exact lowerRamificationGroup_antitone G (IsLocalRing.maximalIdeal B)
    (Int.one_le_ceil_iff.mpr hpos)

omit [Finite G] in
/-- Restricting the inertia action to any subgroup of inertia gives
full inertia for that restricted action. -/
theorem lowerRamificationGroup_subgroup_zero_eq_top
    (H : Subgroup G) (hH : H ≤ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) :
    lowerRamificationGroup H (IsLocalRing.maximalIdeal B) 0 = ⊤ := by
  rw [← lowerRamificationGroup_subgroupOf, Subgroup.subgroupOf_eq_top]
  exact hH

/-- Trivial positive upper groups give the linear inverse
Herbrand function, by its proved integral formula. -/
theorem inverseHerbrandFunction_eq_card_inertia_mul [FaithfulSMul G B]
    (hU : ∀ u : ℝ, 0 < u → upperRamificationGroup (R := B) G u = ⊥)
    {u : ℝ} (hu : 0 ≤ u) :
    inverseHerbrandFunction (R := B) G u =
      (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) : ℝ) * u := by
  rw [inverseHerbrandFunction_eq_integral_div G hu]
  calc
    _ = ∫ _ in (0 : ℝ)..u,
        (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun v hv => by
        rw [Set.uIoc_of_le hu] at hv
        rw [hU v hv.1, Subgroup.card_bot, Nat.cast_one, div_one]
    _ = _ := by simp [intervalIntegral.integral_const, mul_comm]

end Groups

section Fields

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField 𝓀[K]]

local notation "G" => L ≃ₐ[K] L
local notation "B" => spectralIntegerRing K L
local notation "D" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0
local notation "P" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1
local notation "F₁" => IntermediateField.fixedField P

/-- The restricted integers witness total ramification above the wild
fixed field; the relative field degree is the fixed-field degree. -/
theorem wild_fixedField_top_ramificationIdx_eq_finrank :
    (IsLocalRing.maximalIdeal B).ramificationIdx
      ((spectralValuation K L).comap (algebraMap F₁ L)).valuationSubring =
        Module.finrank F₁ L := by
  rw [← fixedField_card_inertia K L P,
    lowerRamificationGroup_subgroup_zero_eq_top G P
      (lowerRamificationGroup_antitone G (IsLocalRing.maximalIdeal B) (by norm_num : (0 : ℤ) ≤ 1)),
    Subgroup.card_top, IntermediateField.finrank_fixedField_eq_card]

/-- The wild fixed field has trivial positive upper groups. -/
theorem wild_fixedField_upper_eq_bot {u : ℝ} (hu : 0 < u) :
    upperRamificationGroup (R := spectralIntegerRing K F₁) (F₁ ≃ₐ[K] F₁) u = ⊥ := by
  rw [← restrictNormalHom_map_upperRamificationGroup_tower K F₁ L u (by linarith)]
  rw [Subgroup.map_eq_bot_iff, IntermediateField.restrictNormalHom_ker,
    IntermediateField.fixingSubgroup_fixedField]
  exact upperRamificationGroup_le_lower_one G hu

/-- Its ramification index is the index of wild inertia in inertia. -/
theorem wild_fixedField_ramificationIdx_eq_relIndex :
    (IsLocalRing.maximalIdeal (spectralIntegerRing K F₁)).ramificationIdx
      𝒪[K] = (P).relIndex D := by
  let ρ : G →* (F₁ ≃ₐ[K] F₁) := AlgEquiv.restrictNormalHom F₁
  have hker : ρ.ker = P := by
    rw [show ρ = AlgEquiv.restrictNormalHom F₁ from rfl,
      IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hmap : (D).map ρ =
      lowerRamificationGroup (F₁ ≃ₐ[K] F₁)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K F₁)) 0 := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero, ρ] using
      restrictNormalHom_map_upperRamificationGroup_tower K F₁ L 0 (by norm_num)
  rw [← spectralIntegerRing_card_lower_zero K F₁, ← hmap, ← Subgroup.relIndex_ker, hker]

/-- The inverse Herbrand function of the tame field is multiplication
by its ramification index on the nonnegative half-line. -/
theorem wild_fixedField_inverseHerbrandFunction {u : ℝ} (hu : 0 ≤ u) :
    inverseHerbrandFunction (R := spectralIntegerRing K F₁) (F₁ ≃ₐ[K] F₁) u =
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K F₁)).ramificationIdx
        𝒪[K] : ℝ) * u := by
  rw [inverseHerbrandFunction_eq_card_inertia_mul (F₁ ≃ₐ[K] F₁)
    (fun _ hu => wild_fixedField_upper_eq_bot K L hu) hu,
    spectralIntegerRing_card_lower_zero K F₁]

/-- The tame field has prime-to-p ramification index even when its
unramified degree has a p-part. -/
theorem wild_fixedField_ramificationIdx_coprime (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] :
    Nat.Coprime p
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K F₁)).ramificationIdx
        𝒪[K]) := by
  let : PerfectField (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.perfectField 𝓀[K]
  rw [wild_fixedField_ramificationIdx_eq_relIndex K L]
  change Nat.Coprime p ((P).subgroupOf D).index
  rw [Subgroup.index_eq_card]
  exact coprime_card_tameInertiaQuotient G p

omit [PerfectField 𝓀[K]] in
/-- The Galois group above the wild fixed field is a p-group. -/
theorem wild_fixedField_isPGroup (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] : IsPGroup p (L ≃ₐ[F₁] L) := by
  let e : (P) ≃* (L ≃ₐ[F₁] L) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField P).symm).trans
      (IntermediateField.fixingSubgroupEquiv F₁)
  exact (lowerRamificationGroup_one_isPGroup G p).of_equiv e

end Fields

end FontaineWintenberger
