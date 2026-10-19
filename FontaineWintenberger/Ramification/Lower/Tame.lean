/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Uniformizer
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.CharP.Reduced

/-!
# The tame inertia homomorphism

The unit ratio of an automorphism applied to an uniformizer gives a residue
unit. On inertia this is multiplicative, and its kernel is the first
lower ramification group.

## Main definitions

* `uniformizerRatio`: The unit by which a ring automorphism multiplies an uniformizer.
* `tameInertiaHom`: The tame inertia homomorphism to units of the residue field.
* `tameInertiaQuotientEquiv`: The tame quotient is the finite residue-unit image.

## Main results

* `residue_smul_eq_of_mem_lower_zero`: Inertia fixes every residue class.
* `tameInertiaHom_eq`: The tame residue homomorphism is independent of the chosen uniformizer.
* `uniformizer_mul_mem_pow_two`: An uniformizer multiple has the next ideal-power order exactly when
  its remaining factor has the preceding order.
* `ker_tameInertiaHom`: The residue-unit kernel is precisely the first lower group inside inertia.
* `isCyclic_tameInertiaQuotient`: Tame inertia is cyclic, even when the perfect residue field is
  infinite.
* `coprime_card_tameInertiaQuotient`: The order of the tame inertia quotient is prime to the residue
  characteristic.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

/-- The unit by which a ring automorphism multiplies an uniformizer. -/
def uniformizerRatio {π : B} (hπ : Irreducible π) (g : G) : Bˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible B hπ
    (hπ.map (MulSemiringAction.toRingEquiv G B g))).choose

theorem mul_uniformizerRatio {π : B} (hπ : Irreducible π) (g : G) :
    π * (uniformizerRatio G hπ g : B) = g • π :=
  (IsDiscreteValuationRing.associated_of_irreducible B hπ
    (hπ.map (MulSemiringAction.toRingEquiv G B g))).choose_spec

@[simp]
theorem uniformizerRatio_one {π : B} (hπ : Irreducible π) :
    uniformizerRatio G hπ 1 = 1 := by
  apply Units.ext
  apply mul_left_cancel₀ hπ.ne_zero
  simpa only [one_smul, Units.val_one, mul_one] using mul_uniformizerRatio G hπ 1

theorem coe_uniformizerRatio_mul {π : B} (hπ : Irreducible π) (g h : G) :
    (uniformizerRatio G hπ (g * h) : B) =
      (uniformizerRatio G hπ g : B) * (g • (uniformizerRatio G hπ h : B)) := by
  apply mul_left_cancel₀ hπ.ne_zero
  rw [mul_uniformizerRatio, mul_smul]
  calc
    g • (h • π) = g • (π * (uniformizerRatio G hπ h : B)) :=
      congrArg (fun x : B => g • x) (mul_uniformizerRatio G hπ h).symm
    _ = (g • π) * (g • (uniformizerRatio G hπ h : B)) := by
      exact map_mul (MulSemiringAction.toRingHom G B g) _ _
    _ = _ := by rw [← mul_uniformizerRatio G hπ g]; ring

/-- Inertia fixes every residue class. -/
theorem residue_smul_eq_of_mem_lower_zero {g : G}
    (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) (x : B) :
    IsLocalRing.residue B (g • x) = IsLocalRing.residue B x := by
  rw [lowerRamificationGroup_zero, Ideal.mem_inertia] at hg
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hg x)

/-- The tame inertia homomorphism to units of the residue field. -/
def tameInertiaHom {π : B} (hπ : Irreducible π) :
    lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0 →*
      (IsLocalRing.ResidueField B)ˣ where
  toFun g := Units.map (IsLocalRing.residue B).toMonoidHom (uniformizerRatio G hπ g)
  map_one' := by simp
  map_mul' g h := by
    apply Units.ext
    change IsLocalRing.residue B (uniformizerRatio G hπ ((g : G) * h) : B) =
      IsLocalRing.residue B (uniformizerRatio G hπ g : B) *
        IsLocalRing.residue B (uniformizerRatio G hπ h : B)
    rw [coe_uniformizerRatio_mul, map_mul, residue_smul_eq_of_mem_lower_zero G g.property]

/-- The tame residue homomorphism is independent of the chosen uniformizer. -/
theorem tameInertiaHom_eq {π π' : B} (hπ : Irreducible π) (hπ' : Irreducible π') :
    tameInertiaHom G hπ = tameInertiaHom G hπ' := by
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible B hπ hπ'
  apply MonoidHom.ext
  intro g
  have heq : (v : B) * (uniformizerRatio G hπ' g : B) =
      (uniformizerRatio G hπ g : B) * ((g : G) • (v : B)) := by
    apply mul_left_cancel₀ hπ.ne_zero
    calc
      _ = (π * (v : B)) * (uniformizerRatio G hπ' g : B) := (mul_assoc _ _ _).symm
      _ = π' * (uniformizerRatio G hπ' g : B) :=
        congrArg (fun x : B => x * (uniformizerRatio G hπ' g : B)) hv
      _ = (g : G) • π' := mul_uniformizerRatio G hπ' g
      _ = (g : G) • (π * (v : B)) := congrArg (fun x : B => (g : G) • x) hv.symm
      _ = ((g : G) • π) * ((g : G) • (v : B)) :=
        map_mul (MulSemiringAction.toRingHom G B g) _ _
      _ = _ := by rw [← mul_uniformizerRatio G hπ g]; ring
  have hres := congrArg (IsLocalRing.residue B) heq
  rw [map_mul, map_mul, residue_smul_eq_of_mem_lower_zero G g.property] at hres
  apply Units.ext
  change IsLocalRing.residue B (uniformizerRatio G hπ g : B) =
    IsLocalRing.residue B (uniformizerRatio G hπ' g : B)
  apply mul_left_cancel₀ (show IsLocalRing.residue B (v : B) ≠ 0 from
    (IsUnit.map (IsLocalRing.residue B) v.isUnit).ne_zero)
  exact (mul_comm _ _).trans hres.symm

@[simp]
theorem tameInertiaHom_coe {π : B} (hπ : Irreducible π)
    (g : lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) :
    (tameInertiaHom G hπ g : IsLocalRing.ResidueField B) =
      IsLocalRing.residue B (uniformizerRatio G hπ g : B) := rfl

/-- An uniformizer multiple has the next ideal-power order exactly when its
remaining factor has the preceding order. -/
private theorem uniformizer_mul_mem_pow_two {π x : B} (hπ : Irreducible π) :
    π * x ∈ IsLocalRing.maximalIdeal B ^ 2 ↔ x ∈ IsLocalRing.maximalIdeal B := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, pow_two]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact mul_left_cancel₀ hπ.ne_zero (by simpa only [mul_assoc] using hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, by ring⟩

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField B)]

include p in
/-- The residue-unit kernel is precisely the first lower group inside inertia. -/
theorem ker_tameInertiaHom {π : B} (hπ : Irreducible π) :
    (tameInertiaHom G hπ).ker =
      (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1).subgroupOf
        (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) := by
  ext g
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change IsLocalRing.residue B (uniformizerRatio G hπ g : B) = 1 ↔
    (g : G) ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1
  have hcrit : (g : G) ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1 ↔
      (g : G) • π - π ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    simpa only [Nat.cast_one] using
      mem_lowerRamificationGroup_iff_uniformizer G p hπ g.property 1
  rw [hcrit]
  have heq : (g : G) • π - π = π * ((uniformizerRatio G hπ g : B) - 1) := by
    rw [← mul_uniformizerRatio G hπ g]
    ring
  rw [heq, uniformizer_mul_mem_pow_two hπ, ← Ideal.Quotient.eq_zero_iff_mem]
  change IsLocalRing.residue B (uniformizerRatio G hπ g : B) = 1 ↔
    IsLocalRing.residue B ((uniformizerRatio G hπ g : B) - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]

/-- The tame quotient is the finite residue-unit image. -/
def tameInertiaQuotientEquiv {π : B} (hπ : Irreducible π) :
    (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) ⧸
      (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1).subgroupOf
        (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) ≃*
      (tameInertiaHom G hπ).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_tameInertiaHom G p hπ).symm).trans
    (QuotientGroup.quotientKerEquivRange (tameInertiaHom G hπ))

include p in
/-- Tame inertia is cyclic, even when the perfect residue field is infinite. -/
theorem isCyclic_tameInertiaQuotient [Finite G] :
    IsCyclic ((lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) ⧸
      (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1).subgroupOf
        (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  let : Finite (tameInertiaHom G hπ).range :=
    Finite.of_surjective (tameInertiaHom G hπ).rangeRestrict
      (tameInertiaHom G hπ).rangeRestrict_surjective
  let e := tameInertiaQuotientEquiv G p hπ
  exact isCyclic_of_injective e.toMonoidHom e.injective

include p in
/-- The order of the tame inertia quotient is prime to the residue characteristic. -/
theorem coprime_card_tameInertiaQuotient [Finite G] :
    Nat.Coprime p
      (Nat.card ((lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) ⧸
        (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1).subgroupOf
          (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0))) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdiv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  let e := tameInertiaQuotientEquiv G p hπ
  have hgp : g ^ p = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hpimage := congrArg e hgp
  rw [map_pow, map_one] at hpimage
  have hpval := congrArg
    (fun z : (tameInertiaHom G hπ).range => ((z : (IsLocalRing.ResidueField B)ˣ) :
      IsLocalRing.ResidueField B)) hpimage
  change (((e g : (tameInertiaHom G hπ).range) : (IsLocalRing.ResidueField B)ˣ) :
    IsLocalRing.ResidueField B) ^ p = 1 at hpval
  have hz : (((e g : (tameInertiaHom G hπ).range) : (IsLocalRing.ResidueField B)ˣ) :
      IsLocalRing.ResidueField B) = 1 := by
    apply frobenius_inj (IsLocalRing.ResidueField B) p
    simpa only [frobenius_def, one_pow] using hpval
  have heq : e g = 1 := by
    apply Subtype.ext
    exact Units.ext hz
  have hg1 : g = 1 := e.injective (heq.trans e.map_one.symm)
  have : p = 1 := hg.symm.trans (by simp only [hg1, orderOf_one])
  exact (Fact.out : p.Prime).ne_one this

end

end FontaineWintenberger
