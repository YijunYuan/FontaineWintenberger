/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Embedding.Basic

/-!
# Ramification of arbitrary valuation-preserving automorphisms

The order is the infimum on the valuation ring. Perfect residue
digits compute it on every uniformizer, without a completeness, finite residue
field, or finite-order automorphism hypothesis.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

section IntegerAutomorphism

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The signed displacement order on the DVR. -/
def integerRamificationNumber (g : R ≃+* R) : EReal :=
  ((ramificationOrder (R := R) (R ≃+* R) g : ℝ≥0∞) : EReal) - 1

/-- The integral displacement infimum is attained, including at infinity. -/
theorem exists_addVal_eq_ramificationOrder (g : R ≃+* R) :
    ∃ a : R, IsDiscreteValuationRing.addVal R (g a - a) =
      ramificationOrder (R := R) (R ≃+* R) g :=
  ENat.exists_eq_iInf _

theorem neg_one_le_integerRamificationNumber (g : R ≃+* R) :
    -1 ≤ integerRamificationNumber g := by
  unfold integerRamificationNumber
  simpa only [zero_sub] using EReal.sub_le_sub (EReal.coe_ennreal_nonneg _)
    (show (1 : EReal) ≤ 1 from le_rfl)

theorem integerRamificationNumber_eq_top_iff (g : R ≃+* R) :
    integerRamificationNumber g = ⊤ ↔ g = 1 := by
  unfold integerRamificationNumber
  rw [sub_eq_add_neg, ← EReal.coe_one, ← EReal.coe_neg,
    EReal.add_eq_top_iff_eq_top_left (EReal.coe_ne_bot (-1)) (EReal.coe_ne_top (-1)),
    EReal.coe_ennreal_eq_top_iff, ENat.toENNReal_eq_top, ramificationOrder_eq_top_iff]

theorem integerRamificationNumber_eq_nat_sub_one {g : R ≃+* R} (hg : g ≠ 1) :
    ∃ n : ℕ, integerRamificationNumber g = (n : EReal) - 1 := by
  have hfin : ramificationOrder (R := R) (R ≃+* R) g ≠ ⊤ :=
    (ramificationOrder_eq_top_iff (R := R) (R ≃+* R) g).not.mpr hg
  refine ⟨(ramificationOrder (R := R) (R ≃+* R) g).toNat, ?_⟩
  unfold integerRamificationNumber
  rw [← ENat.natCast_toNat hfin, ENat.toENNReal_coe]
  norm_cast

/-- The residue automorphism is trivial precisely when every
integral displacement belongs to the maximal ideal. -/
theorem residueAut_eq_refl_iff (g : R ≃+* R) :
    IsLocalRing.ResidueField.mapEquiv g = RingEquiv.refl _ ↔
      ∀ a : R, g a - a ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro h a
    exact Ideal.Quotient.eq.mp (congrArg (fun e => e (IsLocalRing.residue R a)) h)
  · intro h
    apply RingEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
    exact Ideal.Quotient.eq.mpr (h b)

theorem integerRamificationNumber_eq_neg_one_of_residue_ne (g : R ≃+* R)
    (hres : IsLocalRing.ResidueField.mapEquiv g ≠ RingEquiv.refl _) :
    integerRamificationNumber g = -1 := by
  have hzero : ramificationOrder (R := R) (R ≃+* R) g = 0 := by
    by_contra hn
    have hraw := Order.one_le_iff_ne_zero.mpr hn
    apply hres
    apply (residueAut_eq_refl_iff g).mpr
    intro a
    have ha := hraw.trans (ramificationOrder_le (R := R) (R ≃+* R) g a)
    simpa only [pow_one] using (mem_maximalIdeal_pow_iff_addVal (g a - a) 1).mpr ha
  simp [integerRamificationNumber, hzero]

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    [PerfectField (IsLocalRing.ResidueField R)]

include p in
/-- Inertia makes every uniformizer compute the same intrinsic
order. The necessary membership of the residue characteristic is derived. -/
theorem integerRamificationNumber_eq_uniformizer (g : R ≃+* R)
    (hres : IsLocalRing.ResidueField.mapEquiv g = RingEquiv.refl _)
    {π : R} (hπ : Irreducible π) :
    integerRamificationNumber g =
      (((IsDiscreteValuationRing.addVal R (g π - π) : ℝ≥0∞) : EReal) - 1) := by
  have hp : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    simp only [map_natCast, CharP.cast_eq_zero]
  exact congrArg (fun n : ℕ∞ => (((n : ℝ≥0∞) : EReal) - 1))
    (integralEmbeddingOrder_eq_uniformizer g.toRingHom (RingHom.id R) p hp
      ((residueAut_eq_refl_iff g).mp hres) hπ)

end IntegerAutomorphism

section ValuationRestriction

variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) (g : F ≃+* F) (hv : ∀ x : F, v (g x) = v x)

/-- A valuation-preserving automorphism restricts to the same
valuation ring; its inverse preserves that ring by the same equality. -/
def valuationIntegerAut : v.valuationSubring ≃+* v.valuationSubring where
  toFun x := ⟨g x, by change v (g x) ≤ 1; rw [hv]; exact x.2⟩
  invFun x := ⟨g.symm x, by
    change v (g.symm x) ≤ 1
    have h := hv (g.symm x)
    rw [g.apply_symm_apply] at h
    rw [← h]
    exact x.2⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x)
  right_inv x := Subtype.ext (g.apply_symm_apply x)
  map_mul' x y := Subtype.ext (g.map_mul x y)
  map_add' x y := Subtype.ext (g.map_add x y)

@[simp]
theorem coe_valuationIntegerAut (x : v.valuationSubring) :
    (valuationIntegerAut v g hv x : F) = g x := rfl

/-- The same-field automorphism is determined by its restriction to the
valuation ring, using its field of fractions. -/
theorem valuationIntegerAut_eq_one_iff : valuationIntegerAut v g hv = 1 ↔ g = 1 := by
  constructor
  · intro hg
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := v.valuationSubring)
    intro a
    exact congrArg (fun z : v.valuationSubring => (z : F))
      (congrArg (fun f : v.valuationSubring ≃+* v.valuationSubring => f a) hg)
  · rintro rfl
    exact RingEquiv.ext fun a => Subtype.ext rfl

variable [IsDiscreteValuationRing v.valuationSubring]

/-- The intrinsic signed ramification number of an arbitrary
valuation-preserving field automorphism. -/
def valuedRamificationNumber : EReal :=
  integerRamificationNumber (valuationIntegerAut v g hv)

theorem valuedRamificationNumber_eq_top_iff :
    valuedRamificationNumber v g hv = ⊤ ↔ g = 1 := by
  rw [valuedRamificationNumber, integerRamificationNumber_eq_top_iff,
    valuationIntegerAut_eq_one_iff]

theorem neg_one_le_valuedRamificationNumber : -1 ≤ valuedRamificationNumber v g hv :=
  neg_one_le_integerRamificationNumber _

theorem valuedRamificationNumber_eq_nat_sub_one (hg : g ≠ 1) :
    ∃ n : ℕ, valuedRamificationNumber v g hv = (n : EReal) - 1 :=
  integerRamificationNumber_eq_nat_sub_one
    (fun h => hg ((valuationIntegerAut_eq_one_iff v g hv).mp h))

theorem valuedRamificationNumber_eq_neg_one_of_residue_ne
    (hres : IsLocalRing.ResidueField.mapEquiv (valuationIntegerAut v g hv) ≠
      RingEquiv.refl _) : valuedRamificationNumber v g hv = -1 :=
  integerRamificationNumber_eq_neg_one_of_residue_ne _ hres

end ValuationRestriction

section NormalizedAdditiveValue

variable {F : Type*} [Field F] (A : ValuationSubring F) [IsDiscreteValuationRing A]

local notation "w" => IsDedekindDomain.HeightOneSpectrum.valuation F
  (IsDiscreteValuationRing.maximalIdeal A)

/-- The canonical normalized additive field valuation, with its
infinite value at zero, written in the standard extended reals. -/
def normalizedAdditiveValue (x : F) : EReal := by
  classical
  exact if x = 0 then ⊤ else (((-(WithZero.log (w x)) : ℤ) : ℝ) : EReal)

@[simp]
theorem normalizedAdditiveValue_zero : normalizedAdditiveValue A 0 = ⊤ := by
  simp [normalizedAdditiveValue]

/-- The canonical additive field value extends the canonical integral
valuation of the ring. -/
theorem normalizedAdditiveValue_coe (a : A) :
    normalizedAdditiveValue A (a : F) =
      ((IsDiscreteValuationRing.addVal A a : ℝ≥0∞) : EReal) := by
  by_cases ha : a = 0
  · simp [ha]
  have haF : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  have hfin := (IsDiscreteValuationRing.addVal_eq_top_iff (a := a)).not.mpr ha
  have hw : w (a : F) = WithZero.exp
      (-((IsDiscreteValuationRing.addVal A a).toNat : ℤ)) := by
    change w (algebraMap A F a) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal, ← ENat.natCast_toNat hfin]
    rfl
  rw [normalizedAdditiveValue, ite_eq_right haF, hw, WithZero.log_exp, neg_neg,
    ← ENat.natCast_toNat hfin, ENat.toENNReal_coe]
  norm_cast

/-- Division by a nonzero field element subtracts its normalized
additive value, also when the numerator vanishes. -/
theorem normalizedAdditiveValue_div (x y : F) (hy : y ≠ 0) :
    normalizedAdditiveValue A (x / y) =
      normalizedAdditiveValue A x - normalizedAdditiveValue A y := by
  by_cases hx : x = 0
  · subst x
    rw [zero_div, normalizedAdditiveValue_zero, normalizedAdditiveValue,
      ite_eq_right hy]
    exact (EReal.top_sub_coe _).symm
  rw [normalizedAdditiveValue, ite_eq_right (div_ne_zero hx hy),
    normalizedAdditiveValue, ite_eq_right hx, normalizedAdditiveValue, ite_eq_right hy,
    map_div₀, WithZero.log_div ((w).ne_zero_iff.mpr hx) ((w).ne_zero_iff.mpr hy)]
  push_cast
  norm_cast
  ring

end NormalizedAdditiveValue

section IntrinsicFieldInfimum

variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [IsDiscreteValuationRing v.valuationSubring]
    (g : F ≃+* F) (hv : ∀ x : F, v (g x) = v x)

/-- The field-valued infimum is the integral displacement
order, since the canonical normalized field value extends `addVal`. -/
theorem ramificationOrder_eq_iInf_normalizedAdditiveValue :
    ((ramificationOrder (R := v.valuationSubring) (v.valuationSubring ≃+*
      v.valuationSubring) (valuationIntegerAut v g hv) : ℝ≥0∞) : EReal) =
      ⨅ a : v.valuationSubring,
        normalizedAdditiveValue v.valuationSubring (g (a : F) - a) := by
  have he (a : v.valuationSubring) : g (a : F) - a =
      ((valuationIntegerAut v g hv a - a : v.valuationSubring) : F) := rfl
  simp_rw [he, normalizedAdditiveValue_coe]
  apply le_antisymm
  · apply le_iInf
    intro a
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (ENat.toENNReal_mono
      (ramificationOrder_le (R := v.valuationSubring) _ _ a))
  · obtain ⟨a, ha⟩ := exists_addVal_eq_ramificationOrder (valuationIntegerAut v g hv)
    exact (iInf_le _ a).trans_eq (congrArg (fun n : ℕ∞ => ((n : ℝ≥0∞) : EReal)) ha)

/-- The intrinsic signed number is exactly the normalized field infimum
minus one, on the valuation ring and field. -/
theorem valuedRamificationNumber_eq_iInf :
    valuedRamificationNumber v g hv =
      (⨅ a : v.valuationSubring,
        normalizedAdditiveValue v.valuationSubring (g (a : F) - a)) - 1 := by
  exact congrArg (fun r : EReal => r - 1)
    (ramificationOrder_eq_iInf_normalizedAdditiveValue v g hv)

end IntrinsicFieldInfimum

section UniformizerRatio

variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [IsDiscreteValuationRing v.valuationSubring]
    (g : F ≃+* F) (hv : ∀ x : F, v (g x) = v x)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    [PerfectField (IsLocalRing.ResidueField v.valuationSubring)]

include p in
/-- Every uniformizer computes the signed field number by the
ratio displacement in the field. -/
theorem valuedRamificationNumber_eq_uniformizer_ratio
    (hres : IsLocalRing.ResidueField.mapEquiv (valuationIntegerAut v g hv) =
      RingEquiv.refl _) {π : v.valuationSubring} (hπ : Irreducible π) :
    valuedRamificationNumber v g hv =
      normalizedAdditiveValue v.valuationSubring (g (π : F) / (π : F) - 1) := by
  have hπF : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have he : g (π : F) / (π : F) - 1 =
      ((valuationIntegerAut v g hv π - π : v.valuationSubring) : F) / (π : F) := by
    change g (π : F) / (π : F) - 1 = (g (π : F) - π) / (π : F)
    exact div_sub_one hπF
  rw [he, normalizedAdditiveValue_div _ _ _ hπF,
    normalizedAdditiveValue_coe, normalizedAdditiveValue_coe,
    IsDiscreteValuationRing.addVal_uniformizer hπ]
  simpa only [ENat.toENNReal_one, EReal.coe_ennreal_one, valuedRamificationNumber] using
    integerRamificationNumber_eq_uniformizer p _ hres hπ

include p in
/-- The field expression is independent of every choice of
uniformizer, including when the automorphism is the identity. -/
theorem uniformizer_ratio_normalizedAdditiveValue_eq
    (hres : IsLocalRing.ResidueField.mapEquiv (valuationIntegerAut v g hv) =
      RingEquiv.refl _) {π ϖ : v.valuationSubring}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    normalizedAdditiveValue v.valuationSubring (g (π : F) / (π : F) - 1) =
      normalizedAdditiveValue v.valuationSubring (g (ϖ : F) / (ϖ : F) - 1) :=
  (valuedRamificationNumber_eq_uniformizer_ratio v g hv p hres hπ).symm.trans
    (valuedRamificationNumber_eq_uniformizer_ratio v g hv p hres hϖ)

end UniformizerRatio

end FontaineWintenberger
