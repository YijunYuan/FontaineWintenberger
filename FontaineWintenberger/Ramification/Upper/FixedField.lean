/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.FixedField
public import FontaineWintenberger.Ramification.Upper.Tate

/-!
# Intrinsic ramification under fixed-field restriction

Normal restriction lands in the decomposition subgroup of the
restricted valuation ring. Its existing intrinsic action supplies the
fixed-field order in Tate's coset identity.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L]
variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F₀ L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀

/-- Normal field restriction preserves the restricted integer ring. -/
theorem restrictNormal_mem_fixedField_decomposition (σ : L ≃ₐ[K] L) :
    σ.restrictNormal F₀ ∈ D₀ := by
  change σ.restrictNormal F₀ • A₀ = A₀
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change spectralValuation K L (algebraMap F₀ L ((σ.restrictNormal F₀)⁻¹ x)) ≤ 1 ↔
    spectralValuation K L (algebraMap F₀ L x) ≤ 1
  have hi : (σ.restrictNormal F₀)⁻¹ = (σ⁻¹).restrictNormal F₀ :=
    (map_inv (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F₀) σ).symm
  rw [hi, AlgEquiv.restrictNormal_commutes]
  change spectralNorm K L (σ⁻¹ (algebraMap F₀ L x)) ≤ 1 ↔
    spectralNorm K L (algebraMap F₀ L x) ≤ 1
  rw [← spectralNorm_eq_of_equiv σ⁻¹ (algebraMap F₀ L x)]

/-- Restriction into the intrinsic decomposition group of the fixed-field integers. -/
noncomputable def fixedFieldDecompositionRestriction : (L ≃ₐ[K] L) →* D₀ :=
  (AlgEquiv.restrictNormalHom F₀).codRestrict _
    (restrictNormal_mem_fixedField_decomposition K L H)

/-- The restricted automorphism is precisely the ordinary field restriction. -/
@[simp]
theorem coe_fixedFieldDecompositionRestriction (σ : L ≃ₐ[K] L) :
    (fixedFieldDecompositionRestriction K L H σ : F₀ ≃ₐ[K] F₀) = σ.restrictNormal F₀ := rfl

/-- The intrinsic restricted integer action agrees with the ambient field action. -/
theorem coe_fixedFieldDecompositionRestriction_smul (σ : L ≃ₐ[K] L) (a : A₀) :
    (((fixedFieldDecompositionRestriction K L H σ) • a : A₀) : F₀) =
      σ.restrictNormal F₀ (a : F₀) := rfl

/-- Every fixed-field automorphism preserves its integer ring. -/
theorem fixedField_decompositionSubgroup_eq_top : D₀ = ⊤ := by
  apply top_unique
  intro τ _
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := F₀) (E := L) τ
  exact restrictNormal_mem_fixedField_decomposition K L H σ

variable [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- Every intrinsic fixed-field decomposition automorphism is a field restriction. -/
theorem fixedFieldDecompositionRestriction_surjective :
    Function.Surjective (fixedFieldDecompositionRestriction K L H) := by
  intro g
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := F₀) (E := L) (g : F₀ ≃ₐ[K] F₀)
  exact ⟨σ, Subtype.ext hσ⟩

/-- The intrinsic restriction map has exactly the prescribed normal subgroup as kernel. -/
theorem fixedFieldDecompositionRestriction_ker :
    (fixedFieldDecompositionRestriction K L H).ker = H := by
  refine Eq.trans ?_ (IntermediateField.fixingSubgroup_fixedField H)
  ext σ
  change fixedFieldDecompositionRestriction K L H σ = 1 ↔ _
  rw [Subtype.ext_iff]
  change σ.restrictNormal F₀ = 1 ↔ ∀ x : F₀, σ (x : L) = (x : L)
  constructor
  · intro h x
    calc
      σ (x : L) = ((σ.restrictNormal F₀ x : F₀) : L) :=
        (AlgEquiv.restrictNormal_apply F₀ σ x).symm
      _ = (x : L) := by rw [h]; rfl
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_apply F₀ σ x).trans (h x)

/-- The intrinsic decomposition group is the prescribed Galois quotient. -/
noncomputable def fixedFieldDecompositionQuotientEquiv : (L ≃ₐ[K] L) ⧸ H ≃* D₀ :=
  QuotientGroup.liftEquiv (N := H) (fixedFieldDecompositionRestriction_surjective K L H)
    (fixedFieldDecompositionRestriction_ker K L H).symm

@[simp]
theorem fixedFieldDecompositionQuotientEquiv_mk (σ : L ≃ₐ[K] L) :
    fixedFieldDecompositionQuotientEquiv K L H σ =
      fixedFieldDecompositionRestriction K L H σ := rfl

/-- Left translation identifies the restriction fiber with the subgroup. -/
noncomputable def fixedFieldRestrictionFiberEquiv (σ : L ≃ₐ[K] L) :
    H ≃ {s : L ≃ₐ[K] L // fixedFieldDecompositionRestriction K L H s =
      fixedFieldDecompositionRestriction K L H σ} :=
  (Equiv.subtypeEquiv (Equiv.refl (L ≃ₐ[K] L)) (fun g => by
    change g ∈ H ↔ g ∈ (fixedFieldDecompositionRestriction K L H).ker
    rw [fixedFieldDecompositionRestriction_ker K L H])).trans
      ((fixedFieldDecompositionRestriction K L H).fiberEquivKer σ).symm

@[simp]
theorem coe_fixedFieldRestrictionFiberEquiv (σ : L ≃ₐ[K] L) (h : H) :
    (fixedFieldRestrictionFiberEquiv K L H σ h : L ≃ₐ[K] L) = σ * h.1 := rfl

omit [FiniteDimensional K L] in
/-- Restriction intertwines the intrinsic actions on the two integer rings. -/
theorem fixedFieldDecompositionRestriction_algebraMap (σ : L ≃ₐ[K] L) (a : A₀) :
    algebraMap A₀ B₀ (fixedFieldDecompositionRestriction K L H σ • a) =
      σ • algebraMap A₀ B₀ a := by
  apply Subtype.ext
  change algebraMap F₀ L (σ.restrictNormal F₀ (a : F₀)) =
    σ (algebraMap F₀ L (a : F₀))
  exact AlgEquiv.restrictNormal_commutes σ F₀ (a : F₀)

/-- The intrinsic decomposition action fixes the coefficient integers. -/
instance fixedFieldDecomposition_smulCommClass : SMulCommClass D₀ 𝒪[K] A₀ where
  smul_comm g r a := by
    apply Subtype.ext
    change (g : F₀ ≃ₐ[K] F₀) ((r : K) • (a : F₀)) =
      (r : K) • (g : F₀ ≃ₐ[K] F₀) (a : F₀)
    exact map_smul (g : F₀ ≃ₐ[K] F₀) (r : K) (a : F₀)

omit [H.Normal] in
/-- Passing to the induced integer algebra automorphism preserves the intrinsic order. -/
theorem fixedFieldDecomposition_order
    [IsDiscreteValuationRing 𝒪[K]]
    (g : D₀) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    ramificationOrder (R := A₀) (A₀ ≃ₐ[𝒪[K]] A₀)
        (MulSemiringAction.toAlgAut D₀ 𝒪[K] A₀ g) =
      (A₀).ramificationOrder K g := rfl

variable [PerfectField 𝓀[K]]

/-- The scaled coset identity on the field restriction and intrinsic integer orders. -/
theorem fixedField_ramificationIdx_mul_order_eq_sum (σ : L ≃ₐ[K] L) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite H
    ((IsLocalRing.maximalIdeal B₀).ramificationIdx A₀ : ℕ∞) *
        (A₀).ramificationOrder K (fixedFieldDecompositionRestriction K L H σ) =
      ∑ h : H, ramificationOrder (R := B₀) (L ≃ₐ[K] L) (σ * h.1) := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  have := fixedField_integer_isGaloisGroup K L H
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K L
  obtain ⟨y, hy⟩ := intermediate_spectral_exists_generator K L F₀
  exact ramificationIdx_mul_order_eq_sum_coset (L ≃ₐ[K] L) H
    (MulSemiringAction.toAlgAut D₀ 𝒪[K] A₀ (fixedFieldDecompositionRestriction K L H σ)) σ
    (fixedFieldDecompositionRestriction_algebraMap K L H σ) hx hy

omit [H.Normal] in
/-- The subgroup inertia has the canonical relative ramification index as its order. -/
theorem fixedField_card_inertia :
    Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) =
      (IsLocalRing.maximalIdeal B₀).ramificationIdx A₀ := by
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  have := fixedField_integer_moduleFinite K L H
  have := fixedField_integer_isGaloisGroup K L H
  have : PerfectField (IsLocalRing.ResidueField A₀) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField 𝒪[K])
  have := hasSeparableResidueFieldsAt_maximalIdeal A₀ B₀
  exact card_lowerRamificationGroup_zero A₀ B₀ H

/-- The scaled intrinsic coset identity with its inertia-cardinality denominator. -/
theorem fixedField_card_inertia_mul_order_eq_sum (σ : L ≃ₐ[K] L) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite H
    (Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) : ℕ∞) *
        (A₀).ramificationOrder K (fixedFieldDecompositionRestriction K L H σ) =
      ∑ h : H, ramificationOrder (R := B₀) (L ≃ₐ[K] L) (σ * h.1) := by
  rw [fixedField_card_inertia K L H]
  exact fixedField_ramificationIdx_mul_order_eq_sum K L H σ

/-- Tate's coset average, in extended nonnegative reals so division is exact. -/
theorem fixedField_order_eq_sum_div_ramificationIdx (σ : L ≃ₐ[K] L) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite H
    ((A₀).ramificationOrder K (fixedFieldDecompositionRestriction K L H σ) : ℝ≥0∞) =
      (∑ h : H, (ramificationOrder (R := B₀) (L ≃ₐ[K] L) (σ * h.1) : ℝ≥0∞)) /
        (IsLocalRing.maximalIdeal B₀).ramificationIdx A₀ := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  let := Fintype.ofFinite H
  apply (ENNReal.eq_div_iff
    (by exact_mod_cast (local_ramificationIdx_pos A₀ B₀).ne')
    (ENNReal.natCast_ne_top _)).2
  have h := congrArg ENat.toENNRealRingHom
    (fixedField_ramificationIdx_mul_order_eq_sum K L H σ)
  simpa only [map_mul, map_sum, ENat.toENNRealRingHom_apply, ENat.toENNReal_coe] using h

/-- The same average with the subgroup inertia as its denominator. -/
theorem fixedField_order_eq_sum_div_card_inertia (σ : L ≃ₐ[K] L) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite H
    ((A₀).ramificationOrder K (fixedFieldDecompositionRestriction K L H σ) : ℝ≥0∞) =
      (∑ h : H, (ramificationOrder (R := B₀) (L ≃ₐ[K] L) (σ * h.1) : ℝ≥0∞)) /
        Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) := by
  rw [fixedField_card_inertia K L H]
  exact fixedField_order_eq_sum_div_ramificationIdx K L H σ

/-- The source's restriction-fiber average for every fixed-field automorphism. -/
theorem fixedField_order_eq_fiber_sum_div_ramificationIdx (τ : D₀) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite {s : L ≃ₐ[K] L //
      fixedFieldDecompositionRestriction K L H s = τ}
    ((A₀).ramificationOrder K τ : ℝ≥0∞) =
      (∑ s : {s : L ≃ₐ[K] L // fixedFieldDecompositionRestriction K L H s = τ},
        (ramificationOrder (R := B₀) (L ≃ₐ[K] L) s.1 : ℝ≥0∞)) /
        (IsLocalRing.maximalIdeal B₀).ramificationIdx A₀ := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L F₀
  let := Fintype.ofFinite H
  obtain ⟨σ, rfl⟩ := fixedFieldDecompositionRestriction_surjective K L H τ
  let := Fintype.ofFinite {s : L ≃ₐ[K] L //
    fixedFieldDecompositionRestriction K L H s = fixedFieldDecompositionRestriction K L H σ}
  rw [fixedField_order_eq_sum_div_ramificationIdx K L H σ]
  congr 1
  exact (fixedFieldRestrictionFiberEquiv K L H σ).sum_comp
    (fun s => (ramificationOrder (R := B₀) (L ≃ₐ[K] L) s.1 : ℝ≥0∞))

/-- The restriction-fiber average with the subgroup inertia denominator. -/
theorem fixedField_order_eq_fiber_sum_div_card_inertia (τ : D₀) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F₀
    letI := Fintype.ofFinite {s : L ≃ₐ[K] L //
      fixedFieldDecompositionRestriction K L H s = τ}
    ((A₀).ramificationOrder K τ : ℝ≥0∞) =
      (∑ s : {s : L ≃ₐ[K] L // fixedFieldDecompositionRestriction K L H s = τ},
        (ramificationOrder (R := B₀) (L ≃ₐ[K] L) s.1 : ℝ≥0∞)) /
        Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) := by
  rw [fixedField_card_inertia K L H]
  exact fixedField_order_eq_fiber_sum_div_ramificationIdx K L H τ

end FontaineWintenberger
