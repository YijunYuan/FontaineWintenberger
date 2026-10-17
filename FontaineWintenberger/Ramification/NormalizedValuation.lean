/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Valuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The normalized field valuation of a discrete valuation subring

We use mathlib's canonical adic valuation of the maximal ideal. Its valuation
ring is the original intrinsic valuation subring. The lower groups therefore
agree with the normalized valuation bounds on the ambient field.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing

variable {R E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field E] [Algebra R E] [IsFractionRing R E]

/-- Ideal powers agree with the canonical normalized valuation on the field
of fractions, including at zero. -/
theorem mem_maximalIdeal_pow_iff_valuation (x : R) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔
      (maximalIdeal R).valuation E (algebraMap R E x) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact ((maximalIdeal R).intValuation_le_pow_iff_mem x n).symm

end FontaineWintenberger

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

local notation "w" => IsDedekindDomain.HeightOneSpectrum.valuation L
  (IsDiscreteValuationRing.maximalIdeal A)

/-- The canonical normalized field valuation has the original valuation ring. -/
theorem normalizedValuation_valuationSubring : (w).valuationSubring = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    change (a : L) = x at ha
    exact ha ▸ a.property
  · intro hx
    exact (IsDiscreteValuationRing.maximalIdeal A).valuation_le_one (⟨x, hx⟩ : A)

theorem mem_maximalIdeal_pow_iff_normalizedValuation (x : A) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal A ^ n ↔ w (x : L) ≤ WithZero.exp (-(n : ℤ)) :=
  FontaineWintenberger.mem_maximalIdeal_pow_iff_valuation x n

variable (K : Type*) [Field K] [Algebra K L]

/-- On integral elements, invariance of the normalized field valuation follows
from invariance of the canonical integral valuation. -/
theorem normalizedValuation_coe_smul (g : A.decompositionSubgroup K) (x : A) :
    w ((g • x : A) : L) = w (x : L) := by
  change w (algebraMap A L (g • x)) = w (algebraMap A L x)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.intValuation_maximalIdeal, FontaineWintenberger.addVal_smul]

/-- Every decomposition-group element preserves the normalized field valuation. -/
theorem normalizedValuation_apply (g : A.decompositionSubgroup K) (x : L) :
    w ((g : L ≃ₐ[K] L) x) = w x := by
  rcases A.mem_or_inv_mem x with hx | hx
  · exact normalizedValuation_coe_smul A K g ⟨x, hx⟩
  · have h := normalizedValuation_coe_smul A K g ⟨x⁻¹, hx⟩
    change w ((g : L ≃ₐ[K] L) (x⁻¹)) = w (x⁻¹) at h
    simpa only [map_inv₀, inv_inj] using h

/-- Lower groups defined through ideal inertia agree with the normalized
valuation bounds on the ambient field. -/
theorem mem_lowerRamificationGroup_iff_normalizedValuation (n : ℤ)
    (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔
      ∀ x : A, w ((g : L ≃ₐ[K] L) (x : L) - (x : L)) ≤
        WithZero.exp (-((n + 1).toNat : ℤ)) := by
  rw [mem_lowerRamificationGroup_iff]
  exact forall_congr' fun x => mem_maximalIdeal_pow_iff_normalizedValuation A (g • x - x) _

end ValuationSubring
