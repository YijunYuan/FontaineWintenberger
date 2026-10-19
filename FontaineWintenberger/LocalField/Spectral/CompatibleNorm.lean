/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Spectral.Uniqueness
public import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# Norm compatibility for a discrete valuation

Mathlib's rank-one norm keeps the valued uniform space. We identify
its valuation ring with the intrinsic ring and transfer the DVR
structure, without any hypothesis that the residue field is finite.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [Field K] (Γ : Type*) [LinearOrderedCommGroupWithZero Γ]
variable [val : Valued K Γ] [Valuation.IsRankOneDiscrete val.v]

noncomputable local instance discrete_rankOne : Valuation.RankOne val.v :=
  Valuation.IsRankOneDiscrete.rankOne val.v (e := 2) (by norm_num)

/-- The nontrivial normed structure obtained from the given discrete valuation. -/
@[instance_reducible]
noncomputable def discreteValuedNormedField : NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField K Γ

noncomputable local instance : NontriviallyNormedField K := discreteValuedNormedField K Γ

local instance : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (Valued.isNonarchimedean_norm K Γ)

theorem discreteValued_norm_le_iff (x y : K) : ‖x‖ ≤ ‖y‖ ↔ val.v x ≤ val.v y :=
  Valued.toNormedField.norm_le_iff

/-- Norm and valuation give exactly the same intrinsic integer ring. -/
theorem discreteValued_valuationSubring :
    (NormedField.valuation (K := K)).valuationSubring = val.v.valuationSubring := by
  ext x
  change ‖x‖₊ ≤ 1 ↔ val.v x ≤ 1
  exact_mod_cast (Valued.toNormedField.norm_le_one_iff (x := x))

/-- The normed structure keeps the uniformity definitionally. -/
theorem discreteValued_uniformSpace :
    (discreteValuedNormedField K Γ).toUniformSpace = Valued.toUniformSpace := rfl

/-- Completeness is completeness for the compatible norm, with no transport axiom. -/
theorem discreteValued_completeSpace [h : CompleteSpace K] :
    @CompleteSpace K (discreteValuedNormedField K Γ).toUniformSpace := h

theorem discreteValued_unitBall_isDiscreteValuationRing
    [IsDiscreteValuationRing val.v.valuationSubring] :
    IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring := by
  rw [discreteValued_valuationSubring K Γ]
  infer_instance

/-- The bundled hypothesis for the norm attached to a complete discrete valuation. -/
theorem discreteValued_isCompleteDiscreteValuedField [h : CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring] : IsCompleteDiscreteValuedField K :=
  have : @CompleteSpace K (discreteValuedNormedField K Γ).toUniformSpace := h
  have := discreteValued_unitBall_isDiscreteValuationRing K Γ
  {}

/-- Henselianity for the valuation ring. -/
theorem discreteValued_henselianLocalRing [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring] :
    HenselianLocalRing val.v.valuationSubring := by
  have := discreteValued_unitBall_isDiscreteValuationRing K Γ
  rw [← discreteValued_valuationSubring K Γ]
  exact unitBall_henselianLocalRing K

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The spectral extension is compatible with the valuation. -/
instance discreteValued_spectral_hasExtension [CompleteSpace K] :
    val.v.HasExtension (spectralValuation K L) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, spectralValuation_algebraMap]
    exact_mod_cast (discreteValued_norm_le_iff K Γ x y).symm


section ChosenExtension

omit [Algebra.IsAlgebraic K L]

variable {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL] (w : Valuation L ΓL)
variable [val.v.HasExtension w]

/-- Extension compatibility survives replacing the valuation by its compatible norm. -/
theorem discreteValued_norm_hasExtension :
    (NormedField.valuation (K := K)).HasExtension w where
  val_isEquiv_comap := by
    intro x y
    change ‖x‖₊ ≤ ‖y‖₊ ↔ w (algebraMap K L x) ≤ w (algebraMap K L y)
    have hnorm : ‖x‖₊ ≤ ‖y‖₊ ↔ val.v x ≤ val.v y := by
      exact_mod_cast discreteValued_norm_le_iff K Γ x y
    exact hnorm.trans (Valuation.HasExtension.val_map_le_iff val.v w x y).symm

include K Γ in
/-- DVR structure for the chosen extension of a source-valued complete field. -/
theorem discreteValued_extension_isDiscreteValuationRing [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : IsDiscreteValuationRing w.valuationSubring := by
  have := discreteValued_norm_hasExtension K Γ L w
  have := discreteValued_isCompleteDiscreteValuedField K Γ
  exact extensionValuationSubring_isDiscreteValuationRing K L w

include K Γ in
theorem discreteValued_extension_henselianLocalRing [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : HenselianLocalRing w.valuationSubring := by
  have := discreteValued_norm_hasExtension K Γ L w
  have := discreteValued_isCompleteDiscreteValuedField K Γ
  exact extensionValuationSubring_henselianLocalRing K L w

/-- Integral generation over the ring for any compatible chosen extension. -/
theorem discreteValued_extension_exists_generator [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField val.v.valuationSubring)]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ x : w.valuationSubring, Algebra.adjoin val.v.valuationSubring {x} = ⊤ := by
  have := discreteValued_norm_hasExtension K Γ L w
  have := discreteValued_isCompleteDiscreteValuedField K Γ
  have : PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) := by
    rw [discreteValued_valuationSubring K Γ]
    infer_instance
  obtain ⟨x, hx⟩ := extensionValuationSubring_exists_generator K L w
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hx
  refine ⟨x, ?_⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  let e := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (discreteValued_valuationSubring K Γ))
  have he : (algebraMap val.v.valuationSubring w.valuationSubring).comp
      e.toRingHom = algebraMap (NormedField.valuation (K := K)).valuationSubring
        w.valuationSubring := by
    ext r
    rfl
  intro b
  obtain ⟨p, hp⟩ := hx b
  refine ⟨p.map e.toRingHom, ?_⟩
  change (p.map e.toRingHom).eval₂ (algebraMap val.v.valuationSubring w.valuationSubring) x = b
  rw [Polynomial.eval₂_map, he]
  exact hp

end ChosenExtension

/-- Monogenicity over the integer ring, through the compatible norm. -/
theorem discreteValued_spectral_exists_generator [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField val.v.valuationSubring)]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ x : spectralIntegerRing K L, Algebra.adjoin val.v.valuationSubring {x} = ⊤ :=
  discreteValued_extension_exists_generator K Γ L (spectralValuation K L)

end FontaineWintenberger
