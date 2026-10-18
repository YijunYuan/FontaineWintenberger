/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.IntegralGenerator

/-!
# The spectral integer ring equals every compatible extension valuation ring

Integral closedness gives inclusion into any compatible valuation ring. The
one-dimensional valuation overring theorem and localness exclude a larger ring.
-/

@[expose] public section

namespace Valuation.HasExtension

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ΓK ΓL : Type*} [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] (v : Valuation K ΓK) (w : Valuation L ΓL)
    [v.HasExtension w]

/-- The canonical map between compatible field valuation rings is injective. -/
instance valuationSubring_faithfulSMul : FaithfulSMul v.valuationSubring w.valuationSubring := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro a b hab
  apply Subtype.ext
  apply (algebraMap K L).injective
  exact congrArg (fun y : w.valuationSubring => (y : L)) hab

end Valuation.HasExtension

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
variable [(NormedField.valuation (K := K)).HasExtension w]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The actual integral-closure construction equals any compatible chosen valuation ring. -/
theorem spectralIntegerRing_eq_extension_valuationSubring :
    spectralIntegerRing K L = w.valuationSubring := by
  apply ValuationSubring.eq_of_le_of_ne_top
  · intro x hx
    have hint : IsIntegral OK x := (isIntegral_iff_spectralNorm_le_one K x).mpr hx
    have hW : IsIntegral w.valuationSubring x := hint.tower_top
    exact (Valuation.valuationSubring.integers w).isIntegral_iff_v_le_one.mp hW
  · intro htop
    have hfield : IsField w.valuationSubring := by
      rw [htop]
      exact Field.toIsField _
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible OK
    have hmem : ¬ IsUnit (algebraMap OK w.valuationSubring π) :=
      map_nonunit (algebraMap OK w.valuationSubring) π hπ.not_isUnit
    have hne : algebraMap OK w.valuationSubring π ≠ 0 := by
      intro h
      apply hπ.ne_zero
      apply Subtype.ext
      apply (algebraMap K L).injective
      simpa using congrArg (fun y : w.valuationSubring => (y : L)) h
    let := hfield.toField
    exact hmem (isUnit_iff_ne_zero.mpr hne)

/-- Any compatible chosen valuation ring is the actual base integral closure in `L`. -/
instance extensionValuationSubring_isIntegralClosure :
    IsIntegralClosure w.valuationSubring OK L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [← spectralIntegerRing_eq_extension_valuationSubring K L w]
    exact (spectralIntegerRing_isIntegralClosure K L).isIntegral_iff

instance extensionValuationSubring_moduleFinite : Module.Finite OK w.valuationSubring :=
  IsIntegralClosure.finite (A := OK) (K := K) (L := L) (C := w.valuationSubring)

include K in
theorem extensionValuationSubring_isDiscreteValuationRing :
    IsDiscreteValuationRing w.valuationSubring := by
  rw [← spectralIntegerRing_eq_extension_valuationSubring K L w]
  infer_instance

include K in
theorem extensionValuationSubring_henselianLocalRing : HenselianLocalRing w.valuationSubring := by
  rw [← spectralIntegerRing_eq_extension_valuationSubring K L w]
  infer_instance

/-- Monogenicity for any chosen compatible extension valuation, with arbitrary perfect residue. -/
theorem extensionValuationSubring_exists_generator [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] :
    ∃ x : w.valuationSubring, Algebra.adjoin OK {x} = ⊤ := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  have := extensionValuationSubring_henselianLocalRing K L w
  exact exists_integral_generator

end FontaineWintenberger
