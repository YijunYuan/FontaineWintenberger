/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.Uniqueness
public import FontaineWintenberger.Ramification.Lower.Inertia
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Integers of finite Galois fixed fields

We restrict the ambient spectral valuation to the intermediate field.
The chosen-extension theorem supplies its DVR structure. Fraction
field Galois descent then proves the invariant-ring structure needed
by Tate's scaled identity.

## Main results

* `intermediate_spectral_isDiscreteValuationRing`: The restricted spectral valuation ring of any
  intermediate field is a DVR.
* `intermediate_spectral_henselianLocalRing`: The same intermediate integer ring is Henselian.
* `intermediate_spectral_exists_generator`: Integral generators exist in the intermediate integer
  ring.
* `fixedField_integer_moduleFinite`: The top integers are finite over the fixed-field integers.
* `fixedField_integer_isGaloisGroup`: The top integer ring has the fixed-field integers as its
  invariants.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace Valuation.HasExtension

/-- Restriction along a field algebra map is compatible with the ambient valuation. -/
instance comap_algebraMap {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) :
    (v.comap (algebraMap K L)).HasExtension v := ⟨fun _ _ => Iff.rfl⟩

/-- Canonical maps between compatible valuation rings respect the field scalar tower. -/
instance valuationSubring_isScalarTower {K L M ΓK ΓL ΓM : Type*}
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓM]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) (vM : Valuation M ΓM)
    [vK.HasExtension vL] [vL.HasExtension vM] [vK.HasExtension vM] :
    IsScalarTower vK.valuationSubring vL.valuationSubring vM.valuationSubring :=
  ⟨fun a b c => Subtype.ext (smul_assoc (a : K) (b : L) (c : M))⟩

end Valuation.HasExtension

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The two canonical fixed-field presentations give the same Galois group. -/
instance fixedField_isGaloisGroup (H : Subgroup (L ≃ₐ[K] L)) :
    IsGaloisGroup H (fixedField H) L := by
  apply IsGaloisGroup.of_fixedPoints_eq (L ≃ₐ[K] L) K L H (fixedField H)
  ext x
  rfl

end IntermediateField

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The restricted spectral valuation extends the base valuation. -/
instance intermediate_spectral_hasExtension (F : IntermediateField K L) :
    (NormedField.valuation (K := K)).HasExtension
      ((spectralValuation K L).comap (algebraMap F L)) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply K F L,
      spectralValuation_algebraMap, NormedField.valuation_apply]

/-- The restricted spectral valuation ring of any intermediate field is a DVR. -/
theorem intermediate_spectral_isDiscreteValuationRing (F : IntermediateField K L) :
    IsDiscreteValuationRing
      ((spectralValuation K L).comap (algebraMap F L)).valuationSubring :=
  extensionValuationSubring_isDiscreteValuationRing K F
    ((spectralValuation K L).comap (algebraMap F L))

/-- The same intermediate integer ring is Henselian. -/
theorem intermediate_spectral_henselianLocalRing (F : IntermediateField K L) :
    HenselianLocalRing ((spectralValuation K L).comap (algebraMap F L)).valuationSubring :=
  extensionValuationSubring_henselianLocalRing K F
    ((spectralValuation K L).comap (algebraMap F L))

/-- Integral generators exist in the intermediate integer ring. -/
theorem intermediate_spectral_exists_generator [PerfectField 𝓀[K]] (F : IntermediateField K L) :
    ∃ y : ((spectralValuation K L).comap (algebraMap F L)).valuationSubring,
      Algebra.adjoin 𝒪[K] {y} = ⊤ :=
  extensionValuationSubring_exists_generator K F
    ((spectralValuation K L).comap (algebraMap F L))

variable (H : Subgroup (L ≃ₐ[K] L))

local notation "F" => IntermediateField.fixedField H
local notation "A" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F L) (spectralValuation K L))
local notation "B" => spectralIntegerRing K L

/-- The top integers are finite over the fixed-field integers. -/
theorem fixedField_integer_moduleFinite : Module.Finite A B :=
  Module.Finite.of_restrictScalars_finite 𝒪[K] A B

/-- The top integer ring has the fixed-field integers as its invariants. -/
theorem fixedField_integer_isGaloisGroup : IsGaloisGroup H A B := by
  have : IsDiscreteValuationRing A := intermediate_spectral_isDiscreteValuationRing K L F
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top 𝒪[K]
  have : SMulDistribClass H B L := {
    smul_distrib_smul := fun h x z => by
      change (h : L ≃ₐ[K] L) ((x : L) * z) = ((h • x : B) : L) * (h : L ≃ₐ[K] L) z
      exact map_mul (h : L ≃ₐ[K] L) (x : L) z }
  exact IsGaloisGroup.of_isFractionRing H A B F L

end FontaineWintenberger
