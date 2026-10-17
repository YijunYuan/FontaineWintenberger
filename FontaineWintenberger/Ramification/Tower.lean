module

public import FontaineWintenberger.Ramification.Index
public import FontaineWintenberger.LocalField.Uniqueness
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Valuation.Extension

/-!
# Normalized field valuations and ramification indices in towers

The normalized field formula specializes Mathlib's adic valuation theorem.
It uses the actual maximal ideals and canonical local-length ramification index.
-/

@[expose] public section

namespace FontaineWintenberger

section FractionFields

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [IsScalarTower R K L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]

local notation "vR" => IsDedekindDomain.HeightOneSpectrum.valuation K
  (IsDiscreteValuationRing.maximalIdeal R)
local notation "vS" => IsDedekindDomain.HeightOneSpectrum.valuation L
  (IsDiscreteValuationRing.maximalIdeal S)

/-- The normalized field valuation restricts by the canonical ramification-index power. -/
theorem normalizedValuation_algebraMap (x : K) :
    vS (algebraMap K L x) = vR x ^ (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  have : (IsDiscreteValuationRing.maximalIdeal S).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal :=
    (inferInstance : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R))
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L
    (IsDiscreteValuationRing.maximalIdeal R) (IsDiscreteValuationRing.maximalIdeal S) x).symm

/-- The canonical normalized field valuations are compatible as valuations. -/
instance normalizedValuation_hasExtension : (vR).HasExtension (vS) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, normalizedValuation_algebraMap R S K L]
    exact (pow_le_pow_iff_left₀ zero_le zero_le
      (local_ramificationIdx_pos R S).ne').symm

end FractionFields

section Tower

variable (R S T : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [FaithfulSMul S T] [IsLocalHom (algebraMap S T)]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Canonical ramification indices multiply in a tower of local DVR maps. -/
theorem local_ramificationIdx_tower :
    (IsLocalRing.maximalIdeal T).ramificationIdx R =
      (IsLocalRing.maximalIdeal S).ramificationIdx R *
        (IsLocalRing.maximalIdeal T).ramificationIdx S :=
  Ideal.ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal T)

end Tower

section ChosenExtension

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
variable [(NormedField.valuation (K := K)).HasExtension w]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => Valuation.valuationSubring w

/-- The index ideal identity for an actual chosen finite-extension valuation ring. -/
theorem extensionValuationSubring_map_maximalIdeal :
    (IsLocalRing.maximalIdeal OK).map (algebraMap OK OL) =
      IsLocalRing.maximalIdeal OL ^ (IsLocalRing.maximalIdeal OL).ramificationIdx OK := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact map_maximalIdeal_eq_pow_ramificationIdx OK OL

/-- Normalized numerical scaling on the actual source and chosen extension fields. -/
theorem extensionValuationSubring_normalizedValuation_algebraMap (x : K) :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    (IsDiscreteValuationRing.maximalIdeal OL).valuation L (algebraMap K L x) =
      ((IsDiscreteValuationRing.maximalIdeal OK).valuation K x) ^
        (IsLocalRing.maximalIdeal OL).ramificationIdx OK := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact normalizedValuation_algebraMap OK OL K L x

end ChosenExtension

end FontaineWintenberger
