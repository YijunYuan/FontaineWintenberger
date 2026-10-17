module

public import FontaineWintenberger.LocalField.SpectralIntegers
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Valuation rings of finite separable extensions

The spectral unit ball is the actual integral closure of the base unit ball.
Integral-closure finiteness and the valuation-ring structure prove it is a DVR,
without any finiteness hypothesis on the residue field.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L

variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]

instance spectralIntegerRing_moduleFinite : Module.Finite OK OL :=
  IsIntegralClosure.finite (A := OK) (K := K) (L := L) (C := OL)

instance spectralIntegerRing_moduleFree : Module.Free OK OL :=
  IsIntegralClosure.module_free OK K L OL

theorem spectralIntegerRing_finrank : Module.finrank OK OL = Module.finrank K L :=
  IsIntegralClosure.rank OK K L OL

instance spectralIntegerRing_isNoetherianRing : IsNoetherianRing OL :=
  IsNoetherianRing.of_finite OK OL

theorem spectralIntegerRing_not_isField : ¬ IsField OL := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  intro hm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible OK
  have hmem : algebraMap OK OL π ∈ IsLocalRing.maximalIdeal OL :=
    map_nonunit (algebraMap OK OL) π hπ.not_isUnit
  have hz : algebraMap OK OL π = 0 := by simpa [hm] using hmem
  apply hπ.ne_zero
  apply FaithfulSMul.algebraMap_injective OK OL
  exact hz.trans (map_zero _).symm

instance spectralIntegerRing_isDiscreteValuationRing : IsDiscreteValuationRing OL := by
  have h : ValuationRing OL := inferInstance
  exact ((IsDiscreteValuationRing.TFAE OL (spectralIntegerRing_not_isField K L)).out 2 1).mp h

end FontaineWintenberger
