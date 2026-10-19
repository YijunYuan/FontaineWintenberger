/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.Uniqueness
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual normed fields and intermediate towers

Normed algebra maps preserve the field norm, so the actual norm valuations
are compatible. An intermediate field keeps the ambient norm and uniformity;
finite-dimensional completeness and the chosen-extension integer theorems
therefore apply directly to its actual unit ball.
-/

@[expose] public section

namespace NormedField

variable (K L : Type*) [NormedField K] [NormedField L] [NormedAlgebra K L]
    [IsUltrametricDist K] [IsUltrametricDist L]

/-- A normed field algebra is an extension of the actual norm valuations. -/
instance valuation_hasExtension :
    (valuation (K := K)).HasExtension (valuation (K := L)) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, valuation_apply, nnnorm_algebraMap, nnnorm_one, mul_one]

end NormedField

namespace IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]

/-- The ambient field is a normed algebra over an intermediate field with its inherited norm. -/
instance normedAlgebraAmbient (F : IntermediateField K L) : NormedAlgebra F L where
  norm_smul_le r x := by
    change ‖(r : L) * x‖ ≤ ‖(r : L)‖ * ‖x‖
    exact (norm_mul (r : L) x).le

/-- Finite intermediate fields are complete for their actual inherited uniformity. -/
theorem completeSpace_of_finiteDimensional [CompleteSpace K] [FiniteDimensional K L]
    (F : IntermediateField K L) : CompleteSpace F := FiniteDimensional.complete K F

end IntermediateField

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- DVR structure for the actual norm unit ball of a chosen normed field extension. -/
theorem normedAlgebra_unitBall_isDiscreteValuationRing :
    IsDiscreteValuationRing (NormedField.valuation (K := L)).valuationSubring :=
  extensionValuationSubring_isDiscreteValuationRing K L (NormedField.valuation (K := L))

include K in
/-- Henselianity for that actual norm unit ball. -/
theorem normedAlgebra_unitBall_henselianLocalRing :
    HenselianLocalRing (NormedField.valuation (K := L)).valuationSubring :=
  extensionValuationSubring_henselianLocalRing K L (NormedField.valuation (K := L))

/-- The actual norm unit ball is generated over the actual base unit ball. -/
theorem normedAlgebra_unitBall_exists_generator [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] :
    ∃ x : (NormedField.valuation (K := L)).valuationSubring,
      Algebra.adjoin (NormedField.valuation (K := K)).valuationSubring {x} = ⊤ :=
  extensionValuationSubring_exists_generator K L (NormedField.valuation (K := L))

/-- A finite separable normed extension of a complete discretely valued field is again one. -/
theorem normedAlgebra_isCompleteDiscreteValuedField (K L : Type*) [NontriviallyNormedField K]
    [IsCompleteDiscreteValuedField K] [NontriviallyNormedField L] [IsUltrametricDist L]
    [NormedAlgebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsCompleteDiscreteValuedField L :=
  have : CompleteSpace L := FiniteDimensional.complete K L
  have := normedAlgebra_unitBall_isDiscreteValuationRing K L
  {}

end FontaineWintenberger
