module

public import FontaineWintenberger.LocalField.NormedTower
public import FontaineWintenberger.LocalField.FullGalois

/-!
# Actual spectral integers after changing a finite base

Compatible norms identify both spectral constructions with the same actual
unit ball. The identity intertwines the actual fixing-subgroup actions.
-/

@[expose] public section

namespace FontaineWintenberger

section CompatibleNorm

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [Algebra.IsAlgebraic K L]

/-- The spectral integer subring is the actual unit ball of any compatible field norm. -/
theorem spectralIntegerRing_eq_normedUnitBall :
    spectralIntegerRing K L = (NormedField.valuation (K := L)).valuationSubring := by
  ext x
  change spectralNorm K L x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm K]

end CompatibleNorm

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (E : Type*) [NontriviallyNormedField E] [NormedAlgebra K E] [IsUltrametricDist E]
    [Algebra.IsAlgebraic K E]
variable (M : IntermediateField K E) [FiniteDimensional K M]

local instance : CompleteSpace M := FiniteDimensional.complete K M

/-- Both base fields construct the same actual integer subring of the top field. -/
theorem finiteBase_spectralIntegerRing_eq :
    spectralIntegerRing K E = spectralIntegerRing M E :=
  (spectralIntegerRing_eq_normedUnitBall K E).trans
    (spectralIntegerRing_eq_normedUnitBall M E).symm

/-- The identity on field elements identifies the two actual integer rings. -/
noncomputable def finiteBase_spectralIntegerRingEquiv :
    spectralIntegerRing K E ≃+* spectralIntegerRing M E :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (finiteBase_spectralIntegerRing_eq K E M))

@[simp]
theorem coe_finiteBase_spectralIntegerRingEquiv (x : spectralIntegerRing K E) :
    (finiteBase_spectralIntegerRingEquiv K E M x : E) = x := rfl

/-- The fixing-subgroup equivalence uses the very same action on the top integer ring. -/
theorem finiteBase_spectralIntegerRingEquiv_smul (g : M.fixingSubgroup)
    (x : spectralIntegerRing K E) :
    finiteBase_spectralIntegerRingEquiv K E M (g • x) =
      M.fixingSubgroupEquiv g • finiteBase_spectralIntegerRingEquiv K E M x := by
  apply Subtype.ext
  rfl

end FontaineWintenberger
