/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.APF.RamificationBound
public import FontaineWintenberger.LocalField.Residue.Basic
public import FontaineWintenberger.LocalField.Spectral.Tower
public import FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField

/-!
# Relative Herbrand invariants of finite intermediate fields

The smaller field carries the spectral norm over the original base. The ambient separable
extension may be infinite and need not carry a norm.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger.FiniteIntermediateField

section SpectralNorm

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local instance instNontriviallyNormedField (E : FiniteIntermediateField K L) :
    NontriviallyNormedField E.val :=
  spectralNorm.nontriviallyNormedField K E.val

local instance instNormedAlgebra (E : FiniteIntermediateField K L) : NormedAlgebra K E.val :=
  spectralNorm.normedAlgebra K E.val

local instance instIsUltrametricDist (E : FiniteIntermediateField K L) : IsUltrametricDist E.val :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))

local instance instCompleteSpace (E : FiniteIntermediateField K L) : CompleteSpace E.val :=
  spectralNorm.completeSpace K E.val

local instance instIsCompleteDiscreteValuedField (E : FiniteIntermediateField K L) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val

end SpectralNorm

section PerfectResidue

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

attribute [local instance] instNontriviallyNormedField instNormedAlgebra instIsUltrametricDist

local instance instIsPerfectResidueLocalField (E : FiniteIntermediateField K L) :
    IsPerfectResidueLocalField E.val :=
  normedAlgebra_isPerfectResidueLocalField K E.val

end PerfectResidue

attribute [local instance] instNontriviallyNormedField instNormedAlgebra instIsUltrametricDist
  instCompleteSpace instIsCompleteDiscreteValuedField

variable {K L : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The first ramification bound of the finite extension defined by an inclusion. -/
abbrev relativeRamificationBound {E F : FiniteIntermediateField K L} (hEF : E ≤ F) : EReal :=
  apfRamificationBound E.val (IntermediateField.extendScalars hEF)

/-- The inverse Herbrand function of a finite inclusion, using the spectral norm on its base. -/
abbrev relativePhi {E F : FiniteIntermediateField K L} (hEF : E ≤ F) : ℝ → ℝ :=
  let F' := IntermediateField.extendScalars hEF
  letI : FiniteDimensional K F' := F.property
  letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  apfPhi E.val F'

/-- The Herbrand function of the ambient extension over its finite intermediate field. -/
abbrev ambientPsi (E : FiniteIntermediateField K L) : ℝ → ℝ :=
  letI := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
  apfPsi E.val L

end FontaineWintenberger.FiniteIntermediateField
