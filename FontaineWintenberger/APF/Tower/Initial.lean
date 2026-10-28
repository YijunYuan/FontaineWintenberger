/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Criterion
public import FontaineWintenberger.APF.Tower.Tame

/-!
# The unramified and tame initial stages of the elementary tower

Wintenberger's `K₀` and `K₁` are the existing `apfMaximalUnramified` and `apfMaximalTame`.
The former is unramified over the ground field. The latter is totally ramified over `K₀`
and its relative degree is prime to the residue characteristic.

The first ramification bound of every proper elementary step is its elementary level.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1(a)–(b).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section InitialStages

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]

/-- The initial unramified stage has ramification index one over the ground field. -/
theorem apfMaximalUnramified_ramificationIdx :
    (IsLocalRing.maximalIdeal
      (spectralIntegerRing K (apfMaximalUnramified K L).val)).ramificationIdx 𝒪[K] = 1 :=
  (le_apfMaximalUnramified_iff K L _).mp le_rfl

/-- The initial tame stage is totally ramified over the initial unramified stage. -/
theorem apfMaximalTame_relative_ramificationIdx :
    let E := apfMaximalUnramified K L
    let F := apfMaximalTame K L
    let hEF := apfMaximalUnramified_le_maximalTame K L
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
        (spectralIntegerRing K E.val) =
      Module.finrank E.val (IntermediateField.extendScalars hEF) :=
  FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective K L
    (apfMaximalUnramified K L) (apfMaximalTame K L)
    (apfMaximalUnramified_le_maximalTame K L)
    (spectralResidueInclusion_surjective_of_apfMaximalUnramified_le K L _ _ le_rfl
      (apfMaximalUnramified_le_maximalTame K L))

/-- The degree of the tame initial step is the absolute ramification index of its top
field, since its base is unramified. -/
theorem apfMaximalTame_relative_finrank :
    Module.finrank (apfMaximalUnramified K L).val
        (IntermediateField.extendScalars (apfMaximalUnramified_le_maximalTame K L)) =
      (IsLocalRing.maximalIdeal
        (spectralIntegerRing K (apfMaximalTame K L).val)).ramificationIdx 𝒪[K] := by
  let E := apfMaximalUnramified K L
  let F := apfMaximalTame K L
  let hEF := apfMaximalUnramified_le_maximalTame K L
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have ht := local_ramificationIdx_tower 𝒪[K]
    (spectralIntegerRing K E.val) (spectralIntegerRing K F.val)
  rw [apfMaximalUnramified_ramificationIdx K L, one_mul,
    apfMaximalTame_relative_ramificationIdx K L] at ht
  exact ht.symm

/-- The totally ramified initial tame step has degree prime to the residue characteristic. -/
theorem apfMaximalTame_relative_finrank_coprime :
    Nat.Coprime (residueChar K)
      (Module.finrank (apfMaximalUnramified K L).val
        (IntermediateField.extendScalars (apfMaximalUnramified_le_maximalTame K L))) := by
  rw [apfMaximalTame_relative_finrank]
  exact (le_apfMaximalTame_iff K L _).mp le_rfl

end InitialStages

section ElementaryStep

variable {K : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {E F : FiniteIntermediateField K (SeparableClosure K)} {i : ℝ}

/-- The first ramification bound of a proper elementary step is its elementary level. -/
theorem IsElementaryStep.apfRamificationBound_eq (hEF : E < F)
    (h : IsElementaryStep K E F hEF.le i) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
    apfRamificationBound E.val (IntermediateField.extendScalars hEF.le) = (i : EReal) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  change IsElementary E.val (IntermediateField.extendScalars hEF.le) i at h
  let := h.finite
  apply h.apfRamificationBound_eq
  have hp := Module.finrank_pos (R := E.val) (M := IntermediateField.extendScalars hEF.le)
  have hn : Module.finrank E.val (IntermediateField.extendScalars hEF.le) ≠ 1 := by
    intro he
    apply hEF.not_ge
    exact IntermediateField.relfinrank_eq_one_iff.mp
      ((IntermediateField.relfinrank_eq_finrank_of_le hEF.le).trans he)
  omega

end ElementaryStep

end FontaineWintenberger
