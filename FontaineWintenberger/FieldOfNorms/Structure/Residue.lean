/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Truncation
public import FontaineWintenberger.FieldOfNorms.Structure.Uniformizer
public import FontaineWintenberger.APF.Tower.AlgebraicResidue

/-!
# The residue field of the field of norms

Reduction of a deep coordinate identifies the residue field of the
field of norms valuation ring with that of the algebraic extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteIntermediateField K L)

local notation "𝔈" => deepFiniteTower K L D
local notation "𝔅" => deepFiniteTowerQuotient K L D
local notation "𝒜" => deepNormInverseLimit K L D

/-- Each integral truncated coordinate is onto, by the
surjective norm tower and the proved reconstruction equivalence. -/
theorem FieldOfNorms.truncation_surjective (n : ℕ) :
    Function.Surjective (FieldOfNorms.truncation K L D n) := by
  let q (i : ℕ) := deepFiniteTowerTransition K L D i (i + 1) (Nat.le_succ i)
  have hs (i : ℕ) : Function.Surjective (q i) :=
    deepFiniteTowerTransition_surjective K L D i (i + 1) (Nat.le_succ i)
  intro b
  obtain ⟨a, ha⟩ := SequentialInverseLimit.projection_surjective 𝔅 q hs n b
  obtain ⟨α, hα⟩ := (FieldOfNorms.truncationEquiv K L D).surjective a
  refine ⟨α, ?_⟩
  change a.val n = b at ha
  exact (congrArg (fun z : 𝒜 => z.val n) hα).trans ha

/-- Reduction of the first coordinate, factored through
its checked quotient by the square of the maximal ideal. -/
def FieldOfNorms.residueReduction :
    (FieldOfNorms.fieldValuation K L).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  exact (Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))).comp
    (FieldOfNorms.truncation K L D 0)

/-- This reduction is the residue of the finite-field coordinate. -/
@[simp]
theorem FieldOfNorms.residueReduction_apply :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
    FieldOfNorms.residueReduction K L D α =
      IsLocalRing.residue _ (FieldOfNorms.integralCoordinate K L D α 0) := by
  intro α
  rfl

/-- Coordinate reduction is onto the first-stage residue field. -/
theorem FieldOfNorms.residueReduction_surjective :
    Function.Surjective (FieldOfNorms.residueReduction K L D) := by
  intro z
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
  obtain ⟨α, hα⟩ := FieldOfNorms.truncation_surjective K L D 0
    (Ideal.Quotient.mk _ x)
  refine ⟨α, ?_⟩
  change Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))
    (FieldOfNorms.truncation K L D 0 α) = z
  rw [hα, Ideal.Quotient.factor_mk]
  exact hx

/-- The kernel is exactly the maximal ideal of the field of norms
valuation ring, by the proved equality of its normalized valuation. -/
theorem FieldOfNorms.residueReduction_ker :
    RingHom.ker (FieldOfNorms.residueReduction K L D) =
      IsLocalRing.maximalIdeal (FieldOfNorms.fieldValuation K L).valuationSubring := by
  ext α
  change FieldOfNorms.residueReduction K L D α = 0 ↔ _
  rw [FieldOfNorms.residueReduction_apply, IsLocalRing.residue_eq_zero_iff]
  conv_lhs => rw [← pow_one (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 0).val))]
  conv_rhs => rw [← pow_one (IsLocalRing.maximalIdeal
    (FieldOfNorms.fieldValuation K L).valuationSubring)]
  rw [ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    FieldOfNorms.fieldValuation_eq_normalized]
  change _ ↔ FieldOfNorms.valuation K L α.val ≤ _
  rw [FieldOfNorms.valuation_eq_deepFiniteTower K L D 0]
  rfl

/-- The coordinate reduction descends through the maximal
ideal to the first-stage residue field. -/
def FieldOfNorms.residueToLayer :
    IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  exact Ideal.Quotient.lift _ (FieldOfNorms.residueReduction K L D)
    (fun α hα => by
      change α ∈ RingHom.ker (FieldOfNorms.residueReduction K L D)
      rw [FieldOfNorms.residueReduction_ker]
      exact hα)

/-- The descended map acts on the residue of an integral family. -/
@[simp]
theorem FieldOfNorms.residueToLayer_residue :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
    FieldOfNorms.residueToLayer K L D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (FieldOfNorms.integralCoordinate K L D α 0) := by
  intro α
  rfl

/-- The field of norms residue field is identified with the
deep stage's residue field by the coordinate-reduction map. -/
def FieldOfNorms.residueLayerEquiv :
    IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  refine RingEquiv.ofBijective (FieldOfNorms.residueToLayer K L D)
    ⟨(FieldOfNorms.residueToLayer K L D).injective, ?_⟩
  intro z
  obtain ⟨α, hα⟩ := FieldOfNorms.residueReduction_surjective K L D z
  exact ⟨IsLocalRing.residue _ α, hα⟩

/-- The residue equivalence retains the finite coordinate. -/
@[simp]
theorem FieldOfNorms.residueLayerEquiv_residue :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
    FieldOfNorms.residueLayerEquiv K L D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (FieldOfNorms.integralCoordinate K L D α 0) := by
  intro α
  rfl

/-- Above the proved APF residue-stable layer, coordinate reduction
identifies the field of norms residue field with the intrinsic residue
field of the canonical integral closure in the extension. -/
def FieldOfNorms.residueEquiv :
    IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField
        (integralClosure 𝒪[K] L) := by
  let T := apfResidueLayer K L
  let E := deepFiniteTower K L T 0
  exact (FieldOfNorms.residueLayerEquiv K L T).trans
    (integralClosureResidueEquiv K L E
      (le_deepFiniteTower K L T 0)).toRingEquiv

/-- On residues of integral norm families, the intrinsic residue
isomorphism is the finite residue inclusion after coordinate reduction. -/
@[simp]
theorem FieldOfNorms.residueEquiv_residue :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
    FieldOfNorms.residueEquiv K L (IsLocalRing.residue _ α) =
      integralClosureResidueFromLayer K L
        (deepFiniteTower K L (apfResidueLayer K L) 0)
        (IsLocalRing.residue _ (FieldOfNorms.integralCoordinate K L
          (apfResidueLayer K L) α 0)) := by
  intro α
  rfl

/-- The field of norms residue field is perfect, with no finite
residue-field hypothesis. -/
instance FieldOfNorms.instPerfectFieldResidueField :
    PerfectField (IsLocalRing.ResidueField
      (FieldOfNorms.fieldValuation K L).valuationSubring) := by
  let := IsAPF.perfectField_integralClosureResidue K L
  exact PerfectField.of_ringEquiv (FieldOfNorms.residueEquiv K L).symm

end FontaineWintenberger
