/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Truncation
public import FontaineWintenberger.FieldOfNorms.Uniformizer
public import FontaineWintenberger.LocalField.AlgebraicResidue

/-!
# The residue field of the original norm limit

Reduction of an original deep coordinate identifies the residue field of the
actual norm-limit valuation ring with that of the original algebraic extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteLayer K L)

local notation "𝔈" => deepFiniteTower K L D
local notation "𝔅" => deepFiniteTowerQuotient K L D
local notation "𝒜" => deepNormInverseLimit K L D

/-- Each actual integral truncated coordinate is onto, by the actual
surjective norm tower and the proved reconstruction equivalence. -/
theorem normLimitTruncation_surjective (n : ℕ) :
    Function.Surjective (normLimitTruncation K L D n) := by
  let q (i : ℕ) := deepFiniteTowerTransition K L D i (i + 1) (Nat.le_succ i)
  have hs (i : ℕ) : Function.Surjective (q i) :=
    deepFiniteTowerTransition_surjective K L D i (i + 1) (Nat.le_succ i)
  intro b
  obtain ⟨a, ha⟩ := SequentialInverseLimit.projection_surjective 𝔅 q hs n b
  obtain ⟨α, hα⟩ := (normLimitTruncationEquiv K L D).surjective a
  refine ⟨α, ?_⟩
  change a.val n = b at ha
  exact (congrArg (fun z : 𝒜 => z.val n) hα).trans ha

/-- Reduction of the actual first original coordinate, factored through
its checked quotient by the square of the maximal ideal. -/
def normLimitResidueReduction :
    (normLimitFieldValuation K L).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  exact (Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))).comp
    (normLimitTruncation K L D 0)

/-- This reduction is the residue of the original finite-field coordinate. -/
@[simp]
theorem normLimitResidueReduction_apply :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
    normLimitResidueReduction K L D α =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L D α 0) := by
  intro α
  rfl

/-- Actual coordinate reduction is onto the original first-stage residue field. -/
theorem normLimitResidueReduction_surjective :
    Function.Surjective (normLimitResidueReduction K L D) := by
  intro z
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
  obtain ⟨α, hα⟩ := normLimitTruncation_surjective K L D 0
    (Ideal.Quotient.mk _ x)
  refine ⟨α, ?_⟩
  change Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))
    (normLimitTruncation K L D 0 α) = z
  rw [hα, Ideal.Quotient.factor_mk]
  exact hx

/-- The kernel is exactly the maximal ideal of the same original norm-limit
valuation ring, by the proved equality of its normalized valuation. -/
theorem normLimitResidueReduction_ker :
    RingHom.ker (normLimitResidueReduction K L D) =
      IsLocalRing.maximalIdeal (normLimitFieldValuation K L).valuationSubring := by
  ext α
  change normLimitResidueReduction K L D α = 0 ↔ _
  rw [normLimitResidueReduction_apply, IsLocalRing.residue_eq_zero_iff]
  conv_lhs => rw [← pow_one (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 0).val))]
  conv_rhs => rw [← pow_one (IsLocalRing.maximalIdeal
    (normLimitFieldValuation K L).valuationSubring)]
  rw [ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    normLimitFieldValuation_eq_normalized]
  change _ ↔ normLimitValuation K L α.val ≤ _
  rw [normLimitValuation_eq_deepFiniteTower K L D 0]
  rfl

/-- The actual coordinate reduction descends through the original maximal
ideal to the original first-stage residue field. -/
def normLimitResidueToLayer :
    IsLocalRing.ResidueField (normLimitFieldValuation K L).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  exact Ideal.Quotient.lift _ (normLimitResidueReduction K L D)
    (fun α hα => by
      change α ∈ RingHom.ker (normLimitResidueReduction K L D)
      rw [normLimitResidueReduction_ker]
      exact hα)

/-- The descended map acts on the actual residue of an original integral family. -/
@[simp]
theorem normLimitResidueToLayer_residue :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
    normLimitResidueToLayer K L D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L D α 0) := by
  intro α
  rfl

/-- The original norm-limit residue field is identified with the original
deep stage's residue field by the actual coordinate-reduction map. -/
def normLimitResidueLayerEquiv :
    IsLocalRing.ResidueField (normLimitFieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  refine RingEquiv.ofBijective (normLimitResidueToLayer K L D)
    ⟨(normLimitResidueToLayer K L D).injective, ?_⟩
  intro z
  obtain ⟨α, hα⟩ := normLimitResidueReduction_surjective K L D z
  exact ⟨IsLocalRing.residue _ α, hα⟩

/-- The residue equivalence retains the actual original finite coordinate. -/
@[simp]
theorem normLimitResidueLayerEquiv_residue :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
    normLimitResidueLayerEquiv K L D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L D α 0) := by
  intro α
  rfl

/-- Above the proved APF residue-stable layer, actual coordinate reduction
identifies the original norm-limit residue field with the intrinsic residue
field of the canonical integral closure in the original extension. -/
def normLimitResidueEquiv :
    IsLocalRing.ResidueField (normLimitFieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField
        (integralClosure (NormedField.valuation (K := K)).valuationSubring L) := by
  let T := apfResidueLayer K L
  let E := deepFiniteTower K L T 0
  exact (normLimitResidueLayerEquiv K L T).trans
    (integralClosureResidueEquiv K L E
      (le_deepFiniteTower K L T 0)).toRingEquiv

/-- On residues of actual integral norm families, the intrinsic residue
isomorphism is the original finite residue inclusion after coordinate reduction. -/
@[simp]
theorem normLimitResidueEquiv_residue :
    ∀ α : (normLimitFieldValuation K L).valuationSubring,
    normLimitResidueEquiv K L (IsLocalRing.residue _ α) =
      integralClosureResidueFromLayer K L
        (deepFiniteTower K L (apfResidueLayer K L) 0)
        (IsLocalRing.residue _ (normLimitIntegralCoordinate K L
          (apfResidueLayer K L) α 0)) := by
  intro α
  rfl

/-- The actual original norm-limit residue field is perfect, with no finite
residue-field hypothesis. -/
instance normLimitResidue_perfectField :
    PerfectField (IsLocalRing.ResidueField
      (normLimitFieldValuation K L).valuationSubring) := by
  let := IsAPF.perfectField_integralClosureResidue K L
  exact PerfectField.of_ringEquiv (normLimitResidueEquiv K L).symm

end FontaineWintenberger
