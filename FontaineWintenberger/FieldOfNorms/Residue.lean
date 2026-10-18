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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteLayer K L)

local notation "𝔈" => deepFiniteTower K L p D
local notation "𝔅" => deepFiniteTowerQuotient K L p D
local notation "𝒜" => deepNormInverseLimit K L p D

/-- Each actual integral truncated coordinate is onto, by the actual
surjective norm tower and the proved reconstruction equivalence. -/
theorem normLimitTruncation_surjective (n : ℕ) :
    letI := normLimitField K L p
    Function.Surjective (normLimitTruncation K L p D n) := by
  let := normLimitField K L p
  let q (i : ℕ) := deepFiniteTowerTransition K L p D i (i + 1) (Nat.le_succ i)
  have hs (i : ℕ) : Function.Surjective (q i) :=
    deepFiniteTowerTransition_surjective K L p D i (i + 1) (Nat.le_succ i)
  intro b
  obtain ⟨a, ha⟩ := SequentialInverseLimit.projection_surjective 𝔅 q hs n b
  obtain ⟨α, hα⟩ := (normLimitTruncationEquiv K L p D).surjective a
  refine ⟨α, ?_⟩
  change a.val n = b at ha
  exact (congrArg (fun z : 𝒜 => z.val n) hα).trans ha

/-- Reduction of the actual first original coordinate, factored through
its checked quotient by the square of the maximal ideal. -/
def normLimitResidueReduction :
    letI := normLimitField K L p
    (normLimitFieldValuation K L p).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  letI := normLimitField K L p
  exact (Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))).comp
    (normLimitTruncation K L p D 0)

/-- This reduction is the residue of the original finite-field coordinate. -/
@[simp]
theorem normLimitResidueReduction_apply :
    letI := normLimitField K L p
    ∀ α : (normLimitFieldValuation K L p).valuationSubring,
    normLimitResidueReduction K L p D α =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L p D α 0) := by
  let := normLimitField K L p
  intro α
  rfl

/-- Actual coordinate reduction is onto the original first-stage residue field. -/
theorem normLimitResidueReduction_surjective :
    letI := normLimitField K L p
    Function.Surjective (normLimitResidueReduction K L p D) := by
  let := normLimitField K L p
  intro z
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
  obtain ⟨α, hα⟩ := normLimitTruncation_surjective K L p D 0
    (Ideal.Quotient.mk _ x)
  refine ⟨α, ?_⟩
  change Ideal.Quotient.factor (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0))
    (normLimitTruncation K L p D 0 α) = z
  rw [hα, Ideal.Quotient.factor_mk]
  exact hx

/-- The kernel is exactly the maximal ideal of the same original norm-limit
valuation ring, by the proved equality of its normalized valuation. -/
theorem normLimitResidueReduction_ker :
    letI := normLimitField K L p
    RingHom.ker (normLimitResidueReduction K L p D) =
      IsLocalRing.maximalIdeal (normLimitFieldValuation K L p).valuationSubring := by
  let := normLimitField K L p
  let := normLimitFieldValuation_isDiscreteValuationRing K L p
  ext α
  change normLimitResidueReduction K L p D α = 0 ↔ _
  rw [normLimitResidueReduction_apply, IsLocalRing.residue_eq_zero_iff]
  conv_lhs => rw [← pow_one (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 0).val))]
  conv_rhs => rw [← pow_one (IsLocalRing.maximalIdeal
    (normLimitFieldValuation K L p).valuationSubring)]
  rw [ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation,
    normLimitFieldValuation_eq_normalized]
  change _ ↔ normLimitValuation K L α.val ≤ _
  rw [normLimitValuation_eq_deepFiniteTower K L p D 0]
  rfl

/-- The actual coordinate reduction descends through the original maximal
ideal to the original first-stage residue field. -/
def normLimitResidueToLayer :
    letI := normLimitField K L p
    IsLocalRing.ResidueField (normLimitFieldValuation K L p).valuationSubring →+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  letI := normLimitField K L p
  exact Ideal.Quotient.lift _ (normLimitResidueReduction K L p D)
    (fun α hα => by
      change α ∈ RingHom.ker (normLimitResidueReduction K L p D)
      rw [normLimitResidueReduction_ker]
      exact hα)

/-- The descended map acts on the actual residue of an original integral family. -/
@[simp]
theorem normLimitResidueToLayer_residue :
    letI := normLimitField K L p
    ∀ α : (normLimitFieldValuation K L p).valuationSubring,
    normLimitResidueToLayer K L p D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L p D α 0) := by
  let := normLimitField K L p
  intro α
  rfl

/-- The original norm-limit residue field is identified with the original
deep stage's residue field by the actual coordinate-reduction map. -/
def normLimitResidueLayerEquiv :
    letI := normLimitField K L p
    IsLocalRing.ResidueField (normLimitFieldValuation K L p).valuationSubring ≃+*
      IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 0).val) := by
  letI := normLimitField K L p
  refine RingEquiv.ofBijective (normLimitResidueToLayer K L p D)
    ⟨(normLimitResidueToLayer K L p D).injective, ?_⟩
  intro z
  obtain ⟨α, hα⟩ := normLimitResidueReduction_surjective K L p D z
  exact ⟨IsLocalRing.residue _ α, hα⟩

/-- The residue equivalence retains the actual original finite coordinate. -/
@[simp]
theorem normLimitResidueLayerEquiv_residue :
    letI := normLimitField K L p
    ∀ α : (normLimitFieldValuation K L p).valuationSubring,
    normLimitResidueLayerEquiv K L p D (IsLocalRing.residue _ α) =
      IsLocalRing.residue _ (normLimitIntegralCoordinate K L p D α 0) := by
  let := normLimitField K L p
  intro α
  rfl

/-- Above the proved APF residue-stable layer, actual coordinate reduction
identifies the original norm-limit residue field with the intrinsic residue
field of the canonical integral closure in the original extension. -/
def normLimitResidueEquiv :
    letI := normLimitField K L p
    IsLocalRing.ResidueField (normLimitFieldValuation K L p).valuationSubring ≃+*
      IsLocalRing.ResidueField
        (integralClosure (NormedField.valuation (K := K)).valuationSubring L) := by
  letI := normLimitField K L p
  let T := apfResidueLayer K L
  let E := deepFiniteTower K L p T 0
  exact (normLimitResidueLayerEquiv K L p T).trans
    (integralClosureResidueEquiv K L E
      (le_deepFiniteTower K L p T 0)).toRingEquiv

/-- On residues of actual integral norm families, the intrinsic residue
isomorphism is the original finite residue inclusion after coordinate reduction. -/
@[simp]
theorem normLimitResidueEquiv_residue :
    letI := normLimitField K L p
    ∀ α : (normLimitFieldValuation K L p).valuationSubring,
    normLimitResidueEquiv K L p (IsLocalRing.residue _ α) =
      integralClosureResidueFromLayer K L
        (deepFiniteTower K L p (apfResidueLayer K L) 0)
        (IsLocalRing.residue _ (normLimitIntegralCoordinate K L p
          (apfResidueLayer K L) α 0)) := by
  let := normLimitField K L p
  intro α
  rfl

/-- The actual original norm-limit residue field is perfect, with no finite
residue-field hypothesis. -/
theorem normLimitResidue_perfectField :
    letI := normLimitField K L p
    PerfectField (IsLocalRing.ResidueField
      (normLimitFieldValuation K L p).valuationSubring) := by
  let := normLimitField K L p
  let := IsAPF.perfectField_integralClosureResidue K L
  exact PerfectField.of_ringEquiv (normLimitResidueEquiv K L p).symm

end FontaineWintenberger
