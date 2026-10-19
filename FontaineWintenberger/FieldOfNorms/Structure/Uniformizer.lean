/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Reconstruction
public import FontaineWintenberger.FieldOfNorms.Basic.Ring

/-!
# An actual norm-family uniformizer

A genuine uniformizer class in the first original finite quotient lifts
through the actual surjective norm tower. Reconstruction supplies a family
on the same original field of norms carrier with normalized value one.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- An actual compatible norm family has normalized value one. The family
is reconstructed from a lifted genuine first-stage uniformizer class. -/
theorem exists_fieldOfNormsValuation_eq_exp_neg_one [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∃ πX : FieldOfNorms K L, FieldOfNorms.valuation K L πX = WithZero.exp (-1 : ℤ) := by
  let D : FiniteIntermediateField K L := FiniteIntermediateField.bottom
  let E := deepFiniteTower K L D
  let B := deepFiniteTowerQuotient K L D
  let q (n : ℕ) := deepFiniteTowerTransition K L D n (n + 1) (Nat.le_succ n)
  let R := spectralIntegerRing K (E 0).val
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs (n : ℕ) : Function.Surjective (q n) :=
    deepFiniteTowerTransition_surjective K L D n (n + 1) (Nat.le_succ n)
  obtain ⟨a, ha⟩ := SequentialInverseLimit.projection_surjective B q hs 0 (Ideal.Quotient.mk _ π)
  change a.val 0 = Ideal.Quotient.mk _ π at ha
  let πX := deepNormReconstruction K L D a
  have hπX : FieldOfNorms.valuation K L πX ≤ 1 :=
    deepNormReconstruction_valuation_le_one K L D a
  let z : R := ⟨FieldOfNorms.coord K L (E 0) πX,
    FieldOfNorms.coord_mem_of_valuation_le_one K L πX hπX (E 0)⟩
  let x := deepNormRepresentative K L D a 0
  obtain ⟨d, hd, heq⟩ := deepNormReconstruction_sub_mem K L D a 0
  have hzd : z - x = d := Subtype.ext heq.symm
  have hz : z - x ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    rw [hzd]
    exact hd
  have hclass : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ 2) z =
      Ideal.Quotient.mk _ π :=
    (Ideal.Quotient.eq.mpr hz).trans
      ((deepNormRepresentative_mk K L D a 0).trans ha)
  have ht := congrArg (truncatedAddVal R 2) hclass
  rw [truncatedAddVal_mk, truncatedAddVal_mk, IsDiscreteValuationRing.addVal_uniformizer hπ] at ht
  have ht' : min (IsDiscreteValuationRing.addVal R z) 2 = 1 := by simpa using ht
  have hzval : IsDiscreteValuationRing.addVal R z = 1 := by
    rcases min_eq_iff.mp ht' with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  refine ⟨πX, ?_⟩
  rw [FieldOfNorms.valuation_eq_deepFiniteTower K L D 0]
  change (IsDiscreteValuationRing.maximalIdeal R).valuation (E 0).val (algebraMap R (E 0).val z) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal, hzval]
  rfl

/-- A chosen actual original norm-compatible family with normalized value one. -/
def FieldOfNorms.uniformizer [IsAPF K L] [Fact (¬ Module.Finite K L)] : FieldOfNorms K L :=
  (exists_fieldOfNormsValuation_eq_exp_neg_one K L).choose

@[simp]
theorem FieldOfNorms.valuation_fieldOfNormsUniformizer [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    FieldOfNorms.valuation K L (FieldOfNorms.uniformizer K L) =
      WithZero.exp (-1 : ℤ) :=
  (exists_fieldOfNormsValuation_eq_exp_neg_one K L).choose_spec

/-- The actual reconstructed uniformizer is a nonzero original norm family. -/
theorem FieldOfNorms.uniformizer_ne_zero [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    FieldOfNorms.uniformizer K L ≠ 0 := by
  intro h
  have hv := FieldOfNorms.valuation_fieldOfNormsUniformizer K L
  rw [h, _root_.map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- All original integer powers have their exact original normalized values. -/
theorem FieldOfNorms.uniformizer_zpow_valuation [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (m : ℤ) :
    FieldOfNorms.valuation K L (FieldOfNorms.uniformizer K L ^ m) =
      WithZero.exp (-m) := by
  rw [map_zpow₀, FieldOfNorms.valuation_fieldOfNormsUniformizer, ← WithZero.exp_zsmul]
  congr 1
  simp

/-- The same original stable valuation attains every normalized integer value and zero. -/
theorem FieldOfNorms.valuation_surjective [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Function.Surjective (FieldOfNorms.valuation K L) := by
  intro a
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, _root_.map_zero _⟩
  | coe a =>
      refine ⟨FieldOfNorms.uniformizer K L ^ (-Multiplicative.toAdd a), ?_⟩
      rw [FieldOfNorms.uniformizer_zpow_valuation, neg_neg]
      rfl

/-- Bundling the same original map as a field valuation preserves its proved surjectivity. -/
theorem FieldOfNorms.fieldValuation_surjective [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    Function.Surjective (FieldOfNorms.fieldValuation K L) := by
  exact FieldOfNorms.valuation_surjective K L

/-- The value group of the actual original field valuation is the entire integer group. -/
theorem FieldOfNorms.fieldValuation_valueGroup_eq_top [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    (FieldOfNorms.fieldValuation K L).valueGroup = ⊤ := by
  apply top_unique
  intro a _ha
  apply MonoidWithZeroHom.mem_valueGroup
  exact FieldOfNorms.valuation_surjective K L a.val

/-- The original normalized field valuation is rank-one discrete by its actual value group. -/
instance FieldOfNorms.fieldValuation_isRankOneDiscrete [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    Valuation.IsRankOneDiscrete (FieldOfNorms.fieldValuation K L) := by
  let hG : Nontrivial (FieldOfNorms.fieldValuation K L).valueGroup := by
    rw [FieldOfNorms.fieldValuation_valueGroup_eq_top K L]
    infer_instance
  exact @Valuation.IsRankOneDiscrete.mk' _ _ _ _
    (FieldOfNorms.fieldValuation K L) inferInstance hG

/-- The actual valuation subring of the same original field is a discrete valuation ring. -/
instance FieldOfNorms.fieldValuation_isDiscreteValuationRing [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    IsDiscreteValuationRing (FieldOfNorms.fieldValuation K L).valuationSubring := by
  let hG : Nontrivial (FieldOfNorms.fieldValuation K L).valueGroup := by
    rw [FieldOfNorms.fieldValuation_valueGroup_eq_top K L]
    infer_instance
  exact @Valuation.valuationSubring_isDiscreteValuationRing _ _ _ _
    (FieldOfNorms.fieldValuation K L) inferInstance hG

/-- The valuation of the `Valued` instance is the field valuation, definitionally. -/
@[simp]
theorem FieldOfNorms.valued_v [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (Valued.v : Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ))) =
      FieldOfNorms.fieldValuation K L := rfl

instance FieldOfNorms.instIsRankOneDiscrete [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (Valued.v : Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
  FieldOfNorms.fieldValuation_isRankOneDiscrete K L

instance FieldOfNorms.instIsDiscreteValuationRing [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    IsDiscreteValuationRing
      (Valued.v : Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ))).valuationSubring :=
  FieldOfNorms.fieldValuation_isDiscreteValuationRing K L

/-- The reconstructed family as an element of its actual original valuation ring. -/
def FieldOfNorms.uniformizerInteger [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (FieldOfNorms.fieldValuation K L).valuationSubring := by
  refine ⟨FieldOfNorms.uniformizer K L, ?_⟩
  change FieldOfNorms.valuation K L (FieldOfNorms.uniformizer K L) ≤ 1
  rw [FieldOfNorms.valuation_fieldOfNormsUniformizer]
  change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
  exact WithZero.exp_le_exp.mpr (by omega)

@[simp]
theorem FieldOfNorms.uniformizerInteger_coe [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (FieldOfNorms.uniformizerInteger K L : FieldOfNorms K L) =
      FieldOfNorms.uniformizer K L := rfl

/-- The original family is a uniformizer for the same actual field valuation. -/
theorem FieldOfNorms.uniformizer_isUniformizer [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    (FieldOfNorms.fieldValuation K L).IsUniformizer
      (FieldOfNorms.uniformizer K L) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (FieldOfNorms.fieldValuation_surjective K L)]
  exact FieldOfNorms.valuation_fieldOfNormsUniformizer K L

/-- The actual original maximal ideal is generated by the reconstructed uniformizer. -/
theorem FieldOfNorms.uniformizer_maximalIdeal [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    IsLocalRing.maximalIdeal (FieldOfNorms.fieldValuation K L).valuationSubring =
      Ideal.span {FieldOfNorms.uniformizerInteger K L} := by
  exact Valuation.IsUniformizer.is_generator
    (π := FieldOfNorms.uniformizerInteger K L)
    (FieldOfNorms.uniformizer_isUniformizer K L)

/-- The actual reconstructed valuation-ring element is irreducible in that same DVR. -/
theorem FieldOfNorms.uniformizerInteger_irreducible [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    Irreducible (FieldOfNorms.uniformizerInteger K L) := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (FieldOfNorms.uniformizer_maximalIdeal K L)

/-- The canonical normalized valuation of the actual original valuation ring
is exactly the existing stable field valuation on the same original carrier. -/
theorem FieldOfNorms.fieldValuation_eq_normalized [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    (IsDiscreteValuationRing.maximalIdeal
      (FieldOfNorms.fieldValuation K L).valuationSubring).valuation (FieldOfNorms K L) =
        FieldOfNorms.fieldValuation K L := by
  let v := FieldOfNorms.fieldValuation K L
  let R := v.valuationSubring
  let π := FieldOfNorms.uniformizerInteger K L
  have hπ : Irreducible π := FieldOfNorms.uniformizerInteger_irreducible K L
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation (FieldOfNorms K L)
  have hwπ : w (algebraMap R (FieldOfNorms K L) π) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hπ.ne_zero
        hπ.maximalIdeal_eq
  have hvπ : v (algebraMap R (FieldOfNorms K L) π) = WithZero.exp (-1 : ℤ) :=
    FieldOfNorms.valuation_fieldOfNormsUniformizer K L
  have hval (a : R) : w (algebraMap R (FieldOfNorms K L) a) = v (algebraMap R (FieldOfNorms K L) a)
      := by
    by_cases ha : a = 0
    · simp only [ha, _root_.map_zero]
    obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hwu : w (algebraMap R (FieldOfNorms K L) (u : R)) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
      change ¬ (u : R) ∈ IsLocalRing.maximalIdeal R
      exact fun h => h u.isUnit
    have hvu : v (algebraMap R (FieldOfNorms K L) (u : R)) = 1 :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers v)).mp u.isUnit
    rw [ha]
    simp only [_root_.map_mul, map_pow, hwu, hvu, hwπ, hvπ]
  apply Valuation.ext
  intro a
  obtain ⟨x, y, _hy, ha⟩ := IsFractionRing.div_surjective R a
  rw [← ha, map_div₀, map_div₀, hval x, hval y]

end FontaineWintenberger
