/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Reconstruction
public import FontaineWintenberger.FieldOfNorms.Valued

/-!
# An actual norm-family uniformizer

A genuine uniformizer class in the first original finite quotient lifts
through the actual surjective norm tower. Reconstruction supplies a family
on the same original norm-limit carrier with normalized value one.
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

include p

/-- An actual compatible norm family has normalized value one. The family
is reconstructed from a lifted genuine first-stage uniformizer class. -/
theorem exists_normLimitValuation_eq_exp_neg_one (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    ∃ πX : NormLimit K L, normLimitValuation K L hL πX = WithZero.exp (-1 : ℤ) := by
  let D : FiniteLayer K L := FiniteLayer.bottom
  let E := deepFiniteTower K L p hL hInfinite D
  let B := deepFiniteTowerQuotient K L p hL hInfinite D
  let q (n : ℕ) := deepFiniteTowerTransition K L p hL hInfinite D n (n + 1) (Nat.le_succ n)
  let R := spectralIntegerRing K (E 0).val
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs (n : ℕ) : Function.Surjective (q n) :=
    deepFiniteTowerTransition_surjective K L p hL hInfinite D n (n + 1) (Nat.le_succ n)
  obtain ⟨a, ha⟩ := SequentialInverseLimit.projection_surjective B q hs 0 (Ideal.Quotient.mk _ π)
  change a.val 0 = Ideal.Quotient.mk _ π at ha
  let πX := deepNormReconstruction K L p hL hInfinite D a
  have hπX : normLimitValuation K L hL πX ≤ 1 :=
    deepNormReconstruction_valuation_le_one K L p hL hInfinite D a
  let z : R := ⟨normLimitEval K L (E 0) πX,
    normLimitEval_mem_of_valuation_le_one K L hL πX hπX (E 0)⟩
  let x := deepNormRepresentative K L p hL hInfinite D a 0
  obtain ⟨d, hd, heq⟩ := deepNormReconstruction_sub_mem K L p hL hInfinite D a 0
  have hzd : z - x = d := Subtype.ext heq.symm
  have hz : z - x ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    rw [hzd]
    exact hd
  have hclass : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ 2) z =
      Ideal.Quotient.mk _ π :=
    (Ideal.Quotient.eq.mpr hz).trans
      ((deepNormRepresentative_mk K L p hL hInfinite D a 0).trans ha)
  have ht := congrArg (truncatedAddVal R 2) hclass
  rw [truncatedAddVal_mk, truncatedAddVal_mk, IsDiscreteValuationRing.addVal_uniformizer hπ] at ht
  have ht' : min (IsDiscreteValuationRing.addVal R z) 2 = 1 := by simpa using ht
  have hzval : IsDiscreteValuationRing.addVal R z = 1 := by
    rcases min_eq_iff.mp ht' with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · norm_num at h
  refine ⟨πX, ?_⟩
  rw [normLimitValuation_eq_deepFiniteTower K L p hL hInfinite D 0]
  change (IsDiscreteValuationRing.maximalIdeal R).valuation (E 0).val (algebraMap R (E 0).val z) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal, hzval]
  rfl

/-- A chosen actual original norm-compatible family with normalized value one. -/
def normLimitUniformizer (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) : NormLimit K L :=
  (exists_normLimitValuation_eq_exp_neg_one K L p hL hInfinite).choose

@[simp]
theorem normLimitValuation_normLimitUniformizer (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    normLimitValuation K L hL (normLimitUniformizer K L p hL hInfinite) =
      WithZero.exp (-1 : ℤ) :=
  (exists_normLimitValuation_eq_exp_neg_one K L p hL hInfinite).choose_spec

/-- The actual reconstructed uniformizer is a nonzero original norm family. -/
theorem normLimitUniformizer_ne_zero (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    normLimitUniformizer K L p hL hInfinite ≠ 0 := by
  intro h
  have hv := normLimitValuation_normLimitUniformizer K L p hL hInfinite
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- All original integer powers have their exact original normalized values. -/
theorem normLimitUniformizer_zpow_valuation (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) (m : ℤ) :
    normLimitValuation K L hL (normLimitUniformizer K L p hL hInfinite ^ m) =
      WithZero.exp (-m) := by
  rw [map_zpow₀, normLimitValuation_normLimitUniformizer, ← WithZero.exp_zsmul]
  congr 1
  simp

/-- The same original stable valuation attains every normalized integer value and zero. -/
theorem normLimitValuation_surjective (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    Function.Surjective (normLimitValuation K L hL) := by
  intro a
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, map_zero _⟩
  | coe a =>
      refine ⟨normLimitUniformizer K L p hL hInfinite ^ (-Multiplicative.toAdd a), ?_⟩
      rw [normLimitUniformizer_zpow_valuation, neg_neg]
      rfl

/-- Bundling the same original map as a field valuation preserves its proved surjectivity. -/
theorem normLimitFieldValuation_surjective (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    let := normLimitField K L p hL hInfinite
    Function.Surjective (normLimitFieldValuation K L p hL hInfinite) := by
  let := normLimitField K L p hL hInfinite
  exact normLimitValuation_surjective K L p hL hInfinite

/-- The value group of the actual original field valuation is the entire integer group. -/
theorem normLimitFieldValuation_valueGroup_eq_top (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    let := normLimitField K L p hL hInfinite
    (normLimitFieldValuation K L p hL hInfinite).valueGroup = ⊤ := by
  let := normLimitField K L p hL hInfinite
  apply top_unique
  intro a _ha
  apply MonoidWithZeroHom.mem_valueGroup
  exact normLimitValuation_surjective K L p hL hInfinite a.val

/-- The original normalized field valuation is rank-one discrete by its actual value group. -/
theorem normLimitFieldValuation_isRankOneDiscrete (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    let := normLimitField K L p hL hInfinite
    Valuation.IsRankOneDiscrete (normLimitFieldValuation K L p hL hInfinite) := by
  dsimp only
  let := normLimitField K L p hL hInfinite
  let hG : Nontrivial (normLimitFieldValuation K L p hL hInfinite).valueGroup := by
    rw [normLimitFieldValuation_valueGroup_eq_top K L p hL hInfinite]
    infer_instance
  exact @Valuation.IsRankOneDiscrete.mk' _ _ _ _
    (normLimitFieldValuation K L p hL hInfinite) inferInstance hG

/-- The actual valuation subring of the same original field is a discrete valuation ring. -/
theorem normLimitFieldValuation_isDiscreteValuationRing (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    let := normLimitField K L p hL hInfinite
    IsDiscreteValuationRing (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  dsimp only
  let := normLimitField K L p hL hInfinite
  let hG : Nontrivial (normLimitFieldValuation K L p hL hInfinite).valueGroup := by
    rw [normLimitFieldValuation_valueGroup_eq_top K L p hL hInfinite]
    infer_instance
  exact @Valuation.valuationSubring_isDiscreteValuationRing _ _ _ _
    (normLimitFieldValuation K L p hL hInfinite) inferInstance hG

/-- The reconstructed family as an element of its actual original valuation ring. -/
def normLimitUniformizerInteger (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  letI := normLimitField K L p hL hInfinite
  refine ⟨normLimitUniformizer K L p hL hInfinite, ?_⟩
  change normLimitValuation K L hL (normLimitUniformizer K L p hL hInfinite) ≤ 1
  rw [normLimitValuation_normLimitUniformizer]
  change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
  exact WithZero.exp_le_exp.mpr (by omega)

@[simp]
theorem normLimitUniformizerInteger_coe (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    (normLimitUniformizerInteger K L p hL hInfinite : NormLimit K L) =
      normLimitUniformizer K L p hL hInfinite := rfl

/-- The original family is a uniformizer for the same actual field valuation. -/
theorem normLimitUniformizer_isUniformizer (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitFieldValuation_isRankOneDiscrete K L p hL hInfinite
    (normLimitFieldValuation K L p hL hInfinite).IsUniformizer
      (normLimitUniformizer K L p hL hInfinite) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitFieldValuation_isRankOneDiscrete K L p hL hInfinite
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (normLimitFieldValuation_surjective K L p hL hInfinite)]
  exact normLimitValuation_normLimitUniformizer K L p hL hInfinite

/-- The actual original maximal ideal is generated by the reconstructed uniformizer. -/
theorem normLimitUniformizer_maximalIdeal (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    IsLocalRing.maximalIdeal (normLimitFieldValuation K L p hL hInfinite).valuationSubring =
      Ideal.span {normLimitUniformizerInteger K L p hL hInfinite} := by
  let := normLimitField K L p hL hInfinite
  let := normLimitFieldValuation_isRankOneDiscrete K L p hL hInfinite
  exact Valuation.IsUniformizer.is_generator
    (π := normLimitUniformizerInteger K L p hL hInfinite)
    (normLimitUniformizer_isUniformizer K L p hL hInfinite)

/-- The actual reconstructed valuation-ring element is irreducible in that same DVR. -/
theorem normLimitUniformizerInteger_irreducible (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    Irreducible (normLimitUniformizerInteger K L p hL hInfinite) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitFieldValuation_isDiscreteValuationRing K L p hL hInfinite
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (normLimitUniformizer_maximalIdeal K L p hL hInfinite)

/-- The canonical normalized valuation of the actual original valuation ring
is exactly the existing stable field valuation on the same original carrier. -/
theorem normLimitFieldValuation_eq_normalized (hL : IsAPF K L)
    (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitFieldValuation_isDiscreteValuationRing K L p hL hInfinite
    (IsDiscreteValuationRing.maximalIdeal
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring).valuation (NormLimit K L) =
        normLimitFieldValuation K L p hL hInfinite := by
  let := normLimitField K L p hL hInfinite
  let v := normLimitFieldValuation K L p hL hInfinite
  let R := v.valuationSubring
  let : IsDiscreteValuationRing R := normLimitFieldValuation_isDiscreteValuationRing K L p hL
      hInfinite
  let π := normLimitUniformizerInteger K L p hL hInfinite
  have hπ : Irreducible π := normLimitUniformizerInteger_irreducible K L p hL hInfinite
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation (NormLimit K L)
  have hwπ : w (algebraMap R (NormLimit K L) π) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hπ.ne_zero
        hπ.maximalIdeal_eq
  have hvπ : v (algebraMap R (NormLimit K L) π) = WithZero.exp (-1 : ℤ) :=
    normLimitValuation_normLimitUniformizer K L p hL hInfinite
  have hval (a : R) : w (algebraMap R (NormLimit K L) a) = v (algebraMap R (NormLimit K L) a) := by
    by_cases ha : a = 0
    · simp only [ha, map_zero]
    obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hwu : w (algebraMap R (NormLimit K L) (u : R)) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
      change ¬ (u : R) ∈ IsLocalRing.maximalIdeal R
      exact fun h => h u.isUnit
    have hvu : v (algebraMap R (NormLimit K L) (u : R)) = 1 :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers v)).mp u.isUnit
    rw [ha]
    simp only [map_mul, map_pow, hwu, hvu, hwπ, hvπ]
  apply Valuation.ext
  intro a
  obtain ⟨x, y, _hy, ha⟩ := IsFractionRing.div_surjective R a
  rw [← ha, map_div₀, map_div₀, hval x, hval y]

end FontaineWintenberger
