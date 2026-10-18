/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.StrictBaseChange
public import Mathlib.Order.Hom.WithTopBot

/-!
# Extended finite-base ramification and strictness bounds
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

section Extended

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The canonical actual Herbrand order isomorphism extended by its two infinite endpoints. -/
noncomputable def apfHerbrandERealOrderIso [IsAPF K L] : EReal ≃o EReal :=
  (apfHerbrandOrderIso K L).withTopCongr.withBotCongr

@[simp]
theorem apfHerbrandERealOrderIso_coe [IsAPF K L] (u : ℝ) :
    apfHerbrandERealOrderIso K L (u : EReal) = (apfPsi K L u : EReal) := rfl

@[simp]
theorem apfHerbrandERealOrderIso_top [IsAPF K L] :
    apfHerbrandERealOrderIso K L ⊤ = ⊤ :=
  (apfHerbrandERealOrderIso K L).map_top

@[simp]
theorem apfHerbrandERealOrderIso_bot [IsAPF K L] :
    apfHerbrandERealOrderIso K L ⊥ = ⊥ :=
  (apfHerbrandERealOrderIso K L).map_bot

@[simp]
theorem apfHerbrandERealOrderIso_symm_coe [IsAPF K L] (u : ℝ) :
    (apfHerbrandERealOrderIso K L).symm (u : EReal) = (apfPhi K L u : EReal) := rfl

/-- The actual lower bound extends honestly to both infinite endpoints. -/
theorem IsAPF.le_apfHerbrandERealOrderIso [IsAPF K L] (u : EReal) :
    u ≤ apfHerbrandERealOrderIso K L u := by
  induction u using EReal.rec with
  | bot => simp
  | top => simp
  | coe u => exact EReal.coe_le_coe_iff.mpr (IsAPF.le_apfPsi K L u)

end Extended

section FiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

noncomputable local instance : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
noncomputable local instance : NormedAlgebra K M := spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
noncomputable local instance : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'




variable (N : Type*) [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

omit [Algebra.IsSeparable K N] in
/-- Every old admissible upper parameter gives a genuine new admissible parameter. -/
theorem apfSubgroup_finiteBase_eq_top (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : -1 ≤ u)
    (htop : apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u = ⊤) :
    apfSubgroup M i.fieldRange (apfPsi K M u) = ⊤ := by
  rw [← comap_apfSubgroup_finiteBase K M i hu, htop, Subgroup.comap_top]

/-- The extended old ramification bound maps below the actual new-base bound. -/
theorem apfHerbrandERealOrderIso_bound_le :
    apfHerbrandERealOrderIso K M (apfRamificationBound K N) ≤
      apfRamificationBound M N := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [apfRamificationBound_eq_embedding K N (baseChangedSeparableEmbedding K M i),
    (apfHerbrandERealOrderIso K M).map_sSup]
  apply iSup_le
  intro x
  apply iSup_le
  rintro ⟨u, hu, htop, rfl⟩
  rw [apfHerbrandERealOrderIso_coe]
  exact le_apfRamificationBound M N i
    (IsAPF.apfPsi_mem_Ici K M hu)
    (apfSubgroup_finiteBase_eq_top K M N i hu htop)

/-- Changing a finite base increases the actual extended first ramification bound. -/
theorem apfRamificationBound_le_finiteBase :
    apfRamificationBound K N ≤ apfRamificationBound M N :=
  (IsAPF.le_apfHerbrandERealOrderIso K M _).trans
    (apfHerbrandERealOrderIso_bound_le K M N)

/-- Above a positive old first bound the extended strictness constant increases under finite
base. -/
theorem apfStrictnessConstant_le_finiteBase [IsAPF K N]
    (hi : (0 : EReal) < apfRamificationBound K N) :
    apfStrictnessConstant K N ≤ apfStrictnessConstant M N := by
  apply le_iInf
  intro v
  apply le_iInf
  intro hv
  let u := apfPhi K M v
  have hub : apfRamificationBound K N ≤ (u : EReal) := by
    have h := (apfHerbrandERealOrderIso K M).symm.monotone
      ((apfHerbrandERealOrderIso_bound_le K M N).trans hv)
    simpa only [OrderIso.symm_apply_apply, apfHerbrandERealOrderIso_symm_coe] using h
  have hu0 : 0 ≤ u := EReal.coe_nonneg.mp (hi.le.trans hub)
  have hratio := IsAPF.apfStrictnessRatio_finiteBase K M N hu0
  rw [apfPsi_apfPhi] at hratio
  have hone : (1 : ℝ≥0∞) ≤ (apfIndex K M u : ℝ≥0∞) :=
    Nat.one_le_cast.mpr (IsAPF.apfIndex_pos K M hu0)
  calc
    apfStrictnessConstant K N ≤ apfStrictnessRatio K N u :=
      apfStrictnessConstant_le K N hub
    _ = 1 * apfStrictnessRatio K N u := (one_mul _).symm
    _ ≤ (apfIndex K M u : ℝ≥0∞) * apfStrictnessRatio K N u :=
      mul_le_mul_of_nonneg_right hone bot_le
    _ = apfStrictnessRatio M N v := hratio.symm

end FiniteBase

end FontaineWintenberger
