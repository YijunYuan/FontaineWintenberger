/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteBase
public import FontaineWintenberger.APF.IndexTower

/-!
# The actual finite-base APF inertia index identity
-/

@[expose] public section

namespace FontaineWintenberger

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

local notation "ρ" =>
  MonoidHom.comp (Subgroup.subtype (IntermediateField.fixingSubgroup M))
    (MulEquiv.toMonoidHom (absoluteGaloisBaseChangeEquiv K M))

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

variable [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

omit [Algebra.IsSeparable K N] in
/-- The actual inertia product over the new base is the old product preimage. -/
theorem comap_apfInertiaSubgroup_finiteBase (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : 0 ≤ u) :
    (apfInertiaSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u).comap ρ =
      apfInertiaSubgroup M i.fieldRange (apfPsi K M u) := by
  have hψ : 0 ≤ apfPsi K M u := hu.trans (IsAPF.le_apfPsi K M (isAPF_of_finite K M) u)
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.comap_inf,
    comap_apfSubgroup_finiteBase K M i (by linarith),
    comap_absoluteUpper_finiteBase K M (by norm_num : (-1 : ℝ) ≤ 0),
    apfPsi_zero, ← apfInertiaSubgroup_eq_inf M _ _ hψ]

/-- The new-base index is exactly the actual old-base relative tower factor. -/
theorem apfIndex_finiteBase_eq_towerIndexFactor (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : 0 ≤ u) :
    apfIndex M N (apfPsi K M u) =
      apfTowerIndexFactor K M (baseChangedSeparableEmbedding K M i).fieldRange u := by
  have hzero : (absoluteUpperRamificationGroup K 0).comap ρ =
      absoluteUpperRamificationGroup M 0 := by
    simpa only [apfPsi_zero] using
      comap_absoluteUpper_finiteBase K M (by norm_num : (-1 : ℝ) ≤ 0)
  rw [apfIndex_eq_embedding M N i, apfInertiaIndex,
    ← comap_apfInertiaSubgroup_finiteBase K M i hu, ← hzero,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    absoluteGaloisBaseChange_range K M]
  simpa only [apfTowerIndexFactor, apfInertiaSubgroup, inf_comm] using
    (Subgroup.relIndex_sup_sup_normal
    ((baseChangedSeparableEmbedding K M i).fieldRange.fixingSubgroup ⊓
      absoluteUpperRamificationGroup K 0)
    (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
    (absoluteUpperRamificationGroup K u)).symm


/-- The public intrinsic indices factor through the actual finite base, without APF on N. -/
theorem apfIndex_eq_mul_finiteBase {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K N u = apfIndex K M u * apfIndex M N (apfPsi K M u) := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [apfIndex_eq_embedding K N (baseChangedSeparableEmbedding K M i)]
  have hfac := apfIndex_eq_mul_towerIndexFactor K M
    (baseChangedSeparableEmbedding K M i).fieldRange
    (le_baseChangedSeparableEmbedding_fieldRange K M i) hu
  rw [apfIndex_eq_embedding K _ (baseChangedSeparableEmbedding K M i).fieldRange.val,
    IntermediateField.fieldRange_val,
    ← apfIndex_finiteBase_eq_towerIndexFactor K M i hu] at hfac
  exact hfac

end FontaineWintenberger
