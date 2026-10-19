/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import FontaineWintenberger.APF.Subextension
public import Mathlib.Order.Hom.WithTopBot

/-!
# Ramification bounds after finite base change

## Extended finite-base ramification and strictness bounds

## First bounds after finite base change in any finite Galois overfield

Normal products intersect the fixing subgroup by the modular identity.
The own-ring upper-group base change then sends every old admissible parameter
to a new one. The extended order isomorphism preserves their supremum.
-/

@[expose] public section

namespace FontaineWintenberger

open MeasureTheory Filter
open scoped ENNReal

section Extended

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The canonical Herbrand order isomorphism extended by its two infinite endpoints. -/
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

/-- The lower bound extends honestly to both infinite endpoints. -/
theorem IsAPF.le_apfHerbrandERealOrderIso [IsAPF K L] (u : EReal) :
    u ≤ apfHerbrandERealOrderIso K L u := by
  induction u using EReal.rec with
  | bot => simp
  | top => simp
  | coe u => exact EReal.coe_le_coe_iff.mpr (IsAPF.le_apfPsi K L u)

end Extended

section FiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
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
/-- Every old admissible upper parameter gives a new admissible parameter. -/
theorem apfSubgroup_finiteBase_eq_top (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : -1 ≤ u)
    (htop : apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u = ⊤) :
    apfSubgroup M i.fieldRange (apfPsi K M u) = ⊤ := by
  rw [← comap_apfSubgroup_finiteBase K M i hu, htop, Subgroup.comap_top]

/-- The extended old ramification bound maps below the new-base bound. -/
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

/-- Changing a finite base increases the extended first ramification bound. -/
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

namespace FontaineWintenberger

private theorem finiteOverfield_fixing_map
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M N : IntermediateField K L) (hMN : M ≤ N) :
    (N.fixingSubgroup.subgroupOf M.fixingSubgroup).map
      M.fixingSubgroupEquiv.toMonoidHom =
        (IntermediateField.extendScalars hMN).fixingSubgroup := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  ext g
  rfl

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [FiniteDimensional K L] [IsGalois K L]
    [PerfectField 𝓀[K]]

local instance finiteOverfieldBounds_completeSpace (M : IntermediateField K L) :
    CompleteSpace M := FiniteDimensional.complete K M
local instance finiteOverfieldBounds_discreteValuationRing (M : IntermediateField K L) :
    IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
local instance finiteOverfieldBounds_perfectField (M : IntermediateField K L) :
    PerfectField 𝓀[M] :=
  Algebra.IsAlgebraic.perfectField 𝓀[K]

local notation "U" => upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L)

/-- Every old finite-overfield product parameter is admissible over the
intermediate base on its own spectral integer ring. -/
theorem finiteOverfield_fixing_sup_upper_eq_top
    (M N : IntermediateField K L) (hMN : M ≤ N) {u : ℝ} (hu : -1 ≤ u)
    (htop : N.fixingSubgroup ⊔ U u = ⊤) :
    (IntermediateField.extendScalars hMN).fixingSubgroup ⊔
      upperRamificationGroup (R := spectralIntegerRing M L) (L ≃ₐ[M] L)
        (apfPsi K M u) = ⊤ := by
  have hsub : N.fixingSubgroup ≤ M.fixingSubgroup := IntermediateField.fixingSubgroup_le hMN
  have hinter : N.fixingSubgroup ⊔ (U u ⊓ M.fixingSubgroup) = M.fixingSubgroup := by
    rw [← Subgroup.sup_inf_eq_sup_inf_of_le_of_normal
      N.fixingSubgroup M.fixingSubgroup (U u) hsub, htop, top_inf_eq]
  have hfull : N.fixingSubgroup.subgroupOf M.fixingSubgroup ⊔
      (U u).subgroupOf M.fixingSubgroup = ⊤ := by
    apply Subgroup.map_injective (f := M.fixingSubgroup.subtype) Subtype.coe_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hsub, hinter,
      Subgroup.map_top, Subgroup.range_subtype]
  rw [← finiteOverfield_fixing_map M N hMN,
    finiteBase_upperRamificationGroup_of_finiteGalois K L M hu,
    ← Subgroup.map_sup, hfull,
    Subgroup.map_top_of_surjective _ M.fixingSubgroupEquiv.surjective]

/-- The extended old first bound maps below the new-base bound
in any finite Galois overfield, including both infinite endpoints. -/
theorem apfHerbrandERealOrderIso_bound_le_of_finiteGalois
    (M N : IntermediateField K L) (hMN : M ≤ N) :
    apfHerbrandERealOrderIso K M (apfRamificationBound K N) ≤
      apfRamificationBound M (IntermediateField.extendScalars hMN) := by
  rw [apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper K L N,
    (apfHerbrandERealOrderIso K M).map_sSup]
  apply iSup_le
  intro x
  apply iSup_le
  rintro ⟨u, hu, htop, rfl⟩
  rw [apfHerbrandERealOrderIso_coe,
    apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper M L
      (IntermediateField.extendScalars hMN)]
  exact le_sSup ⟨apfPsi K M u,
    IsAPF.apfPsi_mem_Ici K M hu,
    finiteOverfield_fixing_sup_upper_eq_top K L M N hMN hu htop, rfl⟩

/-- Finite base change increases the same intrinsic first bound. -/
theorem apfRamificationBound_le_finiteBase_of_finiteGalois
    (M N : IntermediateField K L) (hMN : M ≤ N) :
    apfRamificationBound K N ≤
      apfRamificationBound M (IntermediateField.extendScalars hMN) :=
  (IsAPF.le_apfHerbrandERealOrderIso K M _).trans
    (apfHerbrandERealOrderIso_bound_le_of_finiteGalois K L M N hMN)

/-- The same old first bound is a common lower bound for every
intermediate step, by base change and a field inclusion. -/
theorem apfRamificationBound_le_step_of_finiteGalois
    (A B N : IntermediateField K L) (hAB : A ≤ B) (hBN : B ≤ N) :
    apfRamificationBound K N ≤
      apfRamificationBound A (IntermediateField.extendScalars hAB) := by
  let N' := IntermediateField.extendScalars (hAB.trans hBN)
  let B' := IntermediateField.extendScalars hAB
  have hle : B' ≤ N' := hBN
  exact (apfRamificationBound_le_finiteBase_of_finiteGalois K L A N
    (hAB.trans hBN)).trans (apfRamificationBound_le_of_algHom A (L := N') (P := B')
      (IntermediateField.inclusion hle))

end FontaineWintenberger
