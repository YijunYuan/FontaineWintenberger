/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.FiniteOverfieldBaseChange
public import FontaineWintenberger.APF.FiniteBaseBounds
public import FontaineWintenberger.APF.StrictDescent

/-!
# Actual first bounds after finite base change in any finite Galois overfield

Normal products intersect the actual fixing subgroup by the modular identity.
The own-ring upper-group base change then sends every old admissible parameter
to an actual new one. The extended order isomorphism preserves their supremum.
-/

@[expose] public section

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

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local instance finiteOverfieldBounds_completeSpace (M : IntermediateField K L) :
    CompleteSpace M := FiniteDimensional.complete K M
local instance finiteOverfieldBounds_discreteValuationRing (M : IntermediateField K L) :
    IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring :=
  normedAlgebra_unitBall_isDiscreteValuationRing K M
local instance finiteOverfieldBounds_perfectField (M : IntermediateField K L) :
    PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring) :=
  Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)

local notation "U" => upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L)

/-- Every old finite-overfield product parameter is admissible over the
actual intermediate base on its own spectral integer ring. -/
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

/-- The extended actual old first bound maps below the actual new-base bound
in any finite Galois overfield, including both infinite endpoints. -/
theorem apfHerbrandERealOrderIso_bound_le_of_finiteGalois
    (M N : IntermediateField K L) (hMN : M ≤ N) :
    apfHerbrandERealOrderIso K M (isAPF_of_finite K M) (apfRamificationBound K N) ≤
      apfRamificationBound M (IntermediateField.extendScalars hMN) := by
  rw [apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper K L N,
    (apfHerbrandERealOrderIso K M (isAPF_of_finite K M)).map_sSup]
  apply iSup_le
  intro x
  apply iSup_le
  rintro ⟨u, hu, htop, rfl⟩
  rw [apfHerbrandERealOrderIso_coe,
    apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper M L
      (IntermediateField.extendScalars hMN)]
  exact le_sSup ⟨apfPsi K M u,
    IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu,
    finiteOverfield_fixing_sup_upper_eq_top K L M N hMN hu htop, rfl⟩

/-- Finite base change increases the same actual intrinsic first bound. -/
theorem apfRamificationBound_le_finiteBase_of_finiteGalois
    (M N : IntermediateField K L) (hMN : M ≤ N) :
    apfRamificationBound K N ≤
      apfRamificationBound M (IntermediateField.extendScalars hMN) :=
  (IsAPF.le_apfHerbrandERealOrderIso K M (isAPF_of_finite K M) _).trans
    (apfHerbrandERealOrderIso_bound_le_of_finiteGalois K L M N hMN)

/-- The same old first bound is a common lower bound for every actual
intermediate step, by genuine base change and an actual field inclusion. -/
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
