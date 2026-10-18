/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.AbsoluteBaseChange
public import FontaineWintenberger.GroupTheory.FiniteIndex

/-!
# APF under actual finite base change

The fixing subgroup of an abstract extension is transported through the
actual closure isomorphism, together with the actual absolute upper group.
-/

@[expose] public section

namespace FontaineWintenberger

section Embeddings

variable (K : Type*) [Field K] (M : IntermediateField K (SeparableClosure K))
noncomputable local instance : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The actual old-base embedding induced by a new-base separable-closure embedding. -/
noncomputable def baseChangedSeparableEmbedding (i : N →ₐ[M] SeparableClosure M) :
    N →ₐ[K] SeparableClosure K :=
  ((separableClosureBaseChangeEquiv K M).toAlgHom.comp i).restrictScalars K

/-- The induced embedding contains the actual new scalar field. -/
theorem le_baseChangedSeparableEmbedding_fieldRange (i : N →ₐ[M] SeparableClosure M) :
    M ≤ (baseChangedSeparableEmbedding K M i).fieldRange := by
  intro x hx
  refine AlgHom.mem_fieldRange.mpr ⟨algebraMap M N ⟨x, hx⟩, ?_⟩
  change separableClosureBaseChangeEquiv K M (i (algebraMap M N ⟨x, hx⟩)) = x
  rw [i.commutes, (separableClosureBaseChangeEquiv K M).commutes]
  rfl

/-- Actual closure base change identifies the two actual fixing subgroups. -/
theorem comap_fixingSubgroup_baseChangedEmbedding (i : N →ₐ[M] SeparableClosure M) :
    (baseChangedSeparableEmbedding K M i).fieldRange.fixingSubgroup.comap
        (M.fixingSubgroup.subtype.comp (absoluteGaloisBaseChangeEquiv K M).toMonoidHom) =
      i.fieldRange.fixingSubgroup := by
  ext g
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp x.property
    apply (separableClosureBaseChangeEquiv K M).injective
    have h' := h ⟨baseChangedSeparableEmbedding K M i y,
      AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩
    change (absoluteGaloisBaseChangeEquiv K M g).1
      (separableClosureBaseChangeEquiv K M (i y)) =
        separableClosureBaseChangeEquiv K M (i y) at h'
    rw [absoluteGaloisBaseChangeEquiv_apply] at h'
    rw [← hy]
    exact h'
  · intro h x
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp x.property
    change (absoluteGaloisBaseChangeEquiv K M g).1 (x : SeparableClosure K) = x
    rw [← hy]
    change (absoluteGaloisBaseChangeEquiv K M g).1
      (separableClosureBaseChangeEquiv K M (i y)) =
        separableClosureBaseChangeEquiv K M (i y)
    rw [absoluteGaloisBaseChangeEquiv_apply]
    exact congrArg (separableClosureBaseChangeEquiv K M)
      (h ⟨i y, AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩)

/-- The actual closure homomorphism has exactly the subgroup fixing the new base as image. -/
theorem absoluteGaloisBaseChange_range :
    (M.fixingSubgroup.subtype.comp (absoluteGaloisBaseChangeEquiv K M).toMonoidHom).range =
      M.fixingSubgroup := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (absoluteGaloisBaseChangeEquiv K M).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

end Embeddings

section Valued

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

omit [IsCompleteDiscreteValuedField K] [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] in
/-- The actual absolute fixing subgroup has finite index for a finite new base. -/
theorem absoluteGaloisBaseChange_range_finiteIndex : (ρ).range.FiniteIndex := by
  rw [absoluteGaloisBaseChange_range K M]
  let : Finite ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ M.fixingSubgroup) :=
    M.fixingSubgroup.quotient_finite_of_isOpen (IntermediateField.fixingSubgroup_isOpen M)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The actual upper-group preimage under finite base change has the intrinsic new parameter. -/
theorem comap_absoluteUpper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).comap ρ =
      absoluteUpperRamificationGroup M (apfPsi K M u) := by
  ext g
  exact (absoluteGaloisBaseChange_mem_upper_iff K M hu g).symm

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The actual APF product over the new base is the preimage of the old-base product. -/
theorem comap_apfSubgroup_finiteBase (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u).comap ρ =
      apfSubgroup M i.fieldRange (apfPsi K M u) := by
  have hA : (baseChangedSeparableEmbedding K M i).fieldRange.fixingSubgroup ≤ (ρ).range := by
    rw [absoluteGaloisBaseChange_range K M]
    exact IntermediateField.fixingSubgroup_le (le_baseChangedSeparableEmbedding_fieldRange K M i)
  rw [apfSubgroup, ← Subgroup.comap_sup_eq_of_normal_right_of_le_range ρ _ _ hA,
    comap_fixingSubgroup_baseChangedEmbedding K M i, comap_absoluteUpper_finiteBase K M hu]
  rfl

variable [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

/-- Public abstract APF is invariant under a finite change of the actual base. -/
theorem isAPF_finiteBase_iff : IsAPF K N ↔ IsAPF M N := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [isAPF_iff_embedding K N (baseChangedSeparableEmbedding K M i),
    isAPF_iff_embedding M N i, isAPFSubextension_iff_finiteIndex,
    isAPFSubextension_iff_finiteIndex]
  let := absoluteGaloisBaseChange_range_finiteIndex K M
  have hM := isAPF_of_finite K M
  constructor
  · intro h v hv
    let u := apfPhi K M hM v
    have hu : -1 ≤ u := apfPhi_mem_Ici K M hM hv
    have hindex := (Subgroup.finiteIndex_iff_comap_of_range ρ
      (apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u)).mp (h u hu)
    rw [comap_apfSubgroup_finiteBase K M i hu, apfPsi_apfPhi] at hindex
    exact hindex
  · intro h u hu
    apply (Subgroup.finiteIndex_iff_comap_of_range ρ
      (apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u)).mpr
    rw [comap_apfSubgroup_finiteBase K M i hu]
    exact h (apfPsi K M u) (IsAPF.apfPsi_mem_Ici K M hM hu)

end Valued

end FontaineWintenberger
