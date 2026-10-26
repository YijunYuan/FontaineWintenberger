/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import FontaineWintenberger.APF.Index
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Monotone

/-!
# APF under finite base change

The fixing subgroup of an abstract extension is transported through the
closure isomorphism, together with the absolute upper group.

## Main definitions

* `baseChangedSeparableEmbedding`: The old-base embedding induced by a new-base separable-closure
  embedding.

## Main results

* `le_baseChangedSeparableEmbedding_fieldRange`: The induced embedding contains the new scalar
  field.
* `comap_fixingSubgroup_baseChangedEmbedding`: Closure base change identifies the two fixing
  subgroups.
* `absoluteGaloisBaseChange_range`: The closure homomorphism has exactly the subgroup fixing the new
  base as image.
* `absoluteGaloisBaseChange_range_finiteIndex`: The absolute fixing subgroup has finite index for a
  finite new base.
* `comap_absoluteUpper_finiteBase`: The upper-group preimage under finite base change has the
  intrinsic new parameter.
* `comap_apfSubgroup_finiteBase`: The APF product over the new base is the preimage of the old-base
  product.
* `isAPF_finiteBase_iff`: Public abstract APF is invariant under a finite change of the base.
* `comap_apfInertiaSubgroup_finiteBase`: The inertia product over the new base is the old product
  preimage.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

section Embeddings

variable (K : Type*) [Field K] (M : IntermediateField K (SeparableClosure K))
/-- The canonical algebra structure on the separable closure of the new base. -/
noncomputable local instance baseChangeEmbeddingAlgebra : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The old-base embedding induced by a new-base separable-closure embedding. -/
noncomputable def baseChangedSeparableEmbedding (i : N →ₐ[M] SeparableClosure M) :
    N →ₐ[K] SeparableClosure K :=
  ((separableClosureBaseChangeEquiv K M).toAlgHom.comp i).restrictScalars K

/-- The induced embedding contains the new scalar field. -/
theorem le_baseChangedSeparableEmbedding_fieldRange (i : N →ₐ[M] SeparableClosure M) :
    M ≤ (baseChangedSeparableEmbedding K M i).fieldRange := by
  intro x hx
  refine AlgHom.mem_fieldRange.mpr ⟨algebraMap M N ⟨x, hx⟩, ?_⟩
  change separableClosureBaseChangeEquiv K M (i (algebraMap M N ⟨x, hx⟩)) = x
  rw [i.commutes, (separableClosureBaseChangeEquiv K M).commutes]
  rfl

/-- Closure base change identifies the two fixing subgroups. -/
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

/-- The closure homomorphism has exactly the subgroup fixing the new base as image. -/
theorem absoluteGaloisBaseChange_range :
    (M.fixingSubgroup.subtype.comp (absoluteGaloisBaseChangeEquiv K M).toMonoidHom).range =
      M.fixingSubgroup := by
  rw [MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (absoluteGaloisBaseChangeEquiv K M).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

end Embeddings

section Valued

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- The spectral norm on the finite base for the APF base-change criterion. -/
noncomputable local instance baseChangeNormedField : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
/-- The spectral norm makes the finite base a normed algebra over `K`. -/
noncomputable local instance baseChangeNormedAlgebra : NormedAlgebra K M :=
  spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
/-- The canonical algebra structure on the separable closure of the finite base. -/
noncomputable local instance baseChangeClosureAlgebra : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'

local notation "ρ" =>
  MonoidHom.comp (Subgroup.subtype (IntermediateField.fixingSubgroup M))
    (MulEquiv.toMonoidHom (absoluteGaloisBaseChangeEquiv K M))

omit [IsCompleteDiscreteValuedField K] [PerfectField 𝓀[K]] in
/-- The absolute fixing subgroup has finite index for a finite new base. -/
theorem absoluteGaloisBaseChange_range_finiteIndex : (ρ).range.FiniteIndex := by
  rw [absoluteGaloisBaseChange_range K M]
  let : Finite ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ M.fixingSubgroup) :=
    M.fixingSubgroup.quotient_finite_of_isOpen (IntermediateField.fixingSubgroup_isOpen M)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The upper-group preimage under finite base change has the intrinsic new parameter. -/
theorem comap_absoluteUpper_finiteBase {u : ℝ} (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).comap ρ =
      absoluteUpperRamificationGroup M (apfPsi K M u) := by
  ext g
  exact (absoluteGaloisBaseChange_mem_upper_iff K M hu g).symm

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The APF product over the new base is the preimage of the old-base product. -/
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

/-- Public abstract APF is invariant under a finite change of the base. -/
theorem isAPF_finiteBase_iff : IsAPF K N ↔ IsAPF M N := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [isAPF_iff_embedding K N (baseChangedSeparableEmbedding K M i),
    isAPF_iff_embedding M N i, isAPFSubextension_iff_finiteIndex,
    isAPFSubextension_iff_finiteIndex]
  let := absoluteGaloisBaseChange_range_finiteIndex K M
  have := isAPF_of_finite K M
  constructor
  · intro h v hv
    let u := apfPhi K M v
    have hu : -1 ≤ u := apfPhi_mem_Ici K M hv
    have hindex := (Subgroup.finiteIndex_iff_comap_of_range ρ
      (apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u)).mp (h u hu)
    rw [comap_apfSubgroup_finiteBase K M i hu, apfPsi_apfPhi] at hindex
    exact hindex
  · intro h u hu
    apply (Subgroup.finiteIndex_iff_comap_of_range ρ
      (apfSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u)).mpr
    rw [comap_apfSubgroup_finiteBase K M i hu]
    exact h (apfPsi K M u) (IsAPF.apfPsi_mem_Ici K M hu)

end Valued

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- The spectral norm on the finite base for the APF index comparison. -/
noncomputable local instance baseChangeIndexNormedField : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
/-- The normed algebra structure on the finite base for the APF index comparison. -/
noncomputable local instance baseChangeIndexNormedAlgebra : NormedAlgebra K M :=
  spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
/-- The canonical separable-closure algebra for the APF index comparison. -/
noncomputable local instance baseChangeIndexClosureAlgebra : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'

local notation "ρ" =>
  MonoidHom.comp (Subgroup.subtype (IntermediateField.fixingSubgroup M))
    (MulEquiv.toMonoidHom (absoluteGaloisBaseChangeEquiv K M))

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

variable [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

omit [Algebra.IsSeparable K N] in
/-- The inertia product over the new base is the old product preimage. -/
theorem comap_apfInertiaSubgroup_finiteBase (i : N →ₐ[M] SeparableClosure M)
    {u : ℝ} (hu : 0 ≤ u) :
    (apfInertiaSubgroup K (baseChangedSeparableEmbedding K M i).fieldRange u).comap ρ =
      apfInertiaSubgroup M i.fieldRange (apfPsi K M u) := by
  have hψ : 0 ≤ apfPsi K M u := hu.trans (IsAPF.le_apfPsi K M u)
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.comap_inf,
    comap_apfSubgroup_finiteBase K M i (by linarith),
    comap_absoluteUpper_finiteBase K M (by norm_num : (-1 : ℝ) ≤ 0),
    apfPsi_zero, ← apfInertiaSubgroup_eq_inf M _ _ hψ]

/-- The new-base index is exactly the old-base relative tower factor. -/
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

/-- The public intrinsic indices factor through the finite base, without APF on N. -/
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

namespace FontaineWintenberger

open MeasureTheory Filter

section Calculus

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- At continuity points of the slope, its primitive has that derivative. -/
theorem IsAPF.hasDerivAt_apfPsi [IsAPF K L] {u : ℝ}
    (hc : ContinuousAt (apfHerbrandSlope K L) u) :
    HasDerivAt (apfPsi K L) (apfHerbrandSlope K L u) u := by
  apply intervalIntegral.integral_hasDerivAt_right
    (IsAPF.intervalIntegrable_apfHerbrandSlope K L 0 u) _ hc
  exact (IsAPF.monotone_apfHerbrandSlope
    K L).measurable.stronglyMeasurable.stronglyMeasurableAtFilter

/-- The APF primitive has its derivative outside a countable set. -/
theorem IsAPF.exists_apfPsi_derivative_countable [IsAPF K L] :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u : ℝ, u ∉ S →
      HasDerivAt (apfPsi K L) (apfHerbrandSlope K L u) u := by
  refine ⟨{u | ¬ ContinuousAt (apfHerbrandSlope K L) u},
    (IsAPF.monotone_apfHerbrandSlope K L).countable_not_continuousAt, ?_⟩
  intro u hu
  exact IsAPF.hasDerivAt_apfPsi K L (not_not.mp hu)

end Calculus

section FiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- The spectral norm on the finite base for composition of Herbrand functions. -/
noncomputable local instance baseChangeHerbrandNormedField : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
/-- The normed algebra structure on the finite base for Herbrand composition. -/
noncomputable local instance baseChangeHerbrandNormedAlgebra : NormedAlgebra K M :=
  spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
/-- The canonical separable-closure algebra for Herbrand composition. -/
noncomputable local instance baseChangeHerbrandClosureAlgebra : Algebra M (SeparableClosure M) :=
  (separableClosure M (AlgebraicClosure M)).algebra'

variable (N : Type*) [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K N]
local instance : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N

/-- The finite-base composite has the old-base slope off a countable set. -/
theorem IsAPF.exists_finiteBase_comp_derivative_countable [IsAPF K N] :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u : ℝ, 0 < u → u ∉ S →
      HasDerivAt ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N u) u := by
  have := isAPF_of_finite K M
  have hNM : IsAPF M N := (isAPF_finiteBase_iff K M).mp ‹_›
  obtain ⟨S₁, hS₁, hd₁⟩ := IsAPF.exists_apfPsi_derivative_countable K M
  obtain ⟨S₂, hS₂, hd₂⟩ := IsAPF.exists_apfPsi_derivative_countable M N
  refine ⟨S₁ ∪ (apfPsi K M ⁻¹' S₂),
    hS₁.union (hS₂.preimage (IsAPF.strictMono_apfPsi K M).injective), ?_⟩
  intro u hu hnot
  have hn₁ : u ∉ S₁ := fun h => hnot (Or.inl h)
  have hn₂ : apfPsi K M u ∉ S₂ := fun h => hnot (Or.inr h)
  have hψ : 0 ≤ apfPsi K M u := hu.le.trans (IsAPF.le_apfPsi K M u)
  have hd := (hd₂ (apfPsi K M u) hn₂).comp u (hd₁ u hn₁)
  have he : (apfIndex M N (apfPsi K M u) : ℝ) * (apfIndex K M u : ℝ) =
      (apfIndex K N u : ℝ) := by
    have he' := congrArg (fun n : ℕ => (n : ℝ))
      (apfIndex_eq_mul_finiteBase K M (N := N) hu.le)
    simpa only [Nat.cast_mul, mul_comm] using he'.symm
  simpa only [apfHerbrandSlope, max_eq_left hu.le, max_eq_left hψ, he] using hd

/-- The Herbrand integral composes across any finite, possibly nonnormal base. -/
theorem IsAPF.apfPsi_finiteBase_comp [IsAPF K N] (u : ℝ) :
    apfPsi M N (apfPsi K M u) = apfPsi K N u := by
  have : IsAPF M N := (isAPF_finiteBase_iff K M).mp ‹_›
  by_cases hu : 0 ≤ u
  · obtain ⟨S, hS, hd⟩ := IsAPF.exists_finiteBase_comp_derivative_countable K M N
    have hcont : ContinuousOn ((apfPsi M N) ∘ (apfPsi K M)) (Set.Icc 0 u) :=
      ((IsAPF.continuous_apfPsi M N).comp
        (IsAPF.continuous_apfPsi K M)).continuousOn
    have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N) hu hS hcont
      (fun v hv => hd v hv.1.1 hv.2)
      (IsAPF.intervalIntegrable_apfHerbrandSlope K N 0 u)
    conv_rhs => rw [apfPsi]
    simpa only [Function.comp_apply, apfPsi_zero, sub_zero] using h.symm
  · rw [apfPsi_of_nonpos K M (le_of_not_ge hu),
      apfPsi_of_nonpos M N (le_of_not_ge hu),
      apfPsi_of_nonpos K N (le_of_not_ge hu)]

end FiniteBase

end FontaineWintenberger
