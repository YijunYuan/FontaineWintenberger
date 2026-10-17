/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.StrictBaseChange

/-!
# Finite base change with the original abstract normed scalar field

All comparisons use the original norm and scalar maps on the finite new base.
The chosen common separable closure serves only to identify actual restrictions.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

namespace AbstractFiniteBase

section CommonClosure

variable (K : Type*) [Field K] (M : Type*) [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Algebra M (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]

local notation "S₀" => AlgHom.fieldRange (IsScalarTower.toAlgHom K M (SeparableClosure K))

local instance : FiniteDimensional K S₀ :=
  Module.Finite.equiv (IsScalarTower.toAlgHom K M (SeparableClosure
      K)).equivFieldRange.toLinearEquiv

local instance : Algebra.IsSeparable M (SeparableClosure K) :=
  Algebra.isSeparable_tower_top_of_isSeparable K M (SeparableClosure K)

omit [FiniteDimensional K M] [Algebra.IsSeparable K M] in
/-- The actual old closure is also a separable closure of the abstract finite base. -/
theorem isSepClosure : IsSepClosure M (SeparableClosure K) :=
  isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩

/-- The actual isomorphism of closures over the original abstract new base. -/
noncomputable def closureEquiv : SeparableClosure M ≃ₐ[M] SeparableClosure K := by
  let := isSepClosure K M
  exact IsSepClosure.equiv M (SeparableClosure M) (SeparableClosure K)

/-- Rebase an actual old-base finite Galois layer, without changing its carrier. -/
noncomputable def finiteLayer
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : S₀ ≤ E.toIntermediateField) :
    FiniteGaloisIntermediateField M (SeparableClosure K) := by
  let D : IntermediateField M (SeparableClosure K) :=
    { E.toIntermediateField.toSubfield with
      algebraMap_mem' := fun x => hME (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩) }
  let : Algebra K D := inferInstanceAs (Algebra K E)
  let : IsScalarTower K M D := IsScalarTower.of_algebraMap_eq (fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K M (SeparableClosure K) x))
  let : FiniteDimensional K D := inferInstanceAs (FiniteDimensional K E)
  let : FiniteDimensional M D := Module.Finite.right K M D
  let : IsGalois K D := inferInstanceAs (IsGalois K E)
  let : IsGalois M D := IsGalois.tower_top_of_isGalois K M D
  exact { D with }

omit [Algebra.IsSeparable K M] in
/-- Old-base normal overfields are cofinal over the abstract new base. -/
theorem exists_layer (D : FiniteGaloisIntermediateField M (SeparableClosure K)) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
      (hME : S₀ ≤ E.toIntermediateField), D ≤ finiteLayer K M E hME := by
  let : FiniteDimensional K D := FiniteDimensional.trans K M D
  let T := D.toIntermediateField.restrictScalars K
  let : FiniteDimensional K T := inferInstanceAs (FiniteDimensional K D)
  let E := finiteGaloisNormalClosure K T
  have hME : S₀ ≤ E.toIntermediateField := by
    rintro x ⟨y, rfl⟩
    exact le_finiteGaloisNormalClosure K T (D.toIntermediateField.algebraMap_mem y)
  exact ⟨E, hME, le_finiteGaloisNormalClosure K T⟩

omit [FiniteDimensional K M] [Algebra.IsSeparable K M] in
/-- Scalar restriction on the common closure has precisely the actual fixing subgroup as range. -/
theorem range_restrictScalars :
    (AlgEquiv.restrictScalarsHom K (S := M) (A := SeparableClosure K)).range =
      (S₀).fixingSubgroup := by
  let e := (IsScalarTower.toAlgHom K M (SeparableClosure K)).equivFieldRange
  let : Algebra M S₀ := e.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower M S₀ (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let f := AlgEquiv.extendScalarsHomOfSurjective
    (R := M) (S := S₀) (A := SeparableClosure K) e.surjective
  have hf : (S₀).fixingSubgroup.subtype.comp ((S₀).fixingSubgroupEquiv.symm.toMonoidHom.comp
      f.toMonoidHom) = AlgEquiv.restrictScalarsHom K (S := M) (A := SeparableClosure K) := by
    ext g x
    rfl
  rw [← hf, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr ((S₀).fixingSubgroupEquiv.symm.surjective.comp f.surjective),
    Subgroup.map_top, Subgroup.range_subtype]

end CommonClosure

section ValuedCommonClosure

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Algebra M (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]

variable [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)]

local notation "S₀" => AlgHom.fieldRange (IsScalarTower.toAlgHom K M (SeparableClosure K))

local instance : FiniteDimensional K S₀ :=
  Module.Finite.equiv (IsScalarTower.toAlgHom K M (SeparableClosure
      K)).equivFieldRange.toLinearEquiv

omit [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] [Algebra.IsSeparable K M] in
/-- All new-base upper conditions are tested on actual old-base normal overfields. -/
theorem mem_upper_iff_cofinal {v : ℝ} (hv : -1 ≤ v)
    (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) v ↔
      ∀ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (hME : S₀ ≤ E.toIntermediateField),
        g.restrictNormal (finiteLayer K M E hME) ∈
          upperRamificationGroup (R := spectralIntegerRing M (finiteLayer K M E hME))
            (finiteLayer K M E hME ≃ₐ[M] finiteLayer K M E hME) v := by
  let F (j : {E : FiniteGaloisIntermediateField K (SeparableClosure K) //
      S₀ ≤ E.toIntermediateField}) := finiteLayer K M j.1 j.2
  have hF : ∀ D : FiniteGaloisIntermediateField M (SeparableClosure K), ∃ j, D ≤ F j := by
    intro D
    obtain ⟨E, hME, hDE⟩ := exists_layer K M D
    exact ⟨⟨E, hME⟩, hDE⟩
  rw [mem_upperRamificationGroupInfinite_iff_cofinal M (SeparableClosure K) F hF hv g]
  exact ⟨fun h E hME => h ⟨E, hME⟩, fun h j => h j.1 j.2⟩

omit [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)] in
/-- A restriction to an actual finite layer detects the upper condition over either base. -/
theorem finite_restriction_mem_upper_iff
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : S₀ ≤ E.toIntermediateField) {u : ℝ} (hu : -1 ≤ u)
    (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g.restrictNormal (finiteLayer K M E hME) ∈
        upperRamificationGroup (R := spectralIntegerRing M (finiteLayer K M E hME))
          (finiteLayer K M E hME ≃ₐ[M] finiteLayer K M E hME) (apfPsi K M u) ↔
      (g.restrictScalars K).restrictNormal E ∈
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  let : Algebra M E := inferInstanceAs (Algebra M (finiteLayer K M E hME))
  let : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq (fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K M (SeparableClosure K) x))
  let : FiniteDimensional M E := Module.Finite.right K M E
  let : Algebra.IsSeparable M E := Algebra.isSeparable_tower_top_of_isSeparable K M E
  let : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.tower_top (K := K) M
  let q : E ≃ₐ[M] E := g.restrictNormal (finiteLayer K M E hME)
  have hq : q.restrictScalars K = (g.restrictScalars K).restrictNormal E := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes g (finiteLayer K M E hME) x).trans
      (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) E x).symm
  change q ∈ upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
    (apfPsi K M u) ↔ _
  rw [finiteTower_mem_upper_iff_restrictScalars K E M hu q, hq]

/-- Actual scalar restriction changes the infinite upper parameter by the intrinsic integral. -/
theorem mem_upper_finiteBase_iff {u : ℝ} (hu : -1 ≤ u)
    (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) (apfPsi K M u) ↔
      g.restrictScalars K ∈ upperRamificationGroupInfinite K (SeparableClosure K) u := by
  have hv := IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu
  rw [mem_upper_iff_cofinal K M hv g,
    mem_upperRamificationGroupInfinite_containing_base_iff K S₀ hu (g.restrictScalars K)]
  exact forall_congr' fun E => forall_congr' fun hME =>
    finite_restriction_mem_upper_iff K M E hME hu g

/-- The actual common-closure homomorphism preserves original field automorphisms. -/
noncomputable def closureHom :
    (SeparableClosure M ≃ₐ[M] SeparableClosure M) →*
      (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  (AlgEquiv.restrictScalarsHom K).comp (closureEquiv K M).autCongr.toMonoidHom

omit [IsUltrametricDist K] [IsUltrametricDist M] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [CompleteSpace M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)] in
/-- The actual closure homomorphism commutes with the chosen closure isomorphism. -/
theorem closureHom_apply (g : SeparableClosure M ≃ₐ[M] SeparableClosure M)
    (x : SeparableClosure M) :
    closureHom K M g (closureEquiv K M x) = closureEquiv K M (g x) := by
  change closureEquiv K M (g ((closureEquiv K M).symm (closureEquiv K M x))) = _
  rw [AlgEquiv.symm_apply_apply]

omit [IsUltrametricDist K] [IsUltrametricDist M] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [CompleteSpace M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)] in
/-- Its range is exactly the subgroup fixing the original embedded finite base. -/
theorem closureHom_range : (closureHom K M).range = (S₀).fixingSubgroup := by
  rw [closureHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (closureEquiv K M).autCongr.surjective,
    Subgroup.map_top, range_restrictScalars K M]

omit [IsUltrametricDist K] [IsUltrametricDist M] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
    [CompleteSpace M] [Algebra.IsSeparable K M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := M)).valuationSubring)] in
/-- The actual finite-base closure homomorphism has finite-index range. -/
theorem closureHom_range_finiteIndex : (closureHom K M).range.FiniteIndex := by
  rw [closureHom_range K M]
  let : Finite ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ (S₀).fixingSubgroup) :=
    (S₀).fixingSubgroup.quotient_finite_of_isOpen (IntermediateField.fixingSubgroup_isOpen S₀)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Absolute upper groups over the original normed new base are genuine preimages. -/
theorem comap_upper {u : ℝ} (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).comap (closureHom K M) =
      absoluteUpperRamificationGroup M (apfPsi K M u) := by
  ext g
  have hv := IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu
  exact ((mem_upperRamificationGroupInfinite_autCongr_iff M (closureEquiv K M) hv g).symm.trans
    (mem_upper_finiteBase_iff K M hu ((closureEquiv K M).autCongr g))).symm

variable {N : Type*} [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The original old-base embedding induced from a new-base separable embedding. -/
noncomputable def embedding (i : N →ₐ[M] SeparableClosure M) : N →ₐ[K] SeparableClosure K :=
  ((closureEquiv K M).toAlgHom.comp i).restrictScalars K

omit [IsUltrametricDist K] [IsUltrametricDist M] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [CompleteSpace M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)] in
/-- The induced old-base image contains the actual image of the finite new base. -/
theorem image_le_embedding (i : N →ₐ[M] SeparableClosure M) :
    S₀ ≤ (embedding K M i).fieldRange := by
  rintro x ⟨y, rfl⟩
  refine AlgHom.mem_fieldRange.mpr ⟨algebraMap M N y, ?_⟩
  change closureEquiv K M (i (algebraMap M N y)) = algebraMap M (SeparableClosure K) y
  rw [i.commutes, (closureEquiv K M).commutes]

omit [IsUltrametricDist K] [IsUltrametricDist M] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
    [CompleteSpace M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := M)).valuationSubring)] in
/-- Equivariance identifies the actual two fixing subgroups. -/
theorem comap_fixing (i : N →ₐ[M] SeparableClosure M) :
    (embedding K M i).fieldRange.fixingSubgroup.comap (closureHom K M) =
      i.fieldRange.fixingSubgroup := by
  ext g
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp x.property
    apply (closureEquiv K M).injective
    have h' := h ⟨embedding K M i y, AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩
    change closureHom K M g (closureEquiv K M (i y)) = closureEquiv K M (i y) at h'
    rw [closureHom_apply] at h'
    rw [← hy]
    exact h'
  · intro h x
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp x.property
    change closureHom K M g (x : SeparableClosure K) = x
    rw [← hy]
    change closureHom K M g (closureEquiv K M (i y)) = closureEquiv K M (i y)
    rw [closureHom_apply]
    exact congrArg (closureEquiv K M) (h ⟨i y, AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩)

/-- The actual APF normal product over the abstract base is the old product preimage. -/
theorem comap_apf (i : N →ₐ[M] SeparableClosure M) {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K (embedding K M i).fieldRange u).comap (closureHom K M) =
      apfSubgroup M i.fieldRange (apfPsi K M u) := by
  have hA : (embedding K M i).fieldRange.fixingSubgroup ≤ (closureHom K M).range := by
    rw [closureHom_range K M]
    exact IntermediateField.fixingSubgroup_le (image_le_embedding K M i)
  rw [apfSubgroup, ← Subgroup.comap_sup_eq_of_normal_right_of_le_range _ _ _ hA,
    comap_fixing K M i, comap_upper K M hu]
  rfl

variable [Algebra.IsSeparable K N]
variable [Algebra.IsSeparable M N]

/-- The abstract original normed base obeys finite-base APF invariance. -/
theorem isAPF_iff : IsAPF K N ↔ IsAPF M N := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [isAPF_iff_embedding K N (embedding K M i), isAPF_iff_embedding M N i,
    isAPFSubextension_iff_finiteIndex, isAPFSubextension_iff_finiteIndex]
  let := closureHom_range_finiteIndex K M
  have hM := isAPF_of_finite K M
  constructor
  · intro h v hv
    let u := apfPhi K M hM v
    have hu : -1 ≤ u := apfPhi_mem_Ici K M hM hv
    have hindex := (Subgroup.finiteIndex_iff_comap_of_range (closureHom K M)
      (apfSubgroup K (embedding K M i).fieldRange u)).mp (h u hu)
    rw [comap_apf K M i hu, apfPsi_apfPhi] at hindex
    exact hindex
  · intro h u hu
    apply (Subgroup.finiteIndex_iff_comap_of_range (closureHom K M)
      (apfSubgroup K (embedding K M i).fieldRange u)).mpr
    rw [comap_apf K M i hu]
    exact h (apfPsi K M u) (IsAPF.apfPsi_mem_Ici K M hM hu)

omit [Algebra.IsSeparable K N] [Algebra.IsSeparable M N] in
/-- The original inertia product over the abstract base is an actual preimage. -/
theorem comap_inertia (i : N →ₐ[M] SeparableClosure M) {u : ℝ} (hu : 0 ≤ u) :
    (apfInertiaSubgroup K (embedding K M i).fieldRange u).comap (closureHom K M) =
      apfInertiaSubgroup M i.fieldRange (apfPsi K M u) := by
  have hψ : 0 ≤ apfPsi K M u := hu.trans (IsAPF.le_apfPsi K M (isAPF_of_finite K M) u)
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.comap_inf,
    comap_apf K M i (by linarith), comap_upper K M (by norm_num : (-1 : ℝ) ≤ 0),
    apfPsi_zero, ← apfInertiaSubgroup_eq_inf M _ _ hψ]

omit [Algebra.IsSeparable K N] in
/-- The abstract-base index is the actual relative inertia index factor. -/
theorem index_eq_factor (i : N →ₐ[M] SeparableClosure M) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex M N (apfPsi K M u) =
      apfTowerIndexFactor K S₀ (embedding K M i).fieldRange u := by
  have hzero : (absoluteUpperRamificationGroup K 0).comap (closureHom K M) =
      absoluteUpperRamificationGroup M 0 := by
    simpa only [apfPsi_zero] using comap_upper K M (by norm_num : (-1 : ℝ) ≤ 0)
  rw [apfIndex_eq_embedding M N i, apfInertiaIndex, ← comap_inertia K M i hu,
    ← hzero, Subgroup.relIndex_comap, Subgroup.map_comap_eq, closureHom_range K M]
  simpa only [apfTowerIndexFactor, apfInertiaSubgroup, inf_comm] using
    (Subgroup.relIndex_sup_sup_normal
      ((embedding K M i).fieldRange.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
      ((S₀).fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0)
      (absoluteUpperRamificationGroup K u)).symm

/-- Actual intrinsic indices factor over the abstract original normed base. -/
theorem index_mul {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K N u = apfIndex K M u * apfIndex M N (apfPsi K M u) := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings M N
  rw [apfIndex_eq_embedding K N (embedding K M i)]
  have hfac := apfIndex_eq_mul_towerIndexFactor K S₀ (embedding K M i).fieldRange
    (image_le_embedding K M i) hu
  rw [apfIndex_eq_embedding K _ (embedding K M i).fieldRange.val,
    IntermediateField.fieldRange_val, ← index_eq_factor K M i hu] at hfac
  rw [← apfIndex_algEquiv K M
    (IsScalarTower.toAlgHom K M (SeparableClosure K)).equivFieldRange] at hfac
  exact hfac

open MeasureTheory Filter
open scoped ENNReal

/-- The derivative of the actual finite-base composite agrees off a countable set. -/
theorem exists_comp_derivative (hN : IsAPF K N) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u : ℝ, 0 < u → u ∉ S →
      HasDerivAt ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N u) u := by
  have hM := isAPF_of_finite K M
  have hNM := (isAPF_iff K M).mp hN
  obtain ⟨S₁, hS₁, hd₁⟩ := IsAPF.exists_apfPsi_derivative_countable K M hM
  obtain ⟨S₂, hS₂, hd₂⟩ := IsAPF.exists_apfPsi_derivative_countable M N hNM
  refine ⟨S₁ ∪ (apfPsi K M ⁻¹' S₂),
    hS₁.union (hS₂.preimage (IsAPF.strictMono_apfPsi K M hM).injective), ?_⟩
  intro u hu hnot
  have hn₁ : u ∉ S₁ := fun h => hnot (Or.inl h)
  have hn₂ : apfPsi K M u ∉ S₂ := fun h => hnot (Or.inr h)
  have hψ : 0 ≤ apfPsi K M u := hu.le.trans (IsAPF.le_apfPsi K M hM u)
  have hd := (hd₂ (apfPsi K M u) hn₂).comp u (hd₁ u hn₁)
  have he : (apfIndex M N (apfPsi K M u) : ℝ) * (apfIndex K M u : ℝ) =
      (apfIndex K N u : ℝ) := by
    have he' := congrArg (fun n : ℕ => (n : ℝ)) (index_mul K M (N := N) hu.le)
    simpa only [Nat.cast_mul, mul_comm] using he'.symm
  simpa only [apfHerbrandSlope, max_eq_left hu.le, max_eq_left hψ, he] using hd

/-- Genuine Herbrand integrals compose over the original normed finite base on all real
parameters. -/
theorem psi_comp (hN : IsAPF K N) (u : ℝ) :
    apfPsi M N (apfPsi K M u) = apfPsi K N u := by
  by_cases hu : 0 ≤ u
  · obtain ⟨S, hS, hd⟩ := exists_comp_derivative K M hN
    have hcont : ContinuousOn ((apfPsi M N) ∘ (apfPsi K M)) (Set.Icc 0 u) :=
      ((IsAPF.continuous_apfPsi M N ((isAPF_iff K M).mp hN)).comp
        (IsAPF.continuous_apfPsi K M (isAPF_of_finite K M))).continuousOn
    have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      ((apfPsi M N) ∘ (apfPsi K M)) (apfHerbrandSlope K N) hu hS hcont
      (fun v hv => hd v hv.1.1 hv.2)
      (IsAPF.intervalIntegrable_apfHerbrandSlope K N hN 0 u)
    conv_rhs => rw [apfPsi]
    simpa only [Function.comp_apply, apfPsi_zero, sub_zero] using h.symm
  · rw [apfPsi_of_nonpos K M (le_of_not_ge hu),
      apfPsi_of_nonpos M N (le_of_not_ge hu), apfPsi_of_nonpos K N (le_of_not_ge hu)]

/-- The actual strictness ratios satisfy the original finite-base identity. -/
theorem ratio (hN : IsAPF K N) {u : ℝ} (hu : 0 ≤ u) :
    apfStrictnessRatio M N (apfPsi K M u) =
      (apfIndex K M u : ℝ≥0∞) * apfStrictnessRatio K N u := by
  have hM := isAPF_of_finite K M
  have hNM := (isAPF_iff K M).mp hN
  have hψ : 0 ≤ apfPsi K M u := hu.trans (IsAPF.le_apfPsi K M hM u)
  have ha : (0 : ℝ) < (apfIndex K M u : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos K M hM hu)
  have hb : (0 : ℝ) < (apfIndex M N (apfPsi K M u) : ℝ) :=
    Nat.cast_pos.mpr (IsAPF.apfIndex_pos M N hNM hψ)
  simp only [apfStrictnessRatio]
  rw [psi_comp K M hN u, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply congrArg ENNReal.ofReal
  have he : (apfIndex K N u : ℝ) =
      (apfIndex K M u : ℝ) * (apfIndex M N (apfPsi K M u) : ℝ) := by
    exact_mod_cast index_mul K M (N := N) hu
  rw [he]
  field_simp [ne_of_gt ha, ne_of_gt hb]

omit [IsUltrametricDist M] [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)] [CompleteSpace M]
    [IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)] in
/-- Finite-base slope stabilization holds for the actual abstract base. -/
theorem exists_index_constant :
    ∃ C : ℕ, 0 < C ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, b ≤ u → apfIndex K M u = C := by
  obtain ⟨C, hC, b, hb, hidx⟩ := exists_apfIndex_finite_constant K S₀
  refine ⟨C, hC, b, hb, ?_⟩
  intro u hu
  rw [apfIndex_algEquiv K M (IsScalarTower.toAlgHom K M (SeparableClosure K)).equivFieldRange]
  exact hidx u hu

/-- The actual strictness lower limits differ by a positive finite multiplier. -/
theorem exists_liminf_mul (hN : IsAPF K N) :
    ∃ C : ℕ, 0 < C ∧ liminf (apfStrictnessRatio M N) atTop =
      (C : ℝ≥0∞) * liminf (apfStrictnessRatio K N) atTop := by
  obtain ⟨C, hC, b, hb, hidx⟩ := exists_index_constant K M
  refine ⟨C, hC, ?_⟩
  have hev : (apfStrictnessRatio M N ∘ apfPsi K M) =ᶠ[atTop]
      (fun u => (C : ℝ≥0∞) * apfStrictnessRatio K N u) :=
    eventually_atTop.mpr ⟨b, fun u hu => by
      rw [Function.comp_apply, ratio K M hN (hb.trans hu), hidx u hu]⟩
  have he := liminf_congr hev
  rw [ENNReal.liminf_const_mul_of_ne_top (by simp : (C : ℝ≥0∞) ≠ ⊤)] at he
  exact (IsAPF.liminf_comp_apfPsi K M (isAPF_of_finite K M)
    (apfStrictnessRatio M N)).symm.trans he

/-- Strict APF is invariant over the original abstract compatible normed finite base. -/
theorem isStrictlyAPF_iff : IsStrictlyAPF K N ↔ IsStrictlyAPF M N := by
  by_cases hN : IsAPF K N
  · have hNM := (isAPF_iff K M).mp hN
    obtain ⟨C, hC, he⟩ := exists_liminf_mul K M hN
    simp only [IsStrictlyAPF, hN, hNM, true_and]
    rw [he, ENNReal.mul_pos_iff]
    exact ⟨fun hp => ⟨Nat.cast_pos.mpr hC, hp⟩, And.right⟩
  · constructor
    · intro h
      exact (hN h.1).elim
    · intro h
      exact (hN ((isAPF_iff K M).mpr h.1)).elim

end ValuedCommonClosure

end AbstractFiniteBase

section AbstractNormedBase

open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
variable (N : Type*) [Field N] [Algebra K N] [Algebra M N]
    [IsScalarTower K M N] [Algebra.IsSeparable K N]

/-- APF is invariant under finite change to any abstract scalar field with its original compatible
norm. -/
theorem isAPF_finiteBase_iff_of_normedAlgebra :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    IsAPF K N ↔ IsAPF M N := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom i
  exact AbstractFiniteBase.isAPF_iff K M

/-- Actual intrinsic inertia indices factor over any abstract finite compatible normed base. -/
theorem apfIndex_eq_mul_finiteBase_of_normedAlgebra {u : ℝ} (hu : 0 ≤ u) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    apfIndex K N u = apfIndex K M u * apfIndex M N (apfPsi K M u) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom i
  exact AbstractFiniteBase.index_mul K M hu

/-- The intrinsic Herbrand integral composes over any abstract finite compatible normed base. -/
theorem IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra (hN : IsAPF K N) (u : ℝ) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    apfPsi M N (apfPsi K M u) = apfPsi K N u := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom i
  exact AbstractFiniteBase.psi_comp K M hN u

/-- The actual strictness ratio is preserved with the genuine finite-base inertia factor. -/
theorem IsAPF.apfStrictnessRatio_finiteBase_of_normedAlgebra
    (hN : IsAPF K N) {u : ℝ} (hu : 0 ≤ u) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    apfStrictnessRatio M N (apfPsi K M u) =
      (apfIndex K M u : ℝ≥0∞) * apfStrictnessRatio K N u := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom i
  exact AbstractFiniteBase.ratio K M hN hu

/-- Strict APF is invariant under any abstract finite change of base with its original norm. -/
theorem isStrictlyAPF_finiteBase_iff_of_normedAlgebra :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    IsStrictlyAPF K N ↔ IsStrictlyAPF M N := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom i
  exact AbstractFiniteBase.isStrictlyAPF_iff K M

end AbstractNormedBase

end FontaineWintenberger
