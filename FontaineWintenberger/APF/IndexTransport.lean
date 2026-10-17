/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Abstract
public import FontaineWintenberger.APF.Index

/-!
# The intrinsic inertia index of a separable extension

Conjugation preserves both the inertia subgroup and the APF subgroup, hence
their actual relative index. An embedding into the separable closure therefore
defines an index for an abstract extension, independent of that embedding.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]

theorem apfInertiaSubgroup_map (L : IntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (u : ℝ) :
    apfInertiaSubgroup K (L.map σ.toAlgHom) u =
      MulAut.conj σ • apfInertiaSubgroup K L u := by
  simp only [apfInertiaSubgroup, IsGalois.map_fixingSubgroup, Subgroup.smul_sup,
    Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self]

theorem apfInertiaIndex_map (L : IntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (u : ℝ) :
    apfInertiaIndex K (L.map σ.toAlgHom) u = apfInertiaIndex K L u := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_map]
  conv_lhs =>
    arg 2
    rw [← Subgroup.Normal.conj_smul_eq_self σ (absoluteUpperRamificationGroup K 0)]
  simp only [Subgroup.pointwise_smul_def]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj σ).injective

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

omit [Algebra.IsSeparable K L] in
theorem apfInertiaIndex_fieldRange_eq (i j : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    apfInertiaIndex K i.fieldRange u = apfInertiaIndex K j.fieldRange u := by
  obtain ⟨σ, hσ⟩ := exists_aut_comp_separableClosure_embeddings K L i j
  have hr : i.fieldRange.map σ.toAlgHom = j.fieldRange := by
    rw [AlgHom.map_fieldRange, hσ]
  rw [← hr, apfInertiaIndex_map]

/-- The actual inertia-relative index, independent of the separable embedding. -/
noncomputable def apfIndex (u : ℝ) : ℕ :=
  apfInertiaIndex K (IsSepClosed.lift : L →ₐ[K] SeparableClosure K).fieldRange u

theorem apfIndex_eq_embedding (i : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    apfIndex K L u = apfInertiaIndex K i.fieldRange u :=
  apfInertiaIndex_fieldRange_eq K L _ i u

@[simp]
theorem apfIndex_zero : apfIndex K L 0 = 1 :=
  apfInertiaIndex_zero K _

theorem IsAPF.apfIndex_pos (hL : IsAPF K L) {u : ℝ} (hu : 0 ≤ u) :
    0 < apfIndex K L u :=
  IsAPFSubextension.inertiaIndex_pos K (hL _) u hu

theorem IsAPF.apfIndex_monotoneOn (hL : IsAPF K L) :
    MonotoneOn (apfIndex K L) (Set.Ici (0 : ℝ)) :=
  IsAPFSubextension.inertiaIndex_monotoneOn K (hL _)

theorem apfIndex_algEquiv {M : Type*} [Field M] [Algebra K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) (u : ℝ) :
    apfIndex K L u = apfIndex K M u := by
  let j : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfIndex_eq_embedding K L (j.comp e.toAlgHom), apfIndex_eq_embedding K M j]
  have hr : (j.comp e.toAlgHom).fieldRange = j.fieldRange := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e.symm b, by simp⟩
  rw [hr]

end FontaineWintenberger
