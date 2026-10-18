/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Basic

/-!
# APF for abstract separable extensions

Embeddings into the separable closure exist and are conjugate under its actual
Galois group. Normality of the absolute upper groups makes APF independent of
the embedding. The public predicate therefore applies to arbitrary separable
field extensions, with no normality or finiteness assumption.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- Conjugation carries the actual APF subgroup onto that of the conjugate field. -/
theorem apfSubgroup_map (L : IntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (u : ℝ) :
    apfSubgroup K (L.map σ.toAlgHom) u = MulAut.conj σ • apfSubgroup K L u := by
  simp only [apfSubgroup, IsGalois.map_fixingSubgroup, Subgroup.smul_sup,
    Subgroup.Normal.conj_smul_eq_self]

theorem apfSubgroup_map_index (L : IntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (u : ℝ) :
    (apfSubgroup K (L.map σ.toAlgHom) u).index = (apfSubgroup K L u).index := by
  rw [apfSubgroup_map, Subgroup.pointwise_smul_def]
  exact Subgroup.index_map_equiv _ (MulAut.conj σ)

theorem isAPFSubextension_map_iff (L : IntermediateField K (SeparableClosure K))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    IsAPFSubextension K (L.map σ.toAlgHom) ↔ IsAPFSubextension K L := by
  simp only [isAPFSubextension_iff_finiteIndex, Subgroup.finiteIndex_iff,
    apfSubgroup_map_index]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

omit [IsCompleteDiscreteValuedField K] in
/-- Every abstract separable extension has an actual separable-closure embedding. -/
theorem nonempty_separableClosure_embeddings : Nonempty (L →ₐ[K] SeparableClosure K) :=
  ⟨IsSepClosed.lift⟩

omit [IsCompleteDiscreteValuedField K] [Algebra.IsSeparable K L] in
/-- Two separable-closure embeddings are conjugate by an actual automorphism. -/
theorem exists_aut_comp_separableClosure_embeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, σ.toAlgHom.comp i = j := by
  let e := i.equivFieldRange.symm.trans j.equivFieldRange
  let σ := e.liftNormal (SeparableClosure K)
  refine ⟨σ, ?_⟩
  ext x
  simpa [σ, e] using AlgEquiv.liftNormal_commutes e (SeparableClosure K)
    (i.equivFieldRange x)

omit [Algebra.IsSeparable K L] in
theorem isAPFSubextension_fieldRange_iff (i j : L →ₐ[K] SeparableClosure K) :
    IsAPFSubextension K i.fieldRange ↔ IsAPFSubextension K j.fieldRange := by
  obtain ⟨σ, hσ⟩ := exists_aut_comp_separableClosure_embeddings K L i j
  have hr : i.fieldRange.map σ.toAlgHom = j.fieldRange := by
    rw [AlgHom.map_fieldRange, hσ]
  rw [← hr]
  exact (isAPFSubextension_map_iff K i.fieldRange σ).symm

/-- Arithmetic profiniteness of an abstract separable field extension. -/
def IsAPF (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] : Prop :=
  ∀ i : L →ₐ[K] SeparableClosure K, IsAPFSubextension K i.fieldRange

/-- The public APF predicate can be tested using any specified embedding. -/
theorem isAPF_iff_embedding (i : L →ₐ[K] SeparableClosure K) :
    IsAPF K L ↔ IsAPFSubextension K i.fieldRange := by
  constructor
  · exact fun h ↦ h i
  · intro h j
    exact (isAPFSubextension_fieldRange_iff K L i j).mp h

/-- The embedding quantifier in `IsAPF` is nonvacuous. -/
theorem isAPF_iff_exists_embedding :
    IsAPF K L ↔ ∃ i : L →ₐ[K] SeparableClosure K, IsAPFSubextension K i.fieldRange := by
  constructor
  · intro h
    obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
    exact ⟨i, h i⟩
  · rintro ⟨i, hi⟩
    exact (isAPF_iff_embedding K L i).mpr hi

theorem isAPF_iff_subextension (E : IntermediateField K (SeparableClosure K)) :
    IsAPF K E ↔ IsAPFSubextension K E := by
  simpa only [IntermediateField.fieldRange_val] using isAPF_iff_embedding K E E.val

/-- Every finite separable abstract extension is APF. -/
theorem isAPF_of_finite [FiniteDimensional K L] : IsAPF K L := by
  intro i
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  exact isAPFSubextension_of_finite K i.fieldRange

variable {L}
variable {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]

/-- APF descends along every algebra embedding, including nonnormal subextensions. -/
theorem IsAPF.of_algHom (hL : IsAPF K L) (f : M →ₐ[K] L) : IsAPF K M := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  have hr : (i.comp f).fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f a, ha⟩
  exact (isAPF_iff_embedding K M (i.comp f)).mpr (IsAPFSubextension.of_le K (hL i) hr)

theorem isAPF_algEquiv (e : L ≃ₐ[K] M) : IsAPF K L ↔ IsAPF K M := by
  constructor
  · exact fun h ↦ IsAPF.of_algHom K h e.symm.toAlgHom
  · exact fun h ↦ IsAPF.of_algHom K h e.toAlgHom

end FontaineWintenberger
