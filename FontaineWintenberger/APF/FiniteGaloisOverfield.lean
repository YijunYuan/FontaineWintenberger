/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.FiniteNonnormal
public import FontaineWintenberger.APF.FiniteBound

/-!
# Intrinsic APF functions in an arbitrary finite Galois overfield

An embedding into the separable closure transports actual fixing subgroups
and upper groups, so the finite nonnormal formulas apply to the original fields.
-/

@[expose] public section

namespace FontaineWintenberger

section FixingSubgroup

variable {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N]

/-- Conjugation by a field isomorphism carries the actual fixing subgroup
to that of the image intermediate field. -/
theorem fixingSubgroup_map_autCongr (f : L ≃ₐ[K] N) (M : IntermediateField K L) :
    M.fixingSubgroup.map f.autCongr.toMonoidHom =
      (M.map f.toAlgHom).fixingSubgroup := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    change h ∈ M.fixingSubgroup at hh
    rw [IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
    rintro y ⟨x, hx, rfl⟩
    change (f.autCongr h) (f x) = f x
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply, hh x hx]
  · intro hg
    obtain ⟨h, rfl⟩ := f.autCongr.surjective g
    refine Subgroup.mem_map.mpr ⟨h, ?_, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
    intro x hx
    apply f.injective
    have he := hg (f x) ⟨x, hx, rfl⟩
    simpa only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply] using he

end FixingSubgroup

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

/-- The intrinsic index is computed in any actual finite Galois overfield,
without normality of the intermediate field. -/
theorem apfIndex_eq_subgroupRelIndex_of_finiteGalois {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K M u =
      ((M.fixingSubgroup ⊓
          upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) 0) ⊔
        upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).relIndex
          (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) 0) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e := j.equivFieldRange
  let : FiniteDimensional K j.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let : IsGalois K j.fieldRange := IsGalois.of_algEquiv e
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := ⟨j.fieldRange⟩
  rw [apfIndex_algEquiv K M (M.equivMap e.toAlgHom),
    apfIndex_eq_subgroupRelIndex K E (M.map e.toAlgHom) hu,
    ← fixingSubgroup_map_autCongr e M,
    ← upperRamificationGroup_map_autCongr K e (by norm_num : -1 ≤ (0 : ℝ)),
    ← upperRamificationGroup_map_autCongr K e (by linarith : -1 ≤ u),
    ← Subgroup.map_inf _ _ _ e.autCongr.injective, ← Subgroup.map_sup]
  exact Subgroup.relIndex_map_map_of_injective _ _ e.autCongr.injective

/-- The intrinsic nonnormal change of parameter uses the subgroup of the
original finite Galois overfield on its original spectral integer ring. -/
theorem apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois
    {u : ℝ} (hu : -1 ≤ u) :
    apfPsi K M u =
      herbrandFunction (R := spectralIntegerRing K L) M.fixingSubgroup
        (inverseHerbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u) := by
  by_cases hu' : u ≤ 0
  · rw [apfPsi_of_nonpos K M hu',
      subgroup_herbrandFunction_comp_inverse_of_nonpos _ _ hu hu']
  · rw [apfPsi_eq_integral_index K M (le_of_not_ge hu'),
      subgroup_herbrandFunction_comp_inverse_eq_integral _ _ (le_of_not_ge hu')]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (le_of_not_ge hu')]
    intro v hv
    dsimp only
    rw [apfIndex_eq_subgroupRelIndex_of_finiteGalois K L M hv.1,
      upperRamificationGroup_zero, lowerRamificationGroup_zero]

/-- The actual inverse change of parameter in any finite Galois overfield. -/
theorem apfPhi_eq_herbrand_comp_subgroup_inverse_of_finiteGalois
    {v : ℝ} (hv : -1 ≤ v) :
    apfPhi K M (isAPF_of_finite K M) v =
      herbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L)
        (inverseHerbrandFunction (R := spectralIntegerRing K L) M.fixingSubgroup v) := by
  apply (IsAPF.strictMono_apfPsi K M (isAPF_of_finite K M)).injective
  rw [apfPsi_apfPhi,
    apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K L M
      (herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ v)),
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ v),
    herbrandFunction_inverseHerbrandFunction _ hv]

/-- Ordinary restriction computes the full APF product index in any finite
Galois overfield; this retains its residue-degree factor. -/
theorem apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K (j.comp M.val).fieldRange u).index =
      (M.fixingSubgroup ⊔
        upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).index := by
  let e := j.equivFieldRange
  let : FiniteDimensional K j.fieldRange := Module.Finite.equiv e.toLinearEquiv
  let : IsGalois K j.fieldRange := IsGalois.of_algEquiv e
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := ⟨j.fieldRange⟩
  have hr : (j.comp M.val).fieldRange =
      (M.map e.toAlgHom).map E.toIntermediateField.val := by
    rw [IntermediateField.fieldRange_comp_val, IntermediateField.map_map]
    rfl
  rw [hr, apfSubgroup_map_eq_comap_sup_upper K E (M.map e.toAlgHom) hu,
    Subgroup.index_comap_of_surjective _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (SeparableClosure K)),
    ← fixingSubgroup_map_autCongr e M,
    ← upperRamificationGroup_map_autCongr K e hu, ← Subgroup.map_sup]
  exact Subgroup.index_map_equiv _ e.autCongr

/-- The full-group condition in the source first bound is detected by the
actual finite fixing subgroup and upper group. -/
theorem apfSubgroup_fieldRange_eq_top_iff_fixingSubgroup_sup_upper_eq_top
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (j.comp M.val).fieldRange u = ⊤ ↔
      M.fixingSubgroup ⊔
        upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u = ⊤ := by
  rw [← Subgroup.index_eq_one, ← Subgroup.index_eq_one,
    apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index K L M j hu]

/-- The actual extended first bound is the supremum where the finite
fixing-subgroup product is full, including both infinite endpoints. -/
theorem apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper :
    apfRamificationBound K M = sSup {x : EReal | ∃ u : ℝ, -1 ≤ u ∧
      M.fixingSubgroup ⊔
        upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u = ⊤ ∧
          x = (u : EReal)} := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [apfRamificationBound_eq_embedding K M (j.comp M.val)]
  congr 1
  ext x
  constructor <;> rintro ⟨u, hu, hg, rfl⟩
  · exact ⟨u, hu,
      (apfSubgroup_fieldRange_eq_top_iff_fixingSubgroup_sup_upper_eq_top K L M j hu).mp hg,
      rfl⟩
  · exact ⟨u, hu,
      (apfSubgroup_fieldRange_eq_top_iff_fixingSubgroup_sup_upper_eq_top K L M j hu).mpr hg,
      rfl⟩

end FontaineWintenberger
