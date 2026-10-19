/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Finite.Galois
public import FontaineWintenberger.Ramification.Herbrand.Subgroup

/-!
# APF functions of finite nonnormal extensions

## Finite non-Galois APF change of parameter

Ordinary restriction to a finite Galois overfield identifies the
fixing subgroup of an arbitrary intermediate field and its inertia coset index.

## Intrinsic APF functions in an arbitrary finite Galois overfield

An embedding into the separable closure transports fixing subgroups
and upper groups, so the finite nonnormal formulas apply to the fields.

## Main results

* `apfSubgroup_map_eq_comap_sup_upper`: The APF product of a nonnormal finite intermediate field is
  a restriction preimage.
* `fixingSubgroup_sup_upper_inf_zero`: Inertia intersection of the finite fixing-subgroup product.
* `apfInertiaIndex_map_eq_subgroupRelIndex`: The intrinsic APF inertia index of an arbitrary finite
  intermediate field.
* `apfIndex_eq_subgroupRelIndex`: The abstract finite field has the same index, without choosing a
  normality instance.
* `apfPsi_eq_subgroup_herbrand_comp_inverse`: The non-Galois finite APF integral is the subgroup
  change of parameter.
* `apfPhi_eq_herbrand_comp_subgroup_inverse`: The inverse change of parameter uses the same finite
  overfield and subgroup.
* `fixingSubgroup_map_autCongr`: Conjugation by a field isomorphism carries the fixing subgroup to
  that of the image intermediate field.
* `apfIndex_eq_subgroupRelIndex_of_finiteGalois`: The intrinsic index is computed in any finite
  Galois overfield, without normality of the intermediate field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField 𝓀[K]]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
variable (M : IntermediateField K E)

local notation "ρ" => AlgEquiv.restrictNormalHom E
local notation "H₀" => M.fixingSubgroup
local notation "U₀" => upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E)

/-- The APF product of a nonnormal finite intermediate field is a restriction preimage. -/
theorem apfSubgroup_map_eq_comap_sup_upper {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (M.map E.toIntermediateField.val) u =
      (H₀ ⊔ U₀ u).comap ρ := by
  have hfix : (M.map E.toIntermediateField.val).fixingSubgroup = (H₀).comap ρ := by
    exact IntermediateField.map_fixingSubgroup (F := K) (E := E)
      (E' := SeparableClosure K) (L := M)
  have hker : E.toIntermediateField.fixingSubgroup ≤ (H₀).comap ρ := by
    rw [← IntermediateField.restrictNormalHom_ker E.toIntermediateField]
    intro g hg
    change ρ g ∈ H₀
    rw [MonoidHom.mem_ker.mp hg]
    exact (H₀).one_mem
  unfold apfSubgroup
  rw [hfix]
  calc
    _ = (H₀).comap ρ ⊔
        (E.toIntermediateField.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u) := by
      rw [← sup_assoc, sup_eq_left.mpr hker]
    _ = (H₀).comap ρ ⊔ (U₀ u).comap ρ := by
      rw [← apfSubgroup, apfSubgroup_eq_comap_upper K E hu]
    _ = _ := Subgroup.comap_sup_eq ρ _ _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (SeparableClosure K))

omit [PerfectField 𝓀[K]] in
/-- Inertia intersection of the finite fixing-subgroup product. -/
theorem fixingSubgroup_sup_upper_inf_zero {u : ℝ} (hu : 0 ≤ u) :
    (H₀ ⊔ U₀ u) ⊓ U₀ 0 = (H₀ ⊓ U₀ 0) ⊔ U₀ u := by
  have hU : U₀ u ≤ U₀ 0 := upperRamificationGroup_antitoneOn
    (R := spectralIntegerRing K E) (E ≃ₐ[K] E) (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u)
        hu
  apply le_antisymm
  · rintro g ⟨hg, hg₀⟩
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hh₀ : h ∈ U₀ 0 := by
      have := (U₀ 0).mul_mem hg₀ ((U₀ 0).inv_mem (hU hn))
      simpa only [mul_inv_cancel_right] using this
    exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hh₀⟩, n, hn, rfl⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hU)

/-- The intrinsic APF inertia index of an arbitrary finite intermediate field. -/
theorem apfInertiaIndex_map_eq_subgroupRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfInertiaIndex K (M.map E.toIntermediateField.val) u =
      ((H₀ ⊓ U₀ 0) ⊔ U₀ u).relIndex (U₀ 0) := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_eq_inf K _ u hu, Subgroup.inf_relIndex_right,
    apfSubgroup_map_eq_comap_sup_upper K E M (by linarith), Subgroup.relIndex_comap,
    absolute_map_upperRamificationGroup K E 0 (by norm_num),
    ← Subgroup.inf_relIndex_right, fixingSubgroup_sup_upper_inf_zero K E M hu]

/-- The abstract finite field has the same index, without choosing a normality instance. -/
theorem apfIndex_eq_subgroupRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K M u = ((H₀ ⊓ U₀ 0) ⊔ U₀ u).relIndex (U₀ 0) := by
  let i := E.toIntermediateField.val.comp M.val
  rw [apfIndex_eq_embedding K M i]
  have hr : i.fieldRange = M.map E.toIntermediateField.val := by
    simpa only [IntermediateField.fieldRange_val] using
      (AlgHom.map_fieldRange M.val E.toIntermediateField.val).symm
  rw [hr]
  exact apfInertiaIndex_map_eq_subgroupRelIndex K E M hu

/-- The non-Galois finite APF integral is the subgroup change of parameter. -/
theorem apfPsi_eq_subgroup_herbrand_comp_inverse {u : ℝ} (hu : -1 ≤ u) :
    apfPsi K M u = herbrandFunction (R := spectralIntegerRing K E) H₀
      (inverseHerbrandFunction (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u) := by
  by_cases hu' : u ≤ 0
  · rw [apfPsi_of_nonpos K M hu',
      subgroup_herbrandFunction_comp_inverse_of_nonpos _ _ hu hu']
  · rw [apfPsi_eq_integral_index K M (le_of_not_ge hu'),
      subgroup_herbrandFunction_comp_inverse_eq_integral _ _ (le_of_not_ge hu')]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (le_of_not_ge hu')]
    intro v hv
    dsimp only
    rw [apfIndex_eq_subgroupRelIndex K E M hv.1, upperRamificationGroup_zero,
      lowerRamificationGroup_zero]

/-- The inverse change of parameter uses the same finite overfield and subgroup. -/
theorem apfPhi_eq_herbrand_comp_subgroup_inverse {v : ℝ} (hv : -1 ≤ v) :
    apfPhi K M v =
      herbrandFunction (R := spectralIntegerRing K E) (E ≃ₐ[K] E)
        (inverseHerbrandFunction (R := spectralIntegerRing K E) H₀ v) := by
  apply (IsAPF.strictMono_apfPsi K M).injective
  rw [apfPsi_apfPhi,
    apfPsi_eq_subgroup_herbrand_comp_inverse K E M
      (herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ v)),
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ v),
    herbrandFunction_inverseHerbrandFunction _ hv]

end FontaineWintenberger

namespace FontaineWintenberger

section FixingSubgroup

variable {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N]

/-- Conjugation by a field isomorphism carries the fixing subgroup
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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

/-- The intrinsic index is computed in any finite Galois overfield,
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
finite Galois overfield on its spectral integer ring. -/
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

/-- The inverse change of parameter in any finite Galois overfield. -/
theorem apfPhi_eq_herbrand_comp_subgroup_inverse_of_finiteGalois
    {v : ℝ} (hv : -1 ≤ v) :
    apfPhi K M v =
      herbrandFunction (R := spectralIntegerRing K L) (L ≃ₐ[K] L)
        (inverseHerbrandFunction (R := spectralIntegerRing K L) M.fixingSubgroup v) := by
  apply (IsAPF.strictMono_apfPsi K M).injective
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

/-- The full-group condition in the first bound is detected by the
finite fixing subgroup and upper group. -/
theorem apfSubgroup_fieldRange_eq_top_iff_fixingSubgroup_sup_upper_eq_top
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K (j.comp M.val).fieldRange u = ⊤ ↔
      M.fixingSubgroup ⊔
        upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u = ⊤ := by
  rw [← Subgroup.index_eq_one, ← Subgroup.index_eq_one,
    apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index K L M j hu]

/-- The extended first bound is the supremum where the finite
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
