/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Defs
public import FontaineWintenberger.Mathlib.GroupTheory.Index

/-!
# The APF index

## The finite positive indices in the APF Herbrand integrand

The denominator subgroup is the product inside absolute inertia.
Arithmetic profiniteness proves that its relative index is finite and
positive; the resulting natural-number function is nondecreasing.

## The intrinsic inertia index of a separable extension

Conjugation preserves both the inertia subgroup and the APF subgroup, hence
their relative index. An embedding into the separable closure therefore
defines an index for an abstract extension, independent of that embedding.

## Relative index factors in nested APF extensions
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- The subgroup in the APF inertia-relative index. -/
noncomputable def apfInertiaSubgroup (L : IntermediateField K (SeparableClosure K)) (u : ℝ) :
    Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  (L.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔ absoluteUpperRamificationGroup K u

/-- The inertia-relative index; positivity for APF extensions is proved below. -/
noncomputable def apfInertiaIndex (L : IntermediateField K (SeparableClosure K)) (u : ℝ) : ℕ :=
  (apfInertiaSubgroup K L u).relIndex (absoluteUpperRamificationGroup K 0)

theorem apfInertiaSubgroup_eq_inf (L : IntermediateField K (SeparableClosure K))
    (u : ℝ) (hu : 0 ≤ u) :
    apfInertiaSubgroup K L u = apfSubgroup K L u ⊓ absoluteUpperRamificationGroup K 0 := by
  have hU : absoluteUpperRamificationGroup K u ≤ absoluteUpperRamificationGroup K 0 :=
    upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K) (by norm_num)
      (by change -1 ≤ u; linarith) hu
  change (L.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
      absoluteUpperRamificationGroup K u =
    (L.fixingSubgroup ⊔ absoluteUpperRamificationGroup K u) ⊓ absoluteUpperRamificationGroup K 0
  apply le_antisymm
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hU)
  · rintro g ⟨hg, hg₀⟩
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hh₀ : h ∈ absoluteUpperRamificationGroup K 0 := by
      have := (absoluteUpperRamificationGroup K 0).mul_mem hg₀
        ((absoluteUpperRamificationGroup K 0).inv_mem (hU hn))
      simpa only [mul_inv_cancel_right] using this
    exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hh₀⟩, n, hn, rfl⟩

theorem apfInertiaSubgroup_le_zero (L : IntermediateField K (SeparableClosure K))
    (u : ℝ) (hu : 0 ≤ u) :
    apfInertiaSubgroup K L u ≤ absoluteUpperRamificationGroup K 0 := by
  rw [apfInertiaSubgroup_eq_inf K L u hu]
  exact inf_le_right

theorem apfInertiaSubgroup_antitoneOn (L : IntermediateField K (SeparableClosure K)) :
    AntitoneOn (apfInertiaSubgroup K L) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  exact sup_le_sup_left
    (upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K)
      (by change -1 ≤ u; change 0 ≤ u at hu; linarith)
      (by change -1 ≤ v; change 0 ≤ v at hv; linarith) huv) _

@[simp]
theorem apfInertiaIndex_zero (L : IntermediateField K (SeparableClosure K)) :
    apfInertiaIndex K L 0 = 1 := by
  unfold apfInertiaIndex apfInertiaSubgroup
  rw [sup_eq_right.mpr (show L.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0 ≤
    absoluteUpperRamificationGroup K 0 from inf_le_right)]
  simp

theorem IsAPFSubextension.inertiaIndex_pos {L : IntermediateField K (SeparableClosure K)}
    [IsAPFSubextension K L] (u : ℝ) (hu : 0 ≤ u) : 0 < apfInertiaIndex K L u := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_eq_inf K L u hu, Subgroup.inf_relIndex_right]
  let : (apfSubgroup K L u).FiniteIndex :=
    (isAPFSubextension_iff_finiteIndex K L).mp ‹_› u (by linarith)
  exact Nat.pos_of_ne_zero (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp
    (Subgroup.isFiniteRelIndex_of_finiteIndex))

theorem IsAPFSubextension.inertia_isFiniteRelIndex {L : IntermediateField K (SeparableClosure K)}
    [IsAPFSubextension K L] (u : ℝ) (hu : 0 ≤ u) :
    (apfInertiaSubgroup K L u).IsFiniteRelIndex (absoluteUpperRamificationGroup K 0) :=
  Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
    (Nat.ne_of_gt (IsAPFSubextension.inertiaIndex_pos K u hu))

theorem IsAPFSubextension.inertiaIndex_monotoneOn {L : IntermediateField K (SeparableClosure K)}
    [IsAPFSubextension K L] : MonotoneOn (apfInertiaIndex K L) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  have hvu := apfInertiaSubgroup_antitoneOn K L hu hv huv
  have hmul := Subgroup.relIndex_mul_relIndex (apfInertiaSubgroup K L v)
    (apfInertiaSubgroup K L u) (absoluteUpperRamificationGroup K 0) hvu
    (apfInertiaSubgroup_le_zero K L u hu)
  exact Nat.le_of_dvd (IsAPFSubextension.inertiaIndex_pos K v hv) (dvd_of_mul_left_eq _ hmul)

end FontaineWintenberger

namespace FontaineWintenberger

open scoped Pointwise

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

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

/-- The inertia-relative index, independent of the separable embedding. -/
noncomputable def apfIndex (u : ℝ) : ℕ :=
  apfInertiaIndex K (IsSepClosed.lift : L →ₐ[K] SeparableClosure K).fieldRange u

theorem apfIndex_eq_embedding (i : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    apfIndex K L u = apfInertiaIndex K i.fieldRange u :=
  apfInertiaIndex_fieldRange_eq K L _ i u

@[simp]
theorem apfIndex_zero : apfIndex K L 0 = 1 :=
  apfInertiaIndex_zero K _

theorem IsAPF.apfIndex_pos [IsAPF K L] {u : ℝ} (hu : 0 ≤ u) :
    0 < apfIndex K L u :=
  IsAPFSubextension.inertiaIndex_pos K u hu

theorem IsAPF.apfIndex_monotoneOn [IsAPF K L] :
    MonotoneOn (apfIndex K L) (Set.Ici (0 : ℝ)) :=
  IsAPFSubextension.inertiaIndex_monotoneOn K

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

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M N : IntermediateField K (SeparableClosure K))

/-- The relative index between the two inertia-product subgroups. -/
noncomputable def apfTowerIndexFactor (u : ℝ) : ℕ :=
  (apfInertiaSubgroup K N u).relIndex (apfInertiaSubgroup K M u)

@[simp]
theorem apfTowerIndexFactor_zero : apfTowerIndexFactor K M N 0 = 1 := by
  simp [apfTowerIndexFactor, apfInertiaSubgroup]

/-- The larger extension has the smaller inertia-product subgroup. -/
theorem apfInertiaSubgroup_antitone_extension (hMN : M ≤ N) (u : ℝ) :
    apfInertiaSubgroup K N u ≤ apfInertiaSubgroup K M u :=
  sup_le_sup_right (inf_le_inf_right _ (IntermediateField.fixingSubgroup_le hMN)) _

/-- Multiplication of the relative indices gives the APF index factorization. -/
theorem apfInertiaIndex_eq_mul_towerIndexFactor (hMN : M ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    apfInertiaIndex K N u = apfInertiaIndex K M u * apfTowerIndexFactor K M N u := by
  have h := Subgroup.relIndex_mul_relIndex (apfInertiaSubgroup K N u)
    (apfInertiaSubgroup K M u) (absoluteUpperRamificationGroup K 0)
    (apfInertiaSubgroup_antitone_extension K M N hMN u)
    (apfInertiaSubgroup_le_zero K M u hu)
  exact h.symm.trans (Nat.mul_comm _ _)

/-- The relative factor is intrinsically computed inside the intermediate inertia subgroup. -/
theorem apfTowerIndexFactor_eq_inertiaRelIndex (hMN : M ≤ N) (u : ℝ) :
    apfTowerIndexFactor K M N u =
      ((N.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔
        (absoluteUpperRamificationGroup K u ⊓
          (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0))).relIndex
        (M.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) :=
  Subgroup.relIndex_sup_sup_eq_inf _ _ _
    (inf_le_inf_right _ (IntermediateField.fixingSubgroup_le hMN))

/-- APF gives positive finite factors, including a nonnormal intermediate extension. -/
theorem IsAPFSubextension.towerIndexFactor_pos [IsAPFSubextension K N]
    {u : ℝ} (hu : 0 ≤ u) : 0 < apfTowerIndexFactor K M N u := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := Subgroup.relIndex_eq_zero_of_le_right
    (apfInertiaSubgroup_le_zero K M u hu) hzero
  exact (Nat.ne_of_gt (IsAPFSubextension.inertiaIndex_pos K u hu)) h

/-- The intrinsic finite relative factor is nondecreasing with the upper parameter. -/
theorem IsAPFSubextension.towerIndexFactor_monotoneOn [IsAPFSubextension K N]
    (hMN : M ≤ N) : MonotoneOn (apfTowerIndexFactor K M N) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hdv := Nat.ne_of_gt (IsAPFSubextension.towerIndexFactor_pos K M N hv)
  rw [apfTowerIndexFactor_eq_inertiaRelIndex K M N hMN v] at hdv
  rw [apfTowerIndexFactor_eq_inertiaRelIndex K M N hMN u,
    apfTowerIndexFactor_eq_inertiaRelIndex K M N hMN v]
  exact Subgroup.relIndex_le_of_le_left
    (sup_le_sup_left (inf_le_inf_right _
      (upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K)
        (by linarith : -1 ≤ u) (by linarith : -1 ≤ v) huv)) _) hdv

/-- The public intrinsic APF indices retain the tower factorization. -/
theorem apfIndex_eq_mul_towerIndexFactor (hMN : M ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K N u = apfIndex K M u * apfTowerIndexFactor K M N u := by
  rw [apfIndex_eq_embedding K N N.val, apfIndex_eq_embedding K M M.val]
  simpa only [IntermediateField.fieldRange_val] using
    apfInertiaIndex_eq_mul_towerIndexFactor K M N hMN hu

end FontaineWintenberger
