/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Basic

/-!
# The finite positive indices in the APF Herbrand integrand

The denominator subgroup is the actual product inside absolute inertia.
Arithmetic profiniteness proves that its relative index is finite and
positive; the resulting natural-number function is nondecreasing.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- The actual subgroup in the APF inertia-relative index. -/
noncomputable def apfInertiaSubgroup (L : IntermediateField K (SeparableClosure K)) (u : ℝ) :
    Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  (L.fixingSubgroup ⊓ absoluteUpperRamificationGroup K 0) ⊔ absoluteUpperRamificationGroup K u

/-- The actual inertia-relative index; positivity for APF extensions is proved below. -/
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
