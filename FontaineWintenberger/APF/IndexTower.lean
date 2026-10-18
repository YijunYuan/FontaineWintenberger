/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.IndexTransport
public import FontaineWintenberger.GroupTheory.NormalIndex

/-!
# Actual relative index factors in nested APF extensions
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (M N : IntermediateField K (SeparableClosure K))

/-- The actual relative index between the two inertia-product subgroups. -/
noncomputable def apfTowerIndexFactor (u : ℝ) : ℕ :=
  (apfInertiaSubgroup K N u).relIndex (apfInertiaSubgroup K M u)

@[simp]
theorem apfTowerIndexFactor_zero : apfTowerIndexFactor K M N 0 = 1 := by
  simp [apfTowerIndexFactor, apfInertiaSubgroup]

/-- The larger extension has the smaller actual inertia-product subgroup. -/
theorem apfInertiaSubgroup_antitone_extension (hMN : M ≤ N) (u : ℝ) :
    apfInertiaSubgroup K N u ≤ apfInertiaSubgroup K M u :=
  sup_le_sup_right (inf_le_inf_right _ (IntermediateField.fixingSubgroup_le hMN)) _

/-- Multiplication of the actual relative indices gives the APF index factorization. -/
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

/-- APF gives genuine positive finite factors, including a nonnormal intermediate extension. -/
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

/-- The public intrinsic APF indices retain the actual tower factorization. -/
theorem apfIndex_eq_mul_towerIndexFactor (hMN : M ≤ N) {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K N u = apfIndex K M u * apfTowerIndexFactor K M N u := by
  rw [apfIndex_eq_embedding K N N.val, apfIndex_eq_embedding K M M.val]
  simpa only [IntermediateField.fieldRange_val] using
    apfInertiaIndex_eq_mul_towerIndexFactor K M N hMN hu

end FontaineWintenberger
