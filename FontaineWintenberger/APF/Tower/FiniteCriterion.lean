/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Criterion

/-!
# Ramification profiles of finite elementary towers

The elementary-step conditions determine the absolute upper products of the terminal
field. The resulting intervals include a final constant tail, so the statements also
cover a tower with no elementary steps.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Remark 1.4.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable {m : ℕ} (E : Fin (m + 1) → FiniteIntermediateField K (SeparableClosure K))
    (b : Fin m → ℝ)

omit [PerfectField 𝓀[K]] in
/-- A finite chain of adjacent profile equalities identifies every later product with
an earlier product, provided that the parameter is below all intervening cutoffs. -/
theorem apfSubgroup_eq_of_finite_step_profiles
    (hstep : ∀ n : Fin m, ∀ u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E n.succ).val u = apfSubgroup K (E n.castSucc).val u)
    {u : ℝ} (hu : -1 ≤ u) (n r : Fin (m + 1)) (hnr : n ≤ r)
    (hcut : ∀ k : Fin m, n.val ≤ k.val → u ≤ b k) :
    apfSubgroup K (E r).val u = apfSubgroup K (E n).val u := by
  induction r using Fin.induction with
  | zero => rw [show n = 0 from le_antisymm hnr (Fin.zero_le n)]
  | succ r ih =>
      rcases hnr.eq_or_lt with rfl | hnr
      · rfl
      · have hnr := Fin.le_castSucc_iff.mpr hnr
        exact (hstep r u hu (hcut r hnr)).trans (ih hnr)

variable (i : Fin m → ℝ) (hE : Monotone E) (hi : StrictMono i)
    (helem : ∀ n : Fin m, IsElementaryStep K (E n.castSucc) (E n.succ)
      (hE n.castSucc_le_succ) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup)

include hi helem in
/-- The transformed levels of a finite elementary tower are strictly increasing. -/
theorem strictMono_apfPhi_finite_elementary_tower :
    StrictMono (fun n : Fin m ↦ apfPhi K (E n.castSucc).val (i n)) := by
  cases m with
  | zero => exact fun n ↦ Fin.elim0 n
  | succ m =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro n
      exact (helem n.castSucc).apfPhi_lt (hi n.castSucc_lt_succ)

include hi helem htame in
/-- Above the transformed level of a finite step, the upper group fixes its upper field. -/
theorem apfSubgroup_eq_fixingSubgroup_of_finite_elementary_step
    (n : Fin m) {u : ℝ} (hnu : apfPhi K (E n.castSucc).val (i n) < u) :
    apfSubgroup K (E n.succ).val u = (E n.succ).val.fixingSubgroup := by
  have hb := strictMono_apfPhi_finite_elementary_tower K E i hE hi helem
  cases m with
  | zero => exact Fin.elim0 n
  | succ m =>
      induction n using Fin.induction with
      | zero =>
          exact (helem 0).apfSubgroup_eq_fixingSubgroup hnu
            (htame u ((helem 0).apfPhi_pos.trans hnu))
      | succ n ih =>
          apply (helem n.succ).apfSubgroup_eq_fixingSubgroup hnu
          rw [← Fin.succ_castSucc, ← ih ((hb n.castSucc_lt_succ).trans hnu)]
          exact le_sup_right

include hi helem htame in
/-- The terminal field of a finite elementary tower has the prescribed values at its
transformed jumps, between them, and on its initial and final intervals. -/
theorem finite_elementary_tower_profiles :
    let b := fun n : Fin m ↦ apfPhi K (E n.castSucc).val (i n)
    StrictMono b ∧
      (∀ n : Fin m, apfSubgroup K (E (Fin.last m)).val (b n) =
        (E n.castSucc).val.fixingSubgroup) ∧
      (∀ (n : Fin m) (u : ℝ), b n < u → (∀ k : Fin m, n < k → u ≤ b k) →
        apfSubgroup K (E (Fin.last m)).val u = (E n.succ).val.fixingSubgroup) ∧
      (∀ u : ℝ, 0 < u → (∀ k : Fin m, u ≤ b k) →
        apfSubgroup K (E (Fin.last m)).val u = (E 0).val.fixingSubgroup) := by
  let b := fun n : Fin m ↦ apfPhi K (E n.castSucc).val (i n)
  have hb := strictMono_apfPhi_finite_elementary_tower K E i hE hi helem
  have hstep (n : Fin m) (u : ℝ) (hu : -1 ≤ u) (hun : u ≤ b n) :
      apfSubgroup K (E n.succ).val u = apfSubgroup K (E n.castSucc).val u :=
    (helem n).apfSubgroup_eq hu hun
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro n
    have hpos := (helem n).apfPhi_pos
    rw [apfSubgroup_eq_of_finite_step_profiles K E b hstep (by linarith : -1 ≤ b n)
      n.castSucc (Fin.last m) (Fin.le_last _) (fun k hnk ↦ hb.monotone hnk)]
    cases m with
    | zero => exact Fin.elim0 n
    | succ m =>
        cases n using Fin.cases with
        | zero => exact sup_eq_left.mpr (htame _ hpos)
        | succ n =>
            rw [← Fin.succ_castSucc]
            exact apfSubgroup_eq_fixingSubgroup_of_finite_elementary_step
              K E i hE hi helem htame n.castSucc (hb n.castSucc_lt_succ)
  · intro n u hnu hun
    have hpos := (helem n).apfPhi_pos.trans hnu
    rw [apfSubgroup_eq_of_finite_step_profiles K E b hstep (by linarith : -1 ≤ u)
      n.succ (Fin.last m) (Fin.le_last _) (fun k hnk ↦ hun k hnk)]
    exact apfSubgroup_eq_fixingSubgroup_of_finite_elementary_step K E i hE hi helem htame n hnu
  · intro u hu hun
    rw [apfSubgroup_eq_of_finite_step_profiles K E b hstep (by linarith : -1 ≤ u)
      0 (Fin.last m) (Fin.zero_le _) (fun k _ ↦ hun k), apfSubgroup,
      sup_eq_left.mpr (htame u hu)]

end FontaineWintenberger
