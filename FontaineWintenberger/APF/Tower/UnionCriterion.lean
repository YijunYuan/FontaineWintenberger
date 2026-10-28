/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Tower.Stages

/-!
# An APF criterion for towers with prescribed finite ramification profiles

Suppose adjoining the next field changes no APF product up to `b n`, and all upper
groups above `b n` fix that next field. For a strictly increasing tower, its union is APF
if and only if the increasing sequence `b` tends to infinity. When it does, the APF
products of the union are exactly the fixing subgroups of the fields of the tower.

These lemmas isolate the passage from finite ramification profiles to the infinite union
in Wintenberger's Remark 1.4.2.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.2.
-/

@[expose] public section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : ℕ → FiniteIntermediateField K (SeparableClosure K)) (b : ℕ → ℝ)

/-- Agreement between successive finite profiles below increasing cutoffs implies agreement
between all later profiles below any one cutoff. -/
theorem apfSubgroup_eq_of_step_profiles (hb : Monotone b)
    (hstep : ∀ n u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u)
    {n m : ℕ} (hnm : n ≤ m) {u : ℝ} (hu : -1 ≤ u) (hun : u ≤ b n) :
    apfSubgroup K (E m).val u = apfSubgroup K (E n).val u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [hstep m u hu (hun.trans (hb hnm)), ih]

/-- The product for the union stabilizes as soon as the parameter is below a finite cutoff. -/
theorem apfSubgroup_iSup_eq_of_step_profiles (hE : Monotone E) (hb : Monotone b)
    (hstep : ∀ n u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u)
    {n : ℕ} {u : ℝ} (hu : -1 ≤ u) (hun : u ≤ b n) :
    apfSubgroup K (⨆ m, (E m).val) u = apfSubgroup K (E n).val u := by
  rw [apfSubgroup_iSup_eq_iInf K _ (fun _ _ h ↦ hE h)]
  apply le_antisymm (iInf_le _ n)
  apply le_iInf
  intro m
  rcases le_total m n with hmn | hnm
  · exact sup_le_sup_right (IntermediateField.fixingSubgroup_le (hE hmn)) _
  · exact (apfSubgroup_eq_of_step_profiles K E b hb hstep hnm hu hun).ge

/-- Divergence of the finite ramification cutoffs makes the union APF. -/
theorem isAPF_iSup_of_step_profiles (hE : Monotone E) (hb : Monotone b)
    (hstep : ∀ n u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u)
    (htop : Tendsto b atTop atTop) : IsAPF K ↥(⨆ n, (E n).val) := by
  apply (isAPF_iff_subextension K _).mpr
  refine ⟨fun u hu ↦ ?_⟩
  obtain ⟨n, hn⟩ := hb.tendsto_atTop_atTop_iff.mp htop u
  rw [apfSubgroup_iSup_eq_of_step_profiles K E b hE hb hstep hu hn]
  exact IsAPFSubextension.isOpen_apfSubgroup u hu

omit [IsCompleteDiscreteValuedField K] in
/-- A strictly increasing sequence of finite intermediate fields has infinite-dimensional
union. -/
theorem not_finiteDimensional_iSup_of_strictMono (hE : StrictMono E) :
    ¬FiniteDimensional K ↥(⨆ n, (E n).val) := by
  intro hfin
  let := hfin
  have hdegree : StrictMono (fun n ↦ Module.finrank K (E n).val) := by
    intro m n hmn
    have hle := (hE hmn).le
    refine lt_of_le_of_ne (IntermediateField.finrank_le_of_le_right hle) ?_
    intro heq
    exact (hE hmn).ne (Subtype.ext
      (IntermediateField.eq_of_le_of_finrank_le hle heq.ge))
  let d := Module.finrank K ↥(⨆ n, (E n).val)
  have hbound : Module.finrank K (E (d + 1)).val ≤ d :=
    IntermediateField.finrank_le_of_le_right (le_iSup (fun n ↦ (E n).val) (d + 1))
  have hlower : d + 1 ≤ Module.finrank K (E (d + 1)).val := hdegree.id_le (d + 1)
  omega

/-- If all cutoffs are bounded, the union's product above them is its fixing subgroup. -/
theorem apfSubgroup_iSup_eq_fixingSubgroup_of_bounded
    (hE : Monotone E)
    (htail : ∀ n u, b n < u →
      apfSubgroup K (E (n + 1)).val u = (E (n + 1)).val.fixingSubgroup)
    {u : ℝ} (hu : ∀ n, b n < u) :
    apfSubgroup K (⨆ n, (E n).val) u = (⨆ n, (E n).val).fixingSubgroup := by
  apply le_antisymm
  · intro g hg
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    change x ∈ ((⨆ n, (E n).val : IntermediateField K (SeparableClosure K)) :
      Set (SeparableClosure K)) at hx
    rw [IntermediateField.coe_iSup_of_directed
      (show Monotone (fun n ↦ (E n).val) from fun _ _ h ↦ hE h).directed_le] at hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    have hg' : g ∈ apfSubgroup K (E (n + 1)).val u :=
      (sup_le_sup_right (IntermediateField.fixingSubgroup_le
        (le_iSup (fun n ↦ (E n).val) (n + 1))) _) hg
    rw [htail n u (hu n)] at hg'
    exact hg' ⟨x, hE (Nat.le_succ n) hn⟩
  · exact le_sup_left

/-- An APF union of a strictly increasing tower forces its finite cutoffs to diverge. -/
theorem tendsto_of_isAPF_iSup_of_step_profiles (hE : StrictMono E) (hb : Monotone b)
    (htail : ∀ n u, b n < u →
      apfSubgroup K (E (n + 1)).val u = (E (n + 1)).val.fixingSubgroup)
    [IsAPF K ↥(⨆ n, (E n).val)] : Tendsto b atTop atTop := by
  apply hb.tendsto_atTop_atTop
  intro u
  by_contra! h
  let v := max u 0
  have hv : ∀ n, b n < v := fun n ↦ (h n).trans_le (le_max_left u 0)
  have hopen := IsAPFSubextension.isOpen_apfSubgroup
    (K := K) (L := ⨆ n, (E n).val) v
    (show -1 ≤ v by dsimp [v]; linarith [le_max_right u 0])
  rw [apfSubgroup_iSup_eq_fixingSubgroup_of_bounded K E b hE.monotone htail hv] at hopen
  exact not_finiteDimensional_iSup_of_strictMono K E hE
    ((InfiniteGalois.isOpen_iff_finite _).mp hopen)

/-- The infinite-union step in the elementary-tower criterion: the APF condition is equivalent
to divergence of the transformed cutoffs in the finite ramification profiles. -/
theorem isAPF_iSup_iff_tendsto_of_step_profiles (hE : StrictMono E) (hb : Monotone b)
    (hstep : ∀ n u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u)
    (htail : ∀ n u, b n < u →
      apfSubgroup K (E (n + 1)).val u = (E (n + 1)).val.fixingSubgroup) :
    IsAPF K ↥(⨆ n, (E n).val) ↔ Tendsto b atTop atTop := by
  constructor
  · intro h
    let := h
    exact tendsto_of_isAPF_iSup_of_step_profiles K E b hE hb htail
  · exact isAPF_iSup_of_step_profiles K E b hE.monotone hb hstep

/-- Between two consecutive cutoffs, the union has exactly the fixing subgroup of the
intervening field. -/
theorem apfSubgroup_iSup_eq_fixingSubgroup_of_step_profiles
    (hE : Monotone E) (hb : Monotone b)
    (hstep : ∀ n u, -1 ≤ u → u ≤ b n →
      apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u)
    (htail : ∀ n u, b n < u →
      apfSubgroup K (E (n + 1)).val u = (E (n + 1)).val.fixingSubgroup)
    {n : ℕ} {u : ℝ} (hu : -1 ≤ u) (hnu : b n < u) (hun : u ≤ b (n + 1)) :
    apfSubgroup K (⨆ n, (E n).val) u = (E (n + 1)).val.fixingSubgroup := by
  rw [apfSubgroup_iSup_eq_of_step_profiles K E b hE hb hstep hu hun, htail n u hnu]

end FontaineWintenberger
