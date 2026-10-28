/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Canonical

/-!
# Uniqueness of the elementary tower

The elementary-step conditions characterize the canonical tower. For a strictly increasing
elementary tower with tame first field and APF union, its transformed levels enumerate all
positive upper breaks. Thus both its levels and its fields agree with the canonical tower
constructed from the upper ramification filtration.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §§1.4.1–1.4.2.
-/

@[expose] public section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (E : ℕ → FiniteIntermediateField K (SeparableClosure K)) (i : ℕ → ℝ)
variable (hE : StrictMono E) (hi : StrictMono i)
variable (helem : ∀ n,
    IsElementaryStep K (E n) (E (n + 1)) (hE.monotone (Nat.le_succ n)) (i n))
variable (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup)

include hE hi helem htame

/-- At a transformed level the product of the union is exactly the fixing subgroup of
the corresponding field of an elementary tower. -/
theorem apfSubgroup_iSup_apfPhi_eq_fixingSubgroup (n : ℕ) :
    apfSubgroup K (⨆ n, (E n).val) (apfPhi K (E n).val (i n)) = (E n).val.fixingSubgroup := by
  obtain ⟨hb, hstep, htail⟩ := elementary_tower_profiles K E i hE.monotone hi helem htame
  rw [apfSubgroup_iSup_eq_of_step_profiles K E _ hE.monotone hb.monotone hstep
    (show -1 ≤ apfPhi K (E n).val (i n) by linarith [(helem n).apfPhi_pos]) le_rfl]
  cases n with
  | zero => exact sup_eq_left.mpr (htame _ (helem 0).apfPhi_pos)
  | succ n => exact htail n _ (hb (Nat.lt_succ_self n))

/-- Each transformed level of a strictly increasing elementary tower is an upper break
of its union. -/
theorem isAPFUpperBreak_apfPhi_of_isElementaryStep (n : ℕ) :
    IsAPFUpperBreak K (⨆ n, (E n).val) (apfPhi K (E n).val (i n)) := by
  obtain ⟨_hb, _hstep, htail⟩ := elementary_tower_profiles K E i hE.monotone hi helem htame
  refine ⟨(helem n).apfPhi_pos, fun u hu heq ↦ ?_⟩
  have hle : apfSubgroup K (⨆ n, (E n).val) u ≤
      apfSubgroup K (E (n + 1)).val u :=
    sup_le_sup_right (IntermediateField.fixingSubgroup_le
      (le_iSup (fun m ↦ (E m).val) (n + 1))) _
  rw [heq, apfSubgroup_iSup_apfPhi_eq_fixingSubgroup K E i hE hi helem htame,
    htail n u hu] at hle
  have hfields := IntermediateField.fixedField_le hle
  rw [InfiniteGalois.fixedField_fixingSubgroup,
    InfiniteGalois.fixedField_fixingSubgroup] at hfields
  exact (hE (Nat.lt_succ_self n)).not_ge hfields

variable [IsAPF K ↥(⨆ n, (E n).val)]

/-- The transformed levels of an elementary tower with APF union enumerate every
positive upper break. -/
theorem isAPFUpperBreak_iSup_iff_mem_range_apfPhi (u : ℝ) :
    IsAPFUpperBreak K (⨆ n, (E n).val) u ↔
      u ∈ Set.range (fun n ↦ apfPhi K (E n).val (i n)) := by
  constructor
  · intro hu
    obtain ⟨hb, hstep, htail⟩ := elementary_tower_profiles K E i hE.monotone hi helem htame
    have htop := (isAPF_iSup_iff_tendsto_of_isElementaryStep K E i hE hi helem htame).mp
      inferInstance
    obtain ⟨m, hm⟩ := (htop.eventually (eventually_ge_atTop u)).exists
    have hex : ∃ n, u ≤ apfPhi K (E n).val (i n) := ⟨m, hm⟩
    let n := Nat.find hex
    have hn : u ≤ apfPhi K (E n).val (i n) := Nat.find_spec hex
    have hprod : apfSubgroup K (⨆ n, (E n).val) u = (E n).val.fixingSubgroup := by
      cases hnzero : n with
      | zero =>
          rw [apfSubgroup_iSup_eq_of_step_profiles K E _ hE.monotone hb.monotone hstep
            (show -1 ≤ u by linarith [hu.1]) (hnzero ▸ hn)]
          exact sup_eq_left.mpr (htame u hu.1)
      | succ k =>
          have hku : apfPhi K (E k).val (i k) < u :=
            lt_of_not_ge (Nat.find_min hex (show k < Nat.find hex by change k < n; omega))
          exact apfSubgroup_iSup_eq_fixingSubgroup_of_step_profiles K E _ hE.monotone
            hb.monotone hstep htail (by linarith [hu.1]) hku (hnzero ▸ hn)
    refine ⟨n, ?_⟩
    apply le_antisymm _ hn
    by_contra! hun
    apply hu.2 _ hun
    rw [apfSubgroup_iSup_apfPhi_eq_fixingSubgroup K E i hE hi helem htame, hprod]
  · rintro ⟨n, rfl⟩
    exact isAPFUpperBreak_apfPhi_of_isElementaryStep K E i hE hi helem htame n

variable [Fact (¬ Module.Finite K ↥(⨆ n, (E n).val))]

/-- The transformed levels of an elementary tower with APF union are the canonical
upper breaks, in the same order. -/
theorem apfUpperBreak_iSup_eq_of_isElementaryStep :
    apfUpperBreak K (⨆ n, (E n).val) = fun n ↦ apfPhi K (E n).val (i n) := by
  apply (strictMono_apfUpperBreak K (⨆ n, (E n).val)).eq_of_range_eq
    (elementary_tower_profiles K E i hE.monotone hi helem htame).1
  ext u
  rw [← isAPFUpperBreak_iff_mem_range,
    isAPFUpperBreak_iSup_iff_mem_range_apfPhi K E i hE hi helem htame]

/-- **Wintenberger 1.4.2:** an elementary tower with APF union is the canonical
elementary tower of that union. -/
theorem apfElementaryStage_iSup_eq_of_isElementaryStep (n : ℕ) :
    apfElementaryStage K (⨆ n, (E n).val) n = E n := by
  apply Subtype.ext
  change apfFiniteStage K (⨆ n, (E n).val)
    (apfUpperBreak K (⨆ n, (E n).val) n) = (E n).val
  rw [apfUpperBreak_iSup_eq_of_isElementaryStep K E i hE hi helem htame,
    apfFiniteStage, apfSubgroup_iSup_apfPhi_eq_fixingSubgroup K E i hE hi helem htame,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- The prescribed elementary levels are also the canonical lower-numbered levels. -/
theorem apfElementaryLevel_iSup_eq_of_isElementaryStep (n : ℕ) :
    apfElementaryLevel K (⨆ n, (E n).val) n = i n := by
  rw [apfElementaryLevel_eq,
    apfElementaryStage_iSup_eq_of_isElementaryStep K E i hE hi helem htame,
    apfUpperBreak_iSup_eq_of_isElementaryStep K E i hE hi helem htame, apfPsi_apfPhi]

end FontaineWintenberger
