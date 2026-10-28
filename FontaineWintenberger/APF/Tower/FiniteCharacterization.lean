/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.FiniteElementary
public import FontaineWintenberger.APF.Tower.FiniteCriterion

/-!
# Characterization of finite elementary towers

A strictly increasing finite tower with elementary successive extensions has precisely its
transformed levels as positive upper breaks. Sorting these levels identifies the tower with
the canonical finite elementary tower, including its terminal field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §§1.4.1–1.4.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {m : ℕ} (E : Fin (m + 1) → FiniteIntermediateField K (SeparableClosure K))
    (b : Fin m → ℝ) (hE : StrictMono E) (hb : StrictMono b) (hbpos : ∀ n, 0 < b n)
variable (hlevel : ∀ n,
    apfSubgroup K (E (Fin.last m)).val (b n) = (E n.castSucc).val.fixingSubgroup)
variable (hplateau : ∀ n u, b n < u → (∀ k, n < k → u ≤ b k) →
    apfSubgroup K (E (Fin.last m)).val u = (E n.succ).val.fixingSubgroup)
variable (hinitial : ∀ u, 0 < u → (∀ n, u ≤ b n) →
    apfSubgroup K (E (Fin.last m)).val u = (E 0).val.fixingSubgroup)

include hE hb hbpos hlevel hplateau hinitial

/-- Exact finite plateaux enumerate all the positive upper breaks of the terminal field. -/
theorem isAPFUpperBreak_iff_mem_range_of_finite_profiles (u : ℝ) :
    IsAPFUpperBreak K (E (Fin.last m)).val u ↔ u ∈ Set.range b := by
  constructor
  · intro hu
    by_cases hex : ∃ n, u ≤ b n
    · obtain ⟨n, hn, hmin⟩ := wellFounded_lt.has_min {n : Fin m | u ≤ b n} hex
      have hprev : ∀ k : Fin m, k < n → b k < u :=
        fun k hk ↦ lt_of_not_ge fun hku ↦ hmin k hku hk
      have hprod : apfSubgroup K (E (Fin.last m)).val u = (E n.castSucc).val.fixingSubgroup := by
        cases m with
        | zero => exact Fin.elim0 n
        | succ m =>
            cases n using Fin.cases with
            | zero => exact hinitial u hu.1 fun k ↦ hn.trans (hb.monotone (Fin.zero_le k))
            | succ n =>
                rw [← Fin.succ_castSucc]
                exact hplateau n.castSucc u (hprev _ n.castSucc_lt_succ) fun k hk ↦
                  hn.trans (hb.monotone (Fin.castSucc_lt_iff_succ_le.mp hk))
      refine ⟨n, ?_⟩
      apply le_antisymm _ hn
      by_contra! hun
      exact hu.2 (b n) hun ((hlevel n).trans hprod.symm)
    · have hall : ∀ n, b n < u := by simpa only [not_exists, not_le] using hex
      have hfix : apfSubgroup K (E (Fin.last m)).val u = (E (Fin.last m)).val.fixingSubgroup := by
        cases m with
        | zero => exact hinitial u hu.1 (fun n ↦ Fin.elim0 n)
        | succ r =>
            exact hplateau (Fin.last r) u (hall _) (fun k hk ↦
              (not_lt_of_ge (Fin.le_last k) hk).elim)
      apply False.elim
      apply hu.2 (u + 1) (by linarith)
      apply le_antisymm
      · exact apfSubgroup_antitoneOn K (E (Fin.last m)).val
          (by change -1 ≤ u; linarith [hu.1])
          (by change -1 ≤ u + 1; linarith [hu.1]) (by linarith)
      · rw [hfix]
        exact le_sup_left
  · rintro ⟨n, rfl⟩
    refine ⟨hbpos n, fun u hnu heq ↦ ?_⟩
    have hle : apfSubgroup K (E (Fin.last m)).val u ≤ (E n.succ).val.fixingSubgroup := by
      cases m with
      | zero => exact Fin.elim0 n
      | succ m =>
          cases n using Fin.lastCases with
          | last =>
              exact (hplateau _ u hnu (fun k hk ↦ (not_lt_of_ge (Fin.le_last k) hk).elim)).le
          | cast n =>
              let v := min u (b n.succ)
              have hnv : b n.castSucc < v := lt_min hnu (hb n.castSucc_lt_succ)
              have hnext : ∀ j, n.castSucc < j → v ≤ b j := fun j hj ↦
                (min_le_right _ _).trans (hb.monotone (Fin.castSucc_lt_iff_succ_le.mp hj))
              rw [← hplateau n.castSucc v hnv hnext]
              exact apfSubgroup_antitoneOn K (E (Fin.last (m + 1))).val
                (show -1 ≤ v by linarith [hbpos n.castSucc])
                (show -1 ≤ u by linarith [hbpos n.castSucc]) (min_le_left _ _)
    rw [heq, hlevel n] at hle
    have hfields := IntermediateField.fixedField_le hle
    rw [InfiniteGalois.fixedField_fixingSubgroup,
      InfiniteGalois.fixedField_fixingSubgroup] at hfields
    exact (hE n.castSucc_lt_succ).not_ge hfields

/-- A finite profile has as many elementary steps as its terminal field has positive breaks. -/
theorem card_apfFiniteUpperBreaks_eq_of_finite_profiles :
    (apfFiniteUpperBreaks K (E (Fin.last m)).val).card = m := by
  classical
  have hset : Finset.univ.image b = apfFiniteUpperBreaks K (E (Fin.last m)).val := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_apfFiniteUpperBreaks,
      isAPFUpperBreak_iff_mem_range_of_finite_profiles K E b hE hb hbpos hlevel hplateau hinitial,
      Set.mem_range]
  rw [← hset, Finset.card_image_of_injective _ hb.injective, Finset.card_univ, Fintype.card_fin]

/-- Sorting the break set recovers the prescribed increasing finite list of breaks. -/
theorem apfFiniteUpperBreak_eq_of_finite_profiles
    (hc : (apfFiniteUpperBreaks K (E (Fin.last m)).val).card = m) (n : Fin m) :
    apfFiniteUpperBreak K (E (Fin.last m)).val (Fin.cast hc.symm n) = b n := by
  have hbmem : ∀ n, b n ∈ apfFiniteUpperBreaks K (E (Fin.last m)).val := by
    intro n
    rw [mem_apfFiniteUpperBreaks,
      isAPFUpperBreak_iff_mem_range_of_finite_profiles K E b hE hb hbpos hlevel hplateau hinitial]
    exact ⟨n, rfl⟩
  have hsort := Finset.orderEmbOfFin_unique hc hbmem hb
  have hcast : apfFiniteUpperBreak K (E (Fin.last m)).val (Fin.cast hc.symm n) =
      (apfFiniteUpperBreaks K (E (Fin.last m)).val).orderEmbOfFin hc n := by
    apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
    rfl
  exact hcast.trans (congrFun hsort n).symm

/-- Finite ramification profiles identify all stages, including the terminal stage, with
the canonical finite elementary tower. -/
theorem apfFiniteElementaryStage_eq_of_finite_profiles
    (hc : (apfFiniteUpperBreaks K (E (Fin.last m)).val).card = m) (n : Fin (m + 1)) :
    apfFiniteElementaryStage K (E (Fin.last m)).val
      (Fin.cast (congrArg (fun r ↦ r + 1) hc.symm) n) = E n := by
  apply Subtype.ext
  cases n using Fin.lastCases with
  | last => rw [Fin.cast_last, apfFiniteElementaryStage_last]
  | cast n =>
    rw [Fin.cast_castSucc, apfFiniteElementaryStage_castSucc,
      apfFiniteUpperBreak_eq_of_finite_profiles K E b hE hb hbpos hlevel hplateau hinitial hc,
      apfFiniteStage, hlevel, InfiniteGalois.fixedField_fixingSubgroup]

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable {m : ℕ} (E : Fin (m + 1) → FiniteIntermediateField K (SeparableClosure K))
    (i : Fin m → ℝ)

/-- **Wintenberger 1.4.2**, finite case: the elementary-step conditions identify the given
tower and its levels with the canonical finite elementary tower of its terminal field.
The equality of the numbers of steps supplies the casts between their finite index types. -/
theorem exists_apfFiniteElementaryStage_eq_of_isElementaryStep
    (hE : StrictMono E) (hi : StrictMono i)
    (helem : ∀ n : Fin m, IsElementaryStep K (E n.castSucc) (E n.succ)
      (hE.monotone n.castSucc_le_succ) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup) :
    ∃ hc : (apfFiniteUpperBreaks K (E (Fin.last m)).val).card = m,
      (∀ n : Fin (m + 1), apfFiniteElementaryStage K (E (Fin.last m)).val
        (Fin.cast (congrArg (fun r ↦ r + 1) hc.symm) n) = E n) ∧
      ∀ n : Fin m, apfFiniteElementaryLevel K (E (Fin.last m)).val (Fin.cast hc.symm n) = i n := by
  let b := fun n : Fin m ↦ apfPhi K (E n.castSucc).val (i n)
  obtain ⟨hb, hlevel, hplateau, hinitial⟩ :=
    finite_elementary_tower_profiles K E i hE.monotone hi helem htame
  have hbpos : ∀ n, 0 < b n := fun n ↦ (helem n).apfPhi_pos
  let hc := card_apfFiniteUpperBreaks_eq_of_finite_profiles
    K E b hE hb hbpos hlevel hplateau hinitial
  refine ⟨hc, apfFiniteElementaryStage_eq_of_finite_profiles
    K E b hE hb hbpos hlevel hplateau hinitial hc, fun n ↦ ?_⟩
  rw [apfFiniteElementaryLevel,
    apfFiniteUpperBreak_eq_of_finite_profiles K E b hE hb hbpos hlevel hplateau hinitial hc]
  have hs : apfFiniteStage K (E (Fin.last m)).val (b n) = (E n.castSucc).val := by
    rw [apfFiniteStage, hlevel n, InfiniteGalois.fixedField_fixingSubgroup]
  rw [← apfPsi_eq_of_apfFiniteStage_le K (E (Fin.last m)).val (E n.castSucc).val
    (hE.monotone (Fin.le_last _)) hs.le le_rfl]
  exact apfPsi_apfPhi K (E n.castSucc).val (i n)

end FontaineWintenberger
