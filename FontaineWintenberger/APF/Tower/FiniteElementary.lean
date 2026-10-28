/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Breaks
public import FontaineWintenberger.APF.Tower.Criterion
public import FontaineWintenberger.APF.Tower.FiniteConstants
public import Mathlib.Data.Finset.Sort

/-!
# The elementary tower of a finite extension

The positive upper breaks of a finite separable extension form a finite set. Sorting them
gives the finite elementary tower, with the original extension appended as its final field.
The indexing begins with Wintenberger's `K₁`; the unramified field `K₀` remains the stage at zero.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]

omit [PerfectField 𝓀[K]] in
/-- The union of a finite increasing tower of finite separable extensions is APF.
This is the finite alternative in Wintenberger's Remark 1.4.2. -/
theorem isAPF_iSup_fin {m : ℕ}
    (E : Fin (m + 1) → FiniteIntermediateField K (SeparableClosure K)) (hE : Monotone E) :
    IsAPF K ↥(⨆ n, (E n).val) := by
  have heq : (⨆ n, (E n).val) = (E (Fin.last m)).val := by
    apply le_antisymm (iSup_le fun n ↦ hE (Fin.le_last n))
    exact le_iSup (fun n ↦ (E n).val) (Fin.last m)
  apply (isAPF_iff_subextension K _).mpr
  rw [heq]
  infer_instance

variable (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]

local instance : IsAPFSubextension K L := isAPFSubextension_of_finite K L

local instance : IsAPF K L := (isAPF_iff_subextension K L).mpr inferInstance

omit [PerfectField 𝓀[K]] in
/-- A finite extension has only finitely many positive upper breaks. -/
theorem finite_setOf_isAPFUpperBreak : {u : ℝ | IsAPFUpperBreak K L u}.Finite := by
  obtain ⟨U, hU, hfix⟩ := exists_absoluteUpper_le_fixingSubgroup_of_finite K L
  apply (finite_setOf_isAPFUpperBreak_le K L U).subset
  intro u hu
  refine ⟨hu, ?_⟩
  by_contra! hUu
  have heq : apfSubgroup K L u = L.fixingSubgroup :=
    sup_eq_left.mpr (hfix u hUu.le)
  have heq' : apfSubgroup K L (u + 1) = L.fixingSubgroup :=
    sup_eq_left.mpr (hfix (u + 1) (by linarith))
  exact hu.2 (u + 1) (by linarith) (heq'.trans heq.symm)

/-- The finite set of positive upper breaks of a finite separable extension. -/
def apfFiniteUpperBreaks : Finset ℝ := (finite_setOf_isAPFUpperBreak K L).toFinset

omit [PerfectField 𝓀[K]] in
@[simp]
theorem mem_apfFiniteUpperBreaks {u : ℝ} :
    u ∈ apfFiniteUpperBreaks K L ↔ IsAPFUpperBreak K L u :=
  Set.Finite.mem_toFinset _

/-- The increasing enumeration of the positive upper breaks of a finite extension. -/
def apfFiniteUpperBreak : Fin (apfFiniteUpperBreaks K L).card ↪o ℝ :=
  (apfFiniteUpperBreaks K L).orderEmbOfFin rfl

omit [PerfectField 𝓀[K]] in
theorem isAPFUpperBreak_apfFiniteUpperBreak (n : Fin (apfFiniteUpperBreaks K L).card) :
    IsAPFUpperBreak K L (apfFiniteUpperBreak K L n) :=
  (mem_apfFiniteUpperBreaks K L).mp
    ((apfFiniteUpperBreaks K L).orderEmbOfFin_mem rfl n)

omit [PerfectField 𝓀[K]] in
theorem apfFiniteUpperBreak_pos (n : Fin (apfFiniteUpperBreaks K L).card) :
    0 < apfFiniteUpperBreak K L n := (isAPFUpperBreak_apfFiniteUpperBreak K L n).1

omit [PerfectField 𝓀[K]] in
theorem range_apfFiniteUpperBreak :
    Set.range (apfFiniteUpperBreak K L) = {u : ℝ | IsAPFUpperBreak K L u} := by
  rw [apfFiniteUpperBreak, Finset.range_orderEmbOfFin]
  ext u
  exact mem_apfFiniteUpperBreaks K L

/-- Without a positive upper break on a half-open interval, its endpoint products agree. -/
theorem apfSubgroup_eq_of_not_upperBreak {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (h : ∀ b ∈ Set.Ico u v, ¬IsAPFUpperBreak K L b) :
    apfSubgroup K L u = apfSubgroup K L v := by
  apply apfSubgroup_eq_of_index_eq K L (by linarith) (by linarith)
  have hm : MonotoneOn (fun v ↦ (apfSubgroup K L v).index) (Set.Ioi 0) :=
    (monotoneOn_apfSubgroup_index K L).mono
      (by intro v hv; change -1 ≤ v; change 0 < v at hv; linarith)
  have hl : ∀ w : ℝ, 0 < w → ∃ a : ℝ, 0 < a ∧ a < w ∧
      ∀ x ∈ Set.Ioc a w, (apfSubgroup K L x).index = (apfSubgroup K L w).index := by
    intro w hw
    obtain ⟨a, ha, haw, hconst⟩ := exists_apfSubgroup_eq_left K L hw
    exact ⟨a, ha, haw, fun x hx ↦ congrArg Subgroup.index (hconst x hx)⟩
  apply hm.eq_of_not_rightJump hl hu huv
  intro b hb hj
  exact h b hb ((isAPFUpperBreak_iff K L).mpr ⟨hu.trans_le hb.1, hj⟩)

/-- The interval preceding a listed finite break has constant APF product. -/
theorem apfSubgroup_eq_at_finiteUpperBreak (n : Fin (apfFiniteUpperBreaks K L).card)
    {u : ℝ} (hu : 0 < u) (hun : u ≤ apfFiniteUpperBreak K L n)
    (hprev : ∀ m : Fin (apfFiniteUpperBreaks K L).card,
      m < n → apfFiniteUpperBreak K L m < u) :
    apfSubgroup K L u = apfSubgroup K L (apfFiniteUpperBreak K L n) := by
  apply apfSubgroup_eq_of_not_upperBreak K L hu hun
  intro b hb hj
  have hmem : b ∈ Set.range (apfFiniteUpperBreak K L) := by
    rw [range_apfFiniteUpperBreak]
    exact hj
  obtain ⟨m, rfl⟩ := hmem
  exact (not_lt_of_ge hb.1) (hprev m ((apfFiniteUpperBreak K L).lt_iff_lt.mp hb.2))

/-- After the final positive upper break, the product is the fixing subgroup. -/
theorem apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks {u : ℝ} (hu : 0 < u)
    (hall : ∀ n : Fin (apfFiniteUpperBreaks K L).card, apfFiniteUpperBreak K L n < u) :
    apfSubgroup K L u = L.fixingSubgroup := by
  obtain ⟨U, _hU, hfix⟩ := exists_absoluteUpper_le_fixingSubgroup_of_finite K L
  have heq : apfSubgroup K L u = apfSubgroup K L (max U u) := by
    apply apfSubgroup_eq_of_not_upperBreak K L hu (le_max_right U u)
    intro b hb hj
    have hmem : b ∈ Set.range (apfFiniteUpperBreak K L) := by
      rw [range_apfFiniteUpperBreak]
      exact hj
    obtain ⟨n, rfl⟩ := hmem
    exact (not_lt_of_ge hb.1) (hall n)
  exact heq.trans (sup_eq_left.mpr (hfix _ (le_max_left U u)))

/-- The stages at the positive breaks, followed by the original extension as terminal stage. -/
def apfFiniteElementaryStage (n : Fin ((apfFiniteUpperBreaks K L).card + 1)) :
    FiniteIntermediateField K (SeparableClosure K) :=
  if h : n.val < (apfFiniteUpperBreaks K L).card then
    ⟨apfFiniteStage K L (apfFiniteUpperBreak K L ⟨n.val, h⟩),
      finiteDimensional_apfFiniteStage K L
        (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L ⟨n.val, h⟩).le)⟩
  else ⟨L, inferInstance⟩

omit [PerfectField 𝓀[K]] in
@[simp]
theorem apfFiniteElementaryStage_castSucc (n : Fin (apfFiniteUpperBreaks K L).card) :
    (apfFiniteElementaryStage K L n.castSucc).val =
      apfFiniteStage K L (apfFiniteUpperBreak K L n) := by
  simp only [apfFiniteElementaryStage, Fin.val_castSucc, n.isLt, dite_true]

omit [PerfectField 𝓀[K]] in
@[simp]
theorem apfFiniteElementaryStage_last :
    (apfFiniteElementaryStage K L (Fin.last (apfFiniteUpperBreaks K L).card)).val = L := by
  simp [apfFiniteElementaryStage]

omit [PerfectField 𝓀[K]] in
theorem apfFiniteElementaryStage_of_lt
    (n : Fin ((apfFiniteUpperBreaks K L).card + 1)) (hn : n.val < (apfFiniteUpperBreaks K L).card) :
    (apfFiniteElementaryStage K L n).val =
      apfFiniteStage K L (apfFiniteUpperBreak K L ⟨n.val, hn⟩) := by
  simp only [apfFiniteElementaryStage, hn, dite_true]

omit [PerfectField 𝓀[K]] in
theorem apfFiniteElementaryStage_of_not_lt
    (n : Fin ((apfFiniteUpperBreaks K L).card + 1))
    (hn : ¬n.val < (apfFiniteUpperBreaks K L).card) :
    (apfFiniteElementaryStage K L n).val = L := by
  simp only [apfFiniteElementaryStage, hn, dite_false]

omit [PerfectField 𝓀[K]] in
@[simp]
theorem fixingSubgroup_apfFiniteElementaryStage_castSucc
    (n : Fin (apfFiniteUpperBreaks K L).card) :
    (apfFiniteElementaryStage K L n.castSucc).val.fixingSubgroup =
      apfSubgroup K L (apfFiniteUpperBreak K L n) := by
  rw [apfFiniteElementaryStage_castSucc, fixingSubgroup_apfFiniteStage]

omit [PerfectField 𝓀[K]] in
theorem apfFiniteElementaryStage_le (n : Fin ((apfFiniteUpperBreaks K L).card + 1)) :
    (apfFiniteElementaryStage K L n).val ≤ L := by
  unfold apfFiniteElementaryStage
  split
  · exact apfFiniteStage_le K L _
  · exact le_rfl

omit [PerfectField 𝓀[K]] in
/-- Every stage belongs to the original extension, and the terminal stage is that extension. -/
theorem iSup_apfFiniteElementaryStage :
    (⨆ n, (apfFiniteElementaryStage K L n).val) = L := by
  apply le_antisymm (iSup_le (apfFiniteElementaryStage_le K L))
  simpa only [apfFiniteElementaryStage_last] using
    le_iSup (fun n ↦ (apfFiniteElementaryStage K L n).val)
      (Fin.last (apfFiniteUpperBreaks K L).card)

/-- Above a finite upper break, the absolute upper group fixes the next stage. -/
theorem absoluteUpper_le_apfFiniteElementaryStage_succ
    (n : Fin (apfFiniteUpperBreaks K L).card) {u : ℝ}
    (hnu : apfFiniteUpperBreak K L n < u) :
    absoluteUpperRamificationGroup K u ≤ (apfFiniteElementaryStage K L n.succ).val.fixingSubgroup :=
    by
  have hu : 0 < u := (apfFiniteUpperBreak_pos K L n).trans hnu
  by_cases hn : n.val + 1 < (apfFiniteUpperBreaks K L).card
  · let m : Fin (apfFiniteUpperBreaks K L).card := ⟨n.val + 1, hn⟩
    rw [apfFiniteElementaryStage_of_lt K L n.succ hn, fixingSubgroup_apfFiniteStage]
    change absoluteUpperRamificationGroup K u ≤ apfSubgroup K L (apfFiniteUpperBreak K L m)
    rcases le_total u (apfFiniteUpperBreak K L m) with hum | hmu
    · rw [← apfSubgroup_eq_at_finiteUpperBreak K L m hu hum (fun j hj ↦ ?_)]
      · exact le_sup_right
      · exact ((apfFiniteUpperBreak K L).monotone (Nat.le_of_lt_succ hj)).trans_lt hnu
    · exact (upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K)
        (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L m).le)
        (neg_one_lt_zero.le.trans hu.le) hmu).trans le_sup_right
  · rw [apfFiniteElementaryStage_of_not_lt K L n.succ hn]
    rw [← apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks K L hu (fun j ↦ ?_)]
    · exact le_sup_right
    · exact ((apfFiniteUpperBreak K L).monotone
        (Nat.le_of_lt_succ (j.isLt.trans_le (not_lt.mp hn)))).trans_lt hnu

omit [PerfectField 𝓀[K]] in
/-- Successive stages of the finite elementary tower are nested. -/
theorem apfFiniteElementaryStage_castSucc_le_succ
    (n : Fin (apfFiniteUpperBreaks K L).card) :
    apfFiniteElementaryStage K L n.castSucc ≤ apfFiniteElementaryStage K L n.succ := by
  change (apfFiniteElementaryStage K L n.castSucc).val ≤ _
  rw [apfFiniteElementaryStage_castSucc]
  by_cases hn : n.val + 1 < (apfFiniteUpperBreaks K L).card
  · rw [apfFiniteElementaryStage_of_lt K L n.succ hn]
    exact apfFiniteStage_mono K L
      (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L n).le)
      (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L ⟨n.val + 1, hn⟩).le)
      ((apfFiniteUpperBreak K L).monotone (Nat.le_succ n.val))
  · rw [apfFiniteElementaryStage_of_not_lt K L n.succ hn]
    exact apfFiniteStage_le K L _

omit [PerfectField 𝓀[K]] in
/-- The finite elementary tower is strictly increasing, including its terminal step. -/
theorem strictMono_apfFiniteElementaryStage : StrictMono (apfFiniteElementaryStage K L) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro n
  refine lt_of_le_of_ne (apfFiniteElementaryStage_castSucc_le_succ K L n) ?_
  intro heq
  have hfix := congrArg (fun E : FiniteIntermediateField K (SeparableClosure K) ↦
    E.val.fixingSubgroup) heq
  rw [fixingSubgroup_apfFiniteElementaryStage_castSucc] at hfix
  by_cases hn : n.val + 1 < (apfFiniteUpperBreaks K L).card
  · rw [apfFiniteElementaryStage_of_lt K L n.succ hn, fixingSubgroup_apfFiniteStage] at hfix
    exact (isAPFUpperBreak_apfFiniteUpperBreak K L n).2 _
      ((apfFiniteUpperBreak K L).strictMono (Nat.lt_succ_self n.val)) hfix.symm
  · rw [apfFiniteElementaryStage_of_not_lt K L n.succ hn] at hfix
    apply (isAPFUpperBreak_apfFiniteUpperBreak K L n).2
      (apfFiniteUpperBreak K L n + 1) (by linarith)
    apply le_antisymm
    · exact apfSubgroup_antitoneOn K L
        (by change -1 ≤ apfFiniteUpperBreak K L n; linarith [apfFiniteUpperBreak_pos K L n])
        (by change -1 ≤ apfFiniteUpperBreak K L n + 1
            linarith [apfFiniteUpperBreak_pos K L n]) (by linarith)
    · rw [hfix]
      exact le_sup_left

/-- The lower-numbered positive breaks of a finite extension. -/
def apfFiniteElementaryLevel (n : Fin (apfFiniteUpperBreaks K L).card) : ℝ :=
  apfPsi K L (apfFiniteUpperBreak K L n)

omit [PerfectField 𝓀[K]] in
theorem apfFiniteElementaryLevel_pos (n : Fin (apfFiniteUpperBreaks K L).card) :
    0 < apfFiniteElementaryLevel K L n :=
  (apfFiniteUpperBreak_pos K L n).trans_le (IsAPF.le_apfPsi K L _)

omit [PerfectField 𝓀[K]] in
theorem strictMono_apfFiniteElementaryLevel : StrictMono (apfFiniteElementaryLevel K L) :=
  (IsAPF.strictMono_apfPsi K L).comp (apfFiniteUpperBreak K L).strictMono

/-- The next finite field gives the entire plateau following a listed upper break,
including the final unbounded plateau. -/
theorem apfSubgroup_eq_fixingSubgroup_finiteElementaryStage_succ
    (n : Fin (apfFiniteUpperBreaks K L).card) {u : ℝ}
    (hnu : apfFiniteUpperBreak K L n < u)
    (hnext : ∀ k : Fin (apfFiniteUpperBreaks K L).card,
      n < k → u ≤ apfFiniteUpperBreak K L k) :
    apfSubgroup K L u = (apfFiniteElementaryStage K L n.succ).val.fixingSubgroup := by
  have hu : 0 < u := (apfFiniteUpperBreak_pos K L n).trans hnu
  by_cases hn : n.val + 1 < (apfFiniteUpperBreaks K L).card
  · let m : Fin (apfFiniteUpperBreaks K L).card := ⟨n.val + 1, hn⟩
    rw [apfFiniteElementaryStage_of_lt K L n.succ hn, fixingSubgroup_apfFiniteStage]
    apply apfSubgroup_eq_at_finiteUpperBreak K L m hu (hnext m (Nat.lt_succ_self n.val))
    intro j hj
    exact ((apfFiniteUpperBreak K L).monotone (Nat.le_of_lt_succ hj)).trans_lt hnu
  · rw [apfFiniteElementaryStage_of_not_lt K L n.succ hn]
    apply apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks K L hu
    intro j
    exact ((apfFiniteUpperBreak K L).monotone
      (Nat.le_of_lt_succ (j.isLt.trans_le (not_lt.mp hn)))).trans_lt hnu

omit [PerfectField 𝓀[K]] in
/-- A finite-stage Herbrand function computes the same lower-numbered break. -/
theorem apfFiniteElementaryLevel_eq (n : Fin (apfFiniteUpperBreaks K L).card) :
    apfFiniteElementaryLevel K L n =
      apfPsi K (apfFiniteElementaryStage K L n.castSucc).val (apfFiniteUpperBreak K L n) := by
  rw [apfFiniteElementaryStage_castSucc]
  exact (apfPsi_eq_of_apfFiniteStage_le K L _ (apfFiniteStage_le K L _) le_rfl le_rfl).symm

/-- Each step of the finite canonical tower is elementary at its lower-numbered break. -/
theorem isElementaryStep_apfFiniteElementaryStage
    (n : Fin (apfFiniteUpperBreaks K L).card) :
    IsElementaryStep K (apfFiniteElementaryStage K L n.castSucc)
      (apfFiniteElementaryStage K L n.succ) (apfFiniteElementaryStage_castSucc_le_succ K L n)
      (apfFiniteElementaryLevel K L n) := by
  rw [apfFiniteElementaryLevel_eq]
  apply isElementaryStep_of_apfSubgroup_profile (apfFiniteUpperBreak_pos K L n)
  · rw [fixingSubgroup_apfFiniteElementaryStage_castSucc]
    apply apfSubgroup_eq_of_apfFiniteStage_le K L _ (apfFiniteElementaryStage_le K L n.succ)
    rw [← apfFiniteElementaryStage_castSucc K L n]
    exact apfFiniteElementaryStage_castSucc_le_succ K L n
  · intro u hu
    exact sup_eq_left.mpr (absoluteUpper_le_apfFiniteElementaryStage_succ K L n hu)

/-- Each finite elementary level is the first bound of the remaining extension over
its corresponding stage. -/
theorem apfRamificationBound_over_apfFiniteElementaryStage
    (n : Fin (apfFiniteUpperBreaks K L).card) :
    let E := (apfFiniteElementaryStage K L n.castSucc).val
    letI := spectralNorm.nontriviallyNormedField K E
    letI := spectralNorm.normedAlgebra K E
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E))
    letI := spectralNorm.completeSpace K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    apfRamificationBound E
        (IntermediateField.extendScalars (apfFiniteElementaryStage_le K L n.castSucc)) =
      (apfFiniteElementaryLevel K L n : EReal) := by
  let E := (apfFiniteElementaryStage K L n.castSucc).val
  let := spectralNorm.nontriviallyNormedField K E
  let := spectralNorm.normedAlgebra K E
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))
  let := spectralNorm.completeSpace K E
  let := normedAlgebra_isCompleteDiscreteValuedField K E
  rw [apfFiniteElementaryLevel_eq]
  apply apfRamificationBound_eq_of_apfSubgroup_jump K E L
    (apfFiniteElementaryStage_le K L n.castSucc) (apfFiniteUpperBreak_pos K L n)
    (fixingSubgroup_apfFiniteElementaryStage_castSucc K L n).symm
  intro u hu
  rw [show E.fixingSubgroup = apfSubgroup K L (apfFiniteUpperBreak K L n) from
    fixingSubgroup_apfFiniteElementaryStage_castSucc K L n]
  exact (isAPFUpperBreak_apfFiniteUpperBreak K L n).2 u hu

/-- A finite extension with positive first bound and no positive breaks has infinite first
bound. This includes the trivial extension, whose elementary tower has no steps. -/
theorem apfRamificationBound_eq_top_of_no_finiteUpperBreaks
    (hi : (0 : EReal) < apfRamificationBound K L)
    (hc : (apfFiniteUpperBreaks K L).card = 0) : apfRamificationBound K L = ⊤ := by
  have hi' := hi
  rw [apfRamificationBound_eq_embedding K L L.val, IntermediateField.fieldRange_val] at hi'
  obtain ⟨_, ⟨v, _hv, hfull, rfl⟩, hvpos⟩ := lt_sSup_iff.mp hi'
  have hvpos : 0 < v := EReal.coe_pos.mp hvpos
  have hfix : L.fixingSubgroup = ⊤ :=
    (apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks K L hvpos
      (fun n ↦ Fin.elim0 (n.cast hc))).symm.trans hfull
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  have hbound : ((max r 0 + 1 : ℝ) : EReal) ≤ apfRamificationBound K L := by
    apply le_apfRamificationBound K L L.val (by linarith [le_max_right r 0])
    simp only [IntermediateField.fieldRange_val, apfSubgroup, hfix, top_sup_eq]
  exact (EReal.coe_lt_coe_iff.mpr (by linarith [le_max_left r 0])).trans_le hbound

variable [NeZero (apfFiniteUpperBreaks K L).card]

/-- With positive first bound, the first finite upper break is the endpoint of the
initial full-product interval. -/
theorem apfSubgroup_eq_top_iff_le_first_finiteUpperBreak
    (hi : (0 : EReal) < apfRamificationBound K L) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K L u = ⊤ ↔ u ≤ apfFiniteUpperBreak K L 0 := by
  have htop : apfSubgroup K L (apfFiniteUpperBreak K L 0) = ⊤ := by
    rw [apfRamificationBound_eq_embedding K L L.val, IntermediateField.fieldRange_val] at hi
    obtain ⟨_, ⟨v, hv, hfull, rfl⟩, hvpos⟩ := lt_sSup_iff.mp hi
    have hvpos : 0 < v := EReal.coe_pos.mp hvpos
    rcases le_total v (apfFiniteUpperBreak K L 0) with hvb | hbv
    · rw [← apfSubgroup_eq_at_finiteUpperBreak K L 0 hvpos hvb (by
        intro m hm
        exact (not_lt_of_ge (Fin.zero_le m) hm).elim)]
      exact hfull
    · apply top_unique
      rw [← hfull]
      exact apfSubgroup_antitoneOn K L
        (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L 0).le) hv hbv
  constructor
  · intro h
    by_contra! hub
    exact (isAPFUpperBreak_apfFiniteUpperBreak K L 0).2 u hub (h.trans htop.symm)
  · intro hub
    apply top_unique
    rw [← htop]
    exact apfSubgroup_antitoneOn K L hu
      (neg_one_lt_zero.le.trans (apfFiniteUpperBreak_pos K L 0).le) hub

/-- The finite version of Wintenberger's identity `i(L/K) = i₁`. -/
theorem apfRamificationBound_eq_apfFiniteElementaryLevel
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfRamificationBound K L = (apfFiniteElementaryLevel K L 0 : EReal) := by
  apply apfRamificationBound_eq_apfPsi_of_apfSubgroup_eq_top_iff K L L.val
    (apfFiniteUpperBreak_pos K L 0).le
  intro u hu
  simpa only [IntermediateField.fieldRange_val] using
    apfSubgroup_eq_top_iff_le_first_finiteUpperBreak K L hi hu

/-- The finite version of Wintenberger's elementary-level formula for the strictness
constant. The denominator in the final term is the degree of the original extension. -/
theorem apfStrictnessConstant_eq_iInf_apfFiniteElementaryLevel_of_nonempty
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfStrictnessConstant K L =
      ⨅ n : Fin (apfFiniteUpperBreaks K L).card,
        ENNReal.ofReal (apfFiniteElementaryLevel K L n /
          Module.finrank K (apfFiniteElementaryStage K L n.succ).val) := by
  apply apfStrictnessConstant_eq_iInf_finrank_of_finite_plateaux K L L.val
    (apfFiniteElementaryStage K L) (apfFiniteUpperBreak K L)
    (apfFiniteUpperBreak K L).strictMono (apfFiniteUpperBreak_pos K L 0).le
  · intro u hu
    simpa only [IntermediateField.fieldRange_val] using
      apfSubgroup_eq_top_iff_le_first_finiteUpperBreak K L hi hu
  · intro n u hnu hun
    simpa only [IntermediateField.fieldRange_val] using
      apfSubgroup_eq_fixingSubgroup_finiteElementaryStage_succ K L n hnu hun

omit [NeZero (apfFiniteUpperBreaks K L).card] in
/-- Wintenberger's finite elementary-level formula, including the empty tower: its empty
infimum and strictness constant are both infinity. -/
theorem apfStrictnessConstant_eq_iInf_apfFiniteElementaryLevel
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfStrictnessConstant K L =
      ⨅ n : Fin (apfFiniteUpperBreaks K L).card,
        ENNReal.ofReal (apfFiniteElementaryLevel K L n /
          Module.finrank K (apfFiniteElementaryStage K L n.succ).val) := by
  by_cases hc : (apfFiniteUpperBreaks K L).card = 0
  · have : IsEmpty (Fin (apfFiniteUpperBreaks K L).card) := ⟨fun n ↦ Fin.elim0 (n.cast hc)⟩
    rw [apfStrictnessConstant_of_bound_eq_top K L
      (apfRamificationBound_eq_top_of_no_finiteUpperBreaks K L hi hc)]
    simp
  · let : NeZero (apfFiniteUpperBreaks K L).card := ⟨hc⟩
    exact apfStrictnessConstant_eq_iInf_apfFiniteElementaryLevel_of_nonempty K L hi

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]

/-- The finite elementary tower starts with the maximal tame stage. If there are no
positive breaks, this sole stage is the original extension. -/
theorem apfFiniteElementaryStage_zero :
    (apfFiniteElementaryStage K L 0).val = apfTameStage K L := by
  by_cases hc : 0 < (apfFiniteUpperBreaks K L).card
  · rw [apfFiniteElementaryStage_of_lt K L 0 hc]
    apply congrArg IntermediateField.fixedField
    apply le_antisymm
    · exact sup_le_sup_left (absoluteUpper_le_absoluteWildInertia K
        (apfFiniteUpperBreak_pos K L ⟨0, hc⟩)) _
    · apply sup_le le_sup_left
      apply Subgroup.topologicalClosure_minimal
      · apply iSup_le
        intro u
        apply (show absoluteUpperRamificationGroup K u.val ≤ apfSubgroup K L u.val from
          le_sup_right).trans
        rcases le_total u.val (apfFiniteUpperBreak K L ⟨0, hc⟩) with hu | hu
        · exact (apfSubgroup_eq_at_finiteUpperBreak K L ⟨0, hc⟩ u.property hu (by
            intro m hm
            change m.val < 0 at hm
            omega)).le
        · exact apfSubgroup_antitoneOn K L
            (by change -1 ≤ apfFiniteUpperBreak K L ⟨0, hc⟩
                linarith [apfFiniteUpperBreak_pos K L ⟨0, hc⟩])
            (by change -1 ≤ u.val; linarith [u.property]) hu
      · exact isClosed_apfSubgroup K L _
  · rw [apfFiniteElementaryStage_of_not_lt K L 0 hc]
    have hU : absoluteWildInertia K ≤ L.fixingSubgroup := by
      apply Subgroup.topologicalClosure_minimal
      · apply iSup_le
        intro u
        rw [← apfSubgroup_eq_fixingSubgroup_after_finiteUpperBreaks K L u.property (fun n ↦ ?_)]
        · exact le_sup_right
        · have := n.isLt
          omega
      · exact InfiniteGalois.fixingSubgroup_isClosed L
    rw [apfTameStage, apfTameSubgroup, sup_eq_left.mpr hU,
      InfiniteGalois.fixedField_fixingSubgroup]

end FontaineWintenberger
