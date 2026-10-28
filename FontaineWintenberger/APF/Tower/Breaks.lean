/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Herbrand
public import FontaineWintenberger.Mathlib.Order.RightJumps
public import FontaineWintenberger.Ramification.Upper.LocallyConstant

/-!
# The positive ramification breaks of an APF extension

The indices of the APF products are increasing and detect equality of the products.
Finite-stage approximation makes the products locally constant from the left. For an
infinite extension the indices are unbounded.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]

/-- The finite indices of the APF products increase with the upper parameter. -/
theorem monotoneOn_apfSubgroup_index :
    MonotoneOn (fun u ↦ (apfSubgroup K L u).index) (Set.Ici (-1)) := by
  intro u hu v hv huv
  have := (isAPFSubextension_iff_finiteIndex K L).mp ‹IsAPFSubextension K L› v hv
  exact Subgroup.index_antitone (apfSubgroup_antitoneOn K L hu hv huv)

/-- Equality of the finite indices detects equality of two APF products. -/
theorem apfSubgroup_eq_of_index_eq {u v : ℝ} (hu : -1 ≤ u) (hv : -1 ≤ v)
    (h : (apfSubgroup K L u).index = (apfSubgroup K L v).index) :
    apfSubgroup K L u = apfSubgroup K L v := by
  have := (isAPFSubextension_iff_finiteIndex K L).mp ‹IsAPFSubextension K L› u hu
  have := (isAPFSubextension_iff_finiteIndex K L).mp ‹IsAPFSubextension K L› v hv
  rcases le_total u v with huv | hvu
  · exact (Subgroup.eq_of_index_dvd_index (apfSubgroup_antitoneOn K L hu hv huv)
      (h.symm ▸ dvd_refl _)).symm
  · exact Subgroup.eq_of_index_dvd_index (apfSubgroup_antitoneOn K L hv hu hvu)
      (h ▸ dvd_refl _)

variable [PerfectField 𝓀[K]]

/-- APF products are locally constant from the left at every positive parameter. -/
theorem exists_apfSubgroup_eq_left {u : ℝ} (hu : 0 < u) :
    ∃ v : ℝ, 0 < v ∧ v < u ∧ ∀ w ∈ Set.Ioc v u,
      apfSubgroup K L w = apfSubgroup K L u := by
  let E := apfFiniteStage K L u
  have huf : -1 ≤ u := by linarith
  have : FiniteDimensional K E := finiteDimensional_apfFiniteStage K L huf
  let D := finiteGaloisNormalClosure K E
  let M := E.comap D.toIntermediateField.val
  have hmap : M.map D.toIntermediateField.val = E :=
    IntermediateField.map_comap_eq_self (by
      rw [IntermediateField.fieldRange_val]
      exact le_finiteGaloisNormalClosure K E)
  obtain ⟨v, hv, hvu, hlocal⟩ := exists_upperRamificationGroup_eq_left
    (R := spectralIntegerRing K D) (D ≃ₐ[K] D) hu
  have heq {w : ℝ} (hw : -1 ≤ w) (hwu : w ≤ u) :
      apfSubgroup K L w = apfSubgroup K E w :=
    (apfSubgroup_eq_of_apfFiniteStage_le K L E (apfFiniteStage_le K L u)
      (apfFiniteStage_mono K L hw huf hwu)).symm
  refine ⟨v, hv, hvu, fun w hw ↦ ?_⟩
  have hw' : -1 ≤ w := by linarith [hw.1]
  rw [heq hw' hw.2, heq huf le_rfl, ← hmap,
    apfSubgroup_map_eq_comap_sup_upper K D M hw',
    apfSubgroup_map_eq_comap_sup_upper K D M huf, hlocal w hw]

omit [PerfectField 𝓀[K]] in
/-- The indices of the APF products of an infinite extension are unbounded. -/
theorem exists_lt_apfSubgroup_index (hinfinite : ¬FiniteDimensional K L) (n : ℕ) :
    ∃ u : ℝ, 0 < u ∧ n < (apfSubgroup K L u).index := by
  by_contra! hbound
  let S : Set ℕ := {m | ∃ u : ℝ, 0 < u ∧ (apfSubgroup K L u).index = m}
  have hS : S.Nonempty := ⟨(apfSubgroup K L 1).index, 1, by norm_num, rfl⟩
  have hSb : BddAbove S := ⟨n, by rintro m ⟨u, hu, rfl⟩; exact hbound u hu⟩
  obtain ⟨d, ⟨⟨a, ha, had⟩, hmax⟩⟩ := hSb.exists_isGreatest_of_nonempty hS
  have hconstant {u : ℝ} (hau : a ≤ u) : apfSubgroup K L u = apfSubgroup K L a := by
    apply apfSubgroup_eq_of_index_eq K L (by linarith) (by linarith)
    apply le_antisymm
    · rw [had]
      exact hmax ⟨u, ha.trans_le hau, rfl⟩
    · exact monotoneOn_apfSubgroup_index K L (by change -1 ≤ a; linarith)
        (by change -1 ≤ u; linarith) hau
  have hstage : L = apfFiniteStage K L a := by
    apply le_antisymm ?_ (apfFiniteStage_le K L a)
    intro x hx
    let M := IntermediateField.adjoin K {x}
    have : FiniteDimensional K M :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hML : M ≤ L := IntermediateField.adjoin_simple_le_iff.mpr hx
    obtain ⟨U, _, hU⟩ := exists_le_apfFiniteStage K L M hML
    have hmem := hU (max U a) (le_max_left _ _)
      (IntermediateField.mem_adjoin_simple_self K x)
    simpa only [apfFiniteStage, hconstant (le_max_right U a)] using hmem
  apply hinfinite
  rw [hstage]
  exact finiteDimensional_apfFiniteStage K L (by linarith : -1 ≤ a)

end FontaineWintenberger

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : IntermediateField K (SeparableClosure K))

/-- A positive upper break of an extension: every larger upper parameter gives a strictly
smaller APF product. This is the set `B` in Wintenberger §1.4.1. -/
def IsAPFUpperBreak (u : ℝ) : Prop :=
  0 < u ∧ ∀ v : ℝ, u < v → apfSubgroup K L v ≠ apfSubgroup K L u

variable [IsAPFSubextension K L]

/-- Positive APF upper breaks are exactly the right jumps of the subgroup index. -/
theorem isAPFUpperBreak_iff {u : ℝ} :
    IsAPFUpperBreak K L u ↔
      0 < u ∧ IsRightJump (fun v ↦ (apfSubgroup K L v).index) u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v huv ↦ ?_⟩
    have := (isAPFSubextension_iff_finiteIndex K L).mp ‹IsAPFSubextension K L› v
      (by linarith : -1 ≤ v)
    exact Subgroup.index_strictAnti (lt_of_le_of_ne
      (apfSubgroup_antitoneOn K L (by change -1 ≤ u; linarith)
        (by change -1 ≤ v; linarith) huv.le) (h v huv))
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v huv heq ↦ ?_⟩
    exact (h v huv).ne (congrArg Subgroup.index heq).symm

/-- A bounded interval contains only finitely many positive upper breaks. -/
theorem finite_setOf_isAPFUpperBreak_le (u : ℝ) :
    {v : ℝ | IsAPFUpperBreak K L v ∧ v ≤ u}.Finite := by
  have hmono : MonotoneOn (fun v ↦ (apfSubgroup K L v).index) (Set.Ioi 0) :=
    (monotoneOn_apfSubgroup_index K L).mono (by
      intro v hv
      change -1 ≤ v
      change 0 < v at hv
      linarith)
  convert hmono.finite_setOf_rightJump_le u using 1
  ext v
  simp only [Set.mem_ofPred_eq, isAPFUpperBreak_iff, and_assoc]

variable [PerfectField 𝓀[K]]

/-- The positive upper breaks of an infinite APF extension form an increasing unbounded
sequence. Its intervals give the exact APF products, including their right endpoints. -/
theorem exists_apfUpperBreaks (hinfinite : ¬FiniteDimensional K L) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ n, 0 < b n) ∧ Tendsto b atTop atTop ∧
      (∀ u : ℝ, IsAPFUpperBreak K L u ↔ u ∈ Set.range b) ∧
      (∀ n u, b n < u → u ≤ b (n + 1) →
        apfSubgroup K L u = apfSubgroup K L (b (n + 1))) ∧
      ∀ u, 0 < u → u ≤ b 0 → apfSubgroup K L u = apfSubgroup K L (b 0) := by
  have hmono : MonotoneOn (fun v ↦ (apfSubgroup K L v).index) (Set.Ioi 0) :=
    (monotoneOn_apfSubgroup_index K L).mono (by
      intro v hv
      change -1 ≤ v
      change 0 < v at hv
      linarith)
  have hleft (u : ℝ) (hu : 0 < u) : ∃ v : ℝ, 0 < v ∧ v < u ∧
      ∀ x ∈ Set.Ioc v u, (apfSubgroup K L x).index = (apfSubgroup K L u).index := by
    obtain ⟨v, hv, hvu, h⟩ := exists_apfSubgroup_eq_left K L hu
    exact ⟨v, hv, hvu, fun x hx ↦ congrArg Subgroup.index (h x hx)⟩
  obtain ⟨b, hb, hpos, htop, hbreak, hinterval, hinitial⟩ :=
    hmono.exists_strictMono_rightJumps hleft (exists_lt_apfSubgroup_index K L hinfinite)
  refine ⟨b, hb, hpos, htop, ?_, ?_, ?_⟩
  · intro u
    rw [isAPFUpperBreak_iff]
    constructor
    · rintro ⟨hu, hj⟩
      exact (hbreak u hu).mp hj
    · rintro ⟨n, rfl⟩
      exact ⟨hpos n, (hbreak (b n) (hpos n)).mpr ⟨n, rfl⟩⟩
  · intro n u hnu hun
    exact apfSubgroup_eq_of_index_eq K L (by linarith [hpos n])
      (by linarith [hpos (n + 1)]) (hinterval n u hnu hun)
  · intro u hu hub
    exact apfSubgroup_eq_of_index_eq K L (by linarith) (by linarith [hpos 0])
      (hinitial u hu hub)

end FontaineWintenberger
