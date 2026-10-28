/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.FiniteProfile
public import FontaineWintenberger.APF.Tower.Tame
public import FontaineWintenberger.APF.Tower.UnionCriterion

/-!
# The APF criterion for elementary towers

An increasing sequence of finite fields with elementary successive steps determines
transformed upper levels `b n = apfPhi K (E n) (i n)`. If the first field is tame and
the elementary levels increase strictly, the transformed levels increase strictly as well.
The union is APF exactly when these transformed levels tend to infinity. In that case the
fields of the sequence are exactly the fixed fields at its upper ramification plateaux.

The indexing starts with the tame field `K₁` in Wintenberger's notation; the unramified
field `K₀` is already contained in this first field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.2.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]

/-- The ramification index of a finite subfield, computed in its spectral integer ring. -/
def FiniteIntermediateField.ramificationIdx
    (E : FiniteIntermediateField K (SeparableClosure K)) : ℕ :=
  (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val)).ramificationIdx 𝒪[K]

/-- A step between finite subfields is elementary for the canonical spectral norm on its base. -/
def IsElementaryStep (E F : FiniteIntermediateField K (SeparableClosure K))
    (hEF : E ≤ F) (i : ℝ) : Prop :=
  letI := spectralNorm.nontriviallyNormedField K E.val
  letI := spectralNorm.normedAlgebra K E.val
  letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  letI := spectralNorm.completeSpace K E.val
  letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
  IsElementary E.val (IntermediateField.extendScalars hEF) i

section Step

variable {K} {E F : FiniteIntermediateField K (SeparableClosure K)} {hEF : E ≤ F} {i : ℝ}

local instance elementaryStepNormedField : NontriviallyNormedField E.val :=
  spectralNorm.nontriviallyNormedField K E.val
local instance elementaryStepNormedAlgebra : NormedAlgebra K E.val :=
  spectralNorm.normedAlgebra K E.val
local instance elementaryStepUltrametric : IsUltrametricDist E.val :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
local instance elementaryStepCompleteSpace : CompleteSpace E.val :=
  spectralNorm.completeSpace K E.val
local instance elementaryStepDiscreteValuedField : IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val

omit [PerfectField 𝓀[K]] in
/-- An elementary step has positive level. -/
theorem IsElementaryStep.level_pos (h : IsElementaryStep K E F hEF i) : 0 < i :=
  IsElementary.level_pos h

omit [PerfectField 𝓀[K]] in
/-- The transformed level of an elementary step is positive. -/
theorem IsElementaryStep.apfPhi_pos (h : IsElementaryStep K E F hEF i) :
    0 < apfPhi K E.val i := by
  have hp := strictMono_apfPhi K E.val h.level_pos
  simpa only [apfPhi_of_nonpos K E.val le_rfl] using hp

/-- Strictly increasing elementary levels remain strictly increasing after base transformation. -/
theorem IsElementaryStep.apfPhi_lt (h : IsElementaryStep K E F hEF i) {j : ℝ} (hij : i < j) :
    apfPhi K E.val i < apfPhi K F.val j :=
  apfPhi_lt_of_isElementary K E.val F.val hEF h hij

/-- Adjoining an elementary step preserves the forward parameter at its own level. -/
theorem IsElementaryStep.apfPhi_eq (h : IsElementaryStep K E F hEF i) :
    apfPhi K F.val i = apfPhi K E.val i :=
  apfPhi_eq_of_isElementary K E.val F.val hEF h

/-- The absolute product is unchanged below the transformed level of an elementary step. -/
theorem IsElementaryStep.apfSubgroup_eq (h : IsElementaryStep K E F hEF i)
    {u : ℝ} (hu : -1 ≤ u) (hui : u ≤ apfPhi K E.val i) :
    apfSubgroup K F.val u = apfSubgroup K E.val u := by
  apply apfSubgroup_eq_of_isElementary K E.val F.val hEF h hu
  have hp := (IsAPF.strictMono_apfPsi K E.val).monotone hui
  simpa only [apfPsi_apfPhi] using hp

/-- Above the transformed level, an elementary step is fixed by every upper group already
fixing its base. -/
theorem IsElementaryStep.apfSubgroup_eq_fixingSubgroup (h : IsElementaryStep K E F hEF i)
    {u : ℝ} (hiu : apfPhi K E.val i < u)
    (hU : absoluteUpperRamificationGroup K u ≤ E.val.fixingSubgroup) :
    apfSubgroup K F.val u = F.val.fixingSubgroup := by
  apply apfSubgroup_eq_fixingSubgroup_of_isElementary K E.val F.val hEF h
    (by linarith [h.apfPhi_pos]) _ hU
  have hp := IsAPF.strictMono_apfPsi K E.val hiu
  simpa only [apfPsi_apfPhi] using hp

/-- A finite one-jump absolute profile determines an elementary step. -/
theorem isElementaryStep_of_apfSubgroup_profile {b : ℝ} (hb : 0 < b)
    (hfull : apfSubgroup K F.val b = E.val.fixingSubgroup)
    (htail : ∀ u : ℝ, b < u → apfSubgroup K F.val u = F.val.fixingSubgroup) :
    IsElementaryStep K E F hEF (apfPsi K E.val b) :=
  isElementary_of_apfSubgroup_profile K E.val F.val hEF hb hfull htail

end Step

variable (E : ℕ → FiniteIntermediateField K (SeparableClosure K)) (i : ℕ → ℝ)

/-- Finite elementary steps yield the absolute upper profiles at their transformed levels. -/
theorem elementary_tower_profiles (hE : Monotone E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup) :
    let b := fun n ↦ apfPhi K (E n).val (i n)
    StrictMono b ∧
      (∀ n u, -1 ≤ u → u ≤ b n →
        apfSubgroup K (E (n + 1)).val u = apfSubgroup K (E n).val u) ∧
      ∀ n u, b n < u →
        apfSubgroup K (E (n + 1)).val u = (E (n + 1)).val.fixingSubgroup := by
  let b := fun n ↦ apfPhi K (E n).val (i n)
  have hb : StrictMono b := strictMono_nat_of_lt_succ fun n ↦
    (helem n).apfPhi_lt (hi (Nat.lt_succ_self n))
  refine ⟨hb, fun n u hu hun ↦ (helem n).apfSubgroup_eq hu hun, ?_⟩
  intro n
  induction n with
  | zero =>
      intro u hu
      exact (helem 0).apfSubgroup_eq_fixingSubgroup hu
        (htame u ((helem 0).apfPhi_pos.trans hu))
  | succ n ih =>
      intro u hu
      apply (helem (n + 1)).apfSubgroup_eq_fixingSubgroup hu
      rw [← ih u ((hb (Nat.lt_succ_self n)).trans hu)]
      exact le_sup_right

/-- **Wintenberger 1.4.2**, infinite case: the union of a strictly increasing elementary
tower with tame first field is APF if and only if the transformed levels tend to infinity. -/
theorem isAPF_iSup_iff_tendsto_of_isElementaryStep (hE : StrictMono E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE.monotone (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup) :
    IsAPF K ↥(⨆ n, (E n).val) ↔
      Tendsto (fun n ↦ apfPhi K (E n).val (i n)) atTop atTop := by
  obtain ⟨hb, hstep, htail⟩ := elementary_tower_profiles K E i hE.monotone hi helem htame
  exact isAPF_iSup_iff_tendsto_of_step_profiles K E _ hE hb.monotone hstep htail

/-- When an elementary tower has APF union, its stages are precisely the finite fields
fixed by the union's upper products between consecutive transformed levels. -/
theorem apfFiniteStage_iSup_eq_of_isElementaryStep (hE : Monotone E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup)
    {n : ℕ} {u : ℝ} (hnu : apfPhi K (E n).val (i n) < u)
    (hun : u ≤ apfPhi K (E (n + 1)).val (i (n + 1))) :
    apfFiniteStage K (⨆ n, (E n).val) u = (E (n + 1)).val := by
  obtain ⟨hb, hstep, htail⟩ := elementary_tower_profiles K E i hE hi helem htame
  rw [apfFiniteStage, apfSubgroup_iSup_eq_fixingSubgroup_of_step_profiles K E _ hE hb.monotone
    hstep htail (by linarith [(helem n).apfPhi_pos]) hnu hun,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- Consecutive transformed levels differ by the elementary level increment divided by
the ramification index of the intervening field. -/
theorem apfPhi_succ_sub_of_isElementaryStep (hE : Monotone E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup)
    (n : ℕ) :
    apfPhi K (E (n + 1)).val (i (n + 1)) - apfPhi K (E n).val (i n) =
      (i (n + 1) - i n) /
        ((E (n + 1)).ramificationIdx K : ℝ) := by
  obtain ⟨hb, _hstep, htail⟩ := elementary_tower_profiles K E i hE hi helem htame
  have hs := apfPsi_sub_of_absoluteUpper_le K (E (n + 1)).val
    (helem n).apfPhi_pos.le (hb (Nat.lt_succ_self n)).le
    (fun u hu ↦ by rw [← htail n u hu]; exact le_sup_right)
  have hψ : apfPsi K (E (n + 1)).val (apfPhi K (E n).val (i n)) = i n := by
    rw [← (helem n).apfPhi_eq, apfPsi_apfPhi]
  rw [apfPsi_apfPhi, hψ] at hs
  have he : ((E (n + 1)).ramificationIdx K : ℝ) ≠ 0 := by
    intro he
    change _ = _ * ((E (n + 1)).ramificationIdx K : ℝ) at hs
    rw [he, mul_zero] at hs
    linarith [hi (Nat.lt_succ_self n)]
  exact (eq_div_iff he).mpr hs.symm

/-- The first transformed level is divided by the ramification index of the tame first field. -/
theorem apfPhi_zero_of_isElementaryStep (hE : Monotone E)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup) :
    apfPhi K (E 0).val (i 0) = i 0 /
      ((E 0).ramificationIdx K : ℝ) := by
  have hs := apfPsi_sub_of_absoluteUpper_le K (E 0).val le_rfl (helem 0).apfPhi_pos.le htame
  rw [apfPsi_apfPhi, apfPsi_zero, sub_zero, sub_zero] at hs
  have he : ((E 0).ramificationIdx K : ℝ) ≠ 0 := by
    intro he
    change _ = _ * ((E 0).ramificationIdx K : ℝ) at hs
    rw [he, mul_zero] at hs
    exact (ne_of_gt (helem 0).level_pos) hs
  exact (eq_div_iff he).mpr hs.symm

/-- The weighted-sum formula for the transformed levels in Wintenberger's Remark 1.4.2,
with the weights expressed as ramification indices of the finite fields. -/
theorem apfPhi_eq_sum_of_isElementaryStep (hE : Monotone E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE (Nat.le_succ n)) (i n))
    (htame : ∀ u : ℝ, 0 < u → absoluteUpperRamificationGroup K u ≤ (E 0).val.fixingSubgroup)
    (n : ℕ) :
    apfPhi K (E n).val (i n) =
      i 0 / ((E 0).ramificationIdx K : ℝ) +
      ∑ k ∈ Finset.range n, (i (k + 1) - i k) /
        ((E (k + 1)).ramificationIdx K : ℝ) := by
  induction n with
  | zero => simpa using apfPhi_zero_of_isElementaryStep K E i hE helem htame
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := apfPhi_succ_sub_of_isElementaryStep K E i hE hi helem htame n
      rw [ih] at hs
      linarith

end FontaineWintenberger

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (E : ℕ → FiniteIntermediateField K (SeparableClosure K)) (i : ℕ → ℝ)

/-- The APF criterion with tameness expressed by the usual prime-to-residue-characteristic
ramification index of the first field. -/
theorem isAPF_iSup_iff_tendsto_of_elementary_tower (hE : StrictMono E) (hi : StrictMono i)
    (helem : ∀ n, IsElementaryStep K (E n) (E (n + 1)) (hE.monotone (Nat.le_succ n)) (i n))
    (htame : Nat.Coprime (residueChar K)
      ((E 0).ramificationIdx K)) :
    IsAPF K ↥(⨆ n, (E n).val) ↔
      Tendsto (fun n ↦ apfPhi K (E n).val (i n)) atTop atTop := by
  apply isAPF_iSup_iff_tendsto_of_isElementaryStep K E i hE hi helem
  intro u hu
  exact (absoluteUpper_le_absoluteWildInertia K hu).trans
    ((spectral_ramificationIdx_coprime_iff_absoluteWildInertia_le K (E 0).val).mp htame)

end FontaineWintenberger
