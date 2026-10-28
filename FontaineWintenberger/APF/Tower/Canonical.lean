/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Breaks
public import FontaineWintenberger.APF.Tower.Criterion
public import FontaineWintenberger.APF.Tower.Elementary
public import FontaineWintenberger.APF.Tower.Tame

/-!
# The canonical elementary tower of an infinite APF extension

The positive upper breaks give a strictly increasing, cofinal tower of finite fields.
Its first field is the maximal tame subextension, and successive steps are elementary
at the corresponding lower-numbered breaks, which tend to infinity.

The indexing here starts at zero with Wintenberger's `K₁`; `apfElementaryStage n` is his
`K_{n+1}`, and `apfElementaryLevel n` is his `i_{n+1}`. The separate unramified stage is
`apfFiniteStage K L 0`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.1.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter
open scoped ENNReal

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    [Fact (¬ Module.Finite K L)]

/-- The increasing enumeration of the positive upper breaks of an infinite APF extension. -/
def apfUpperBreak : ℕ → ℝ :=
  (exists_apfUpperBreaks K L Fact.out).choose

private theorem apfUpperBreak_spec :
    StrictMono (apfUpperBreak K L) ∧ (∀ n, 0 < apfUpperBreak K L n) ∧
      Tendsto (apfUpperBreak K L) atTop atTop ∧
      (∀ u : ℝ, IsAPFUpperBreak K L u ↔ u ∈ Set.range (apfUpperBreak K L)) ∧
      (∀ n u, apfUpperBreak K L n < u → u ≤ apfUpperBreak K L (n + 1) →
        apfSubgroup K L u = apfSubgroup K L (apfUpperBreak K L (n + 1))) ∧
      ∀ u, 0 < u → u ≤ apfUpperBreak K L 0 →
        apfSubgroup K L u = apfSubgroup K L (apfUpperBreak K L 0) :=
  (exists_apfUpperBreaks K L Fact.out).choose_spec

theorem strictMono_apfUpperBreak : StrictMono (apfUpperBreak K L) :=
  (apfUpperBreak_spec K L).1

theorem apfUpperBreak_pos (n : ℕ) : 0 < apfUpperBreak K L n :=
  (apfUpperBreak_spec K L).2.1 n

theorem tendsto_apfUpperBreak : Tendsto (apfUpperBreak K L) atTop atTop :=
  (apfUpperBreak_spec K L).2.2.1

theorem isAPFUpperBreak_iff_mem_range (u : ℝ) :
    IsAPFUpperBreak K L u ↔ u ∈ Set.range (apfUpperBreak K L) :=
  (apfUpperBreak_spec K L).2.2.2.1 u

theorem isAPFUpperBreak_apfUpperBreak (n : ℕ) :
    IsAPFUpperBreak K L (apfUpperBreak K L n) :=
  (isAPFUpperBreak_iff_mem_range K L _).mpr ⟨n, rfl⟩

/-- Between successive upper breaks, the APF product is its value at the right endpoint. -/
theorem apfSubgroup_eq_at_next_upperBreak {n : ℕ} {u : ℝ}
    (hnu : apfUpperBreak K L n < u) (hun : u ≤ apfUpperBreak K L (n + 1)) :
    apfSubgroup K L u = apfSubgroup K L (apfUpperBreak K L (n + 1)) :=
  (apfUpperBreak_spec K L).2.2.2.2.1 n u hnu hun

/-- The positive initial interval ends at the first positive upper break. -/
theorem apfSubgroup_eq_at_first_upperBreak {u : ℝ} (hu : 0 < u)
    (hub : u ≤ apfUpperBreak K L 0) :
    apfSubgroup K L u = apfSubgroup K L (apfUpperBreak K L 0) :=
  (apfUpperBreak_spec K L).2.2.2.2.2 u hu hub

/-- The finite field fixed by the APF product at a positive upper break. -/
def apfElementaryStage (n : ℕ) : FiniteIntermediateField K (SeparableClosure K) :=
  ⟨apfFiniteStage K L (apfUpperBreak K L n),
    finiteDimensional_apfFiniteStage K L (by linarith [apfUpperBreak_pos K L n])⟩

@[simp]
theorem fixingSubgroup_apfElementaryStage (n : ℕ) :
    (apfElementaryStage K L n).val.fixingSubgroup =
      apfSubgroup K L (apfUpperBreak K L n) :=
  fixingSubgroup_apfFiniteStage K L _

theorem apfElementaryStage_le (n : ℕ) : (apfElementaryStage K L n).val ≤ L :=
  apfFiniteStage_le K L _

/-- The elementary tower is strictly increasing. -/
theorem strictMono_apfElementaryStage : StrictMono (apfElementaryStage K L) := by
  intro m n hmn
  have hbreak := strictMono_apfUpperBreak K L hmn
  refine lt_of_le_of_ne (apfFiniteStage_mono K L
    (by linarith [apfUpperBreak_pos K L m])
    (by linarith [apfUpperBreak_pos K L n]) hbreak.le) ?_
  intro heq
  have hfix := congrArg (fun E : FiniteIntermediateField K (SeparableClosure K) ↦
    E.val.fixingSubgroup) heq
  simp only [fixingSubgroup_apfElementaryStage] at hfix
  exact (isAPFUpperBreak_apfUpperBreak K L m).2 _ hbreak hfix.symm

/-- Every finite subextension is contained in a field of the elementary tower. -/
theorem exists_le_apfElementaryStage (M : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K M] (hML : M ≤ L) :
    ∃ n, M ≤ (apfElementaryStage K L n).val := by
  obtain ⟨U, _, hU⟩ := exists_le_apfFiniteStage K L M hML
  obtain ⟨n, hn⟩ := ((tendsto_apfUpperBreak K L).eventually (eventually_ge_atTop U)).exists
  exact ⟨n, hU _ hn⟩

/-- The union of the elementary tower is the original extension. -/
theorem iSup_apfElementaryStage : (⨆ n, (apfElementaryStage K L n).val) = L := by
  apply le_antisymm (iSup_le (apfElementaryStage_le K L))
  intro x hx
  let M := IntermediateField.adjoin K {x}
  have : FiniteDimensional K M :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn⟩ := exists_le_apfElementaryStage K L M
    (IntermediateField.adjoin_simple_le_iff.mpr hx)
  exact (le_iSup (fun n ↦ (apfElementaryStage K L n).val) n)
    (hn (IntermediateField.mem_adjoin_simple_self K x))

/-- The lower-numbered break, equal to the elementary level of the next step. -/
def apfElementaryLevel (n : ℕ) : ℝ :=
  apfPsi K L (apfUpperBreak K L n)

theorem apfElementaryLevel_pos (n : ℕ) : 0 < apfElementaryLevel K L n :=
  (apfUpperBreak_pos K L n).trans_le (IsAPF.le_apfPsi K L _)

theorem strictMono_apfElementaryLevel : StrictMono (apfElementaryLevel K L) :=
  (IsAPF.strictMono_apfPsi K L).comp (strictMono_apfUpperBreak K L)

/-- The elementary levels tend to infinity. -/
theorem tendsto_apfElementaryLevel : Tendsto (apfElementaryLevel K L) atTop atTop :=
  tendsto_apfPsi_comp_atTop K L (tendsto_apfUpperBreak K L)

/-- The finite-stage and infinite-extension Herbrand functions give the same elementary level. -/
theorem apfElementaryLevel_eq (n : ℕ) :
    apfElementaryLevel K L n =
      apfPsi K (apfElementaryStage K L n).val (apfUpperBreak K L n) :=
  (apfPsi_eq_of_apfFiniteStage_le K L (apfElementaryStage K L n).val
    (apfElementaryStage_le K L n) le_rfl le_rfl).symm

/-- Successive fields in the canonical tower are elementary at the lower-numbered break. -/
theorem isElementaryStep_apfElementaryStage (n : ℕ) :
    IsElementaryStep K (apfElementaryStage K L n) (apfElementaryStage K L (n + 1))
      ((strictMono_apfElementaryStage K L).monotone (Nat.le_succ n))
      (apfElementaryLevel K L n) := by
  rw [apfElementaryLevel_eq]
  apply isElementaryStep_of_apfSubgroup_profile (apfUpperBreak_pos K L n)
  · rw [fixingSubgroup_apfElementaryStage]
    apply apfSubgroup_eq_of_apfFiniteStage_le K L _ (apfElementaryStage_le K L _)
    exact (strictMono_apfElementaryStage K L).monotone (Nat.le_succ n)
  · intro u hu
    by_cases hun : u ≤ apfUpperBreak K L (n + 1)
    · rw [fixingSubgroup_apfElementaryStage,
        apfSubgroup_eq_of_apfFiniteStage_le K L _ (apfElementaryStage_le K L _)
          (apfFiniteStage_mono K L
            (by linarith [apfUpperBreak_pos K L n])
            (by linarith [apfUpperBreak_pos K L (n + 1)]) hun)]
      exact apfSubgroup_eq_at_next_upperBreak K L hu hun
    · apply sup_eq_left.mpr
      rw [fixingSubgroup_apfElementaryStage]
      apply (upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K)
        (by change -1 ≤ apfUpperBreak K L (n + 1); linarith [apfUpperBreak_pos K L (n + 1)])
        (by change -1 ≤ u; linarith [apfUpperBreak_pos K L n]) (le_of_not_ge hun)).trans
      exact le_sup_right

/-- When the first ramification bound is positive, the first positive break is exactly the
endpoint of the full APF product. -/
theorem apfSubgroup_eq_top_iff_le_first_upperBreak
    (hi : (0 : EReal) < apfRamificationBound K L) {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K L u = ⊤ ↔ u ≤ apfUpperBreak K L 0 := by
  have htop : apfSubgroup K L (apfUpperBreak K L 0) = ⊤ := by
    rw [apfRamificationBound_eq_embedding K L L.val,
      IntermediateField.fieldRange_val] at hi
    obtain ⟨_, ⟨v, hv, hfull, rfl⟩, hvpos⟩ := lt_sSup_iff.mp hi
    have hvpos : 0 < v := EReal.coe_pos.mp hvpos
    rcases le_total v (apfUpperBreak K L 0) with hvb | hbv
    · rw [← apfSubgroup_eq_at_first_upperBreak K L hvpos hvb]
      exact hfull
    · apply top_unique
      rw [← hfull]
      exact apfSubgroup_antitoneOn K L
        (by change -1 ≤ apfUpperBreak K L 0; linarith [apfUpperBreak_pos K L 0]) hv hbv
  constructor
  · intro h
    by_contra! hub
    exact (isAPFUpperBreak_apfUpperBreak K L 0).2 u hub (h.trans htop.symm)
  · intro hub
    apply top_unique
    rw [← htop]
    exact apfSubgroup_antitoneOn K L hu
      (by change -1 ≤ apfUpperBreak K L 0; linarith [apfUpperBreak_pos K L 0]) hub

/-- **Wintenberger §1.4.1:** `i(L/K) = i₁`, with the hypothesis `i(L/K) > 0` from the paper.
The index zero on the right denotes the first elementary level. -/
theorem apfRamificationBound_eq_apfElementaryLevel
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfRamificationBound K L = (apfElementaryLevel K L 0 : EReal) := by
  apply apfRamificationBound_eq_apfPsi_of_apfSubgroup_eq_top_iff K L L.val
    (apfUpperBreak_pos K L 0).le
  intro u hu
  simpa only [IntermediateField.fieldRange_val] using
    apfSubgroup_eq_top_iff_le_first_upperBreak K L hi hu

/-- **Wintenberger §1.4.1:** the strictness constant is the infimum of the elementary level
divided by the degree of the next field. The positive first-bound hypothesis is essential. -/
theorem apfStrictnessConstant_eq_iInf_apfElementaryLevel
    (hi : (0 : EReal) < apfRamificationBound K L) :
    apfStrictnessConstant K L =
      ⨅ n, ENNReal.ofReal (apfElementaryLevel K L n /
        Module.finrank K (apfElementaryStage K L (n + 1)).val) := by
  apply apfStrictnessConstant_eq_iInf_finrank_of_apfSubgroup_plateaux K L L.val
    (apfElementaryStage K L) (apfUpperBreak K L) (strictMono_apfUpperBreak K L)
    (apfUpperBreak_pos K L 0).le (tendsto_apfUpperBreak K L)
  · intro u hu
    simpa only [IntermediateField.fieldRange_val] using
      apfSubgroup_eq_top_iff_le_first_upperBreak K L hi hu
  · intro n u hnu hun
    simpa only [IntermediateField.fieldRange_val, fixingSubgroup_apfElementaryStage] using
      apfSubgroup_eq_at_next_upperBreak K L hnu hun

/-- The elementary level is also the first ramification bound of the entire remaining
extension over that stage: `i_n = i(L/K_n)` in Wintenberger §1.4.1. -/
theorem apfRamificationBound_over_apfElementaryStage (n : ℕ) :
    let E := (apfElementaryStage K L n).val
    letI := spectralNorm.nontriviallyNormedField K E
    letI := spectralNorm.normedAlgebra K E
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E))
    letI := spectralNorm.completeSpace K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    apfRamificationBound E (IntermediateField.extendScalars (apfElementaryStage_le K L n)) =
      (apfElementaryLevel K L n : EReal) := by
  let E := (apfElementaryStage K L n).val
  let := spectralNorm.nontriviallyNormedField K E
  let := spectralNorm.normedAlgebra K E
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))
  let := spectralNorm.completeSpace K E
  let := normedAlgebra_isCompleteDiscreteValuedField K E
  rw [apfElementaryLevel_eq]
  apply apfRamificationBound_eq_of_apfSubgroup_jump K E L (apfElementaryStage_le K L n)
    (apfUpperBreak_pos K L n) (fixingSubgroup_apfElementaryStage K L n).symm
  intro u hu
  rw [show E.fixingSubgroup = apfSubgroup K L (apfUpperBreak K L n) from
    fixingSubgroup_apfElementaryStage K L n]
  exact (isAPFUpperBreak_apfUpperBreak K L n).2 u hu

/-- For a positive first ramification bound, strict APF is equivalent to a uniform positive
lower bound on the elementary levels divided by the degrees of the following fields. -/
theorem isStrictlyAPF_iff_apfElementaryLevel_div_finrank_of_ramificationBound_pos
    (hi : (0 : EReal) < apfRamificationBound K L) :
    IsStrictlyAPF K L ↔ ∃ c : ℝ, 0 < c ∧ ∀ n,
      c < apfElementaryLevel K L n / Module.finrank K (apfElementaryStage K L (n + 1)).val := by
  rw [isStrictlyAPF_iff_constant_pos K L hi,
    apfStrictnessConstant_eq_iInf_apfElementaryLevel K L hi]
  constructor
  · intro h
    obtain ⟨c, hc, hcf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    refine ⟨c, by exact_mod_cast hc, fun n ↦ ?_⟩
    have hcn := hcf.trans_le (iInf_le _ n)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg c.2).mp (by simpa using hcn)
  · rintro ⟨c, hc, hcn⟩
    exact (ENNReal.ofReal_pos.mpr hc).trans_le
      (le_iInf fun n ↦ ENNReal.ofReal_le_ofReal (hcn n).le)

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    [Fact (¬ Module.Finite K L)]

/-- The first field of the positive-break tower is the maximal tame stage. -/
theorem apfElementaryStage_zero :
    (apfElementaryStage K L 0).val = apfTameStage K L := by
  apply congrArg IntermediateField.fixedField
  apply le_antisymm
  · exact sup_le_sup_left (absoluteUpper_le_absoluteWildInertia K
      (apfUpperBreak_pos K L 0)) _
  · apply sup_le le_sup_left
    apply Subgroup.topologicalClosure_minimal
    · apply iSup_le
      intro u
      apply (show absoluteUpperRamificationGroup K u.val ≤ apfSubgroup K L u.val from
        le_sup_right).trans
      rcases le_total u.val (apfUpperBreak K L 0) with hu | hu
      · exact (apfSubgroup_eq_at_first_upperBreak K L u.property hu).le
      · exact apfSubgroup_antitoneOn K L
          (by change -1 ≤ apfUpperBreak K L 0; linarith [apfUpperBreak_pos K L 0])
          (by change -1 ≤ u.val; linarith [u.property]) hu
    · exact isClosed_apfSubgroup K L _

/-- Every step after the tame stage has prime-power degree, including nonnormal steps. -/
theorem apfElementaryStage_finrank_eq_prime_pow (n : ℕ) :
    ∃ r : ℕ, Module.finrank (apfElementaryStage K L n).val
      (IntermediateField.extendScalars
        ((strictMono_apfElementaryStage K L).monotone (Nat.le_succ n))) =
      residueChar K ^ r := by
  apply finrank_eq_prime_pow_of_apfTameStage_le K L
    (apfElementaryStage K L n).val (apfElementaryStage K L (n + 1)).val
    (apfElementaryStage_le K L (n + 1))
  rw [← apfElementaryStage_zero K L]
  exact (strictMono_apfElementaryStage K L).monotone (Nat.zero_le n)

end FontaineWintenberger
