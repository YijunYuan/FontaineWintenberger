/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FirstBound
public import FontaineWintenberger.APF.FiniteOverfieldBaseChange
public import FontaineWintenberger.Ramification.WildTower

/-!
# First-bound scaling by the actual tame fixed field

The same intrinsic first bound is compared before and after the genuine
wild-fixed-field compositum. Positive upper groups and the actual subgroup
product condition give the scaling, including a zero first break.
-/

@[expose] public section

namespace FontaineWintenberger

private theorem sup_eq_top_iff_subgroupOf_sup_eq_top
    {G : Type*} [Group G] (J P U : Subgroup G) [U.Normal]
    (hUP : U ≤ P) (hHP : J ⊔ P = ⊤) :
    J ⊔ U = ⊤ ↔ J.subgroupOf P ⊔ U.subgroupOf P = ⊤ := by
  constructor
  · intro ht
    apply top_unique
    intro g _
    have hg : (g : G) ∈ J ⊔ U := ht ▸ Subgroup.mem_top _
    obtain ⟨h, hh, u, hu, he⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hhP : h ∈ P := by
      have h := P.mul_mem g.property (P.inv_mem (hUP hu))
      simpa only [← he, mul_inv_cancel_right] using h
    have he' : (⟨h, hhP⟩ : P) * ⟨u, hUP hu⟩ = g := Subtype.ext he
    rw [← he']
    exact (J.subgroupOf P ⊔ U.subgroupOf P).mul_mem
      ((show J.subgroupOf P ≤ _ from le_sup_left) hh)
      ((show U.subgroupOf P ≤ _ from le_sup_right) hu)
  · intro ht
    have hP : P ≤ J ⊔ U := by
      intro g hg
      have hmap := congrArg (Subgroup.map P.subtype) ht
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype] at hmap
      have hg' : g ∈ (⊤ : Subgroup P).map P.subtype := ⟨⟨g, hg⟩, trivial, rfl⟩
      rw [← hmap] at hg'
      have hle : (J ⊓ P) ⊔ (U ⊓ P) ≤ J ⊔ U :=
        sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
      exact hle hg'
    exact top_unique (hHP ▸ sup_le le_sup_left hP)

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [FiniteDimensional K L] [IsGalois K L]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "G" => L ≃ₐ[K] L
local notation "P" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 1
local notation "A" => IntermediateField.fixedField P
local notation "U" => upperRamificationGroup (R := spectralIntegerRing K L) G

local notation "e" => Ideal.ramificationIdx
  (IsLocalRing.maximalIdeal (spectralIntegerRing K A))
  (Valuation.valuationSubring (NormedField.valuation (K := K)))

local instance wildFirstBound_completeSpace : CompleteSpace A := FiniteDimensional.complete K A
local instance wildFirstBound_discreteValuationRing : IsCompleteDiscreteValuedField A :=
  normedAlgebra_isCompleteDiscreteValuedField K A
local instance wildFirstBound_perfectField : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := A)).valuationSubring) :=
  Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)

local instance wildFirstBound_finiteDimensional : FiniteDimensional A L :=
  FiniteDimensional.right K A L
local instance wildFirstBound_isGalois : IsGalois A L :=
  IsGalois.tower_top_of_isGalois K A L
local instance wildFirstBound_spectralDVR : IsDiscreteValuationRing
    (spectralIntegerRing A L) := by
  rw [← finiteBase_spectralIntegerRing_eq K L A]
  infer_instance

omit [IsUltrametricDist L] [FiniteDimensional K L]
  [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem wild_compositum_fixing_map (J : Subgroup G) :
    ((IntermediateField.fixedField P ⊔ IntermediateField.fixedField J).fixingSubgroup.subgroupOf
        (A).fixingSubgroup).map
      (A).fixingSubgroupEquiv.toMonoidHom = (IntermediateField.extendScalars (le_sup_left :
          IntermediateField.fixedField P ≤ (IntermediateField.fixedField P ⊔
              IntermediateField.fixedField J))).fixingSubgroup := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  ext g
  rfl

omit [IsUltrametricDist L]
  [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem wild_compositum_fixing_proper (J : Subgroup G) (hH : J ≠ ⊤) (hHP : J ⊔ P = ⊤) :
    (IntermediateField.extendScalars (le_sup_left : IntermediateField.fixedField P ≤
        (IntermediateField.fixedField P ⊔ IntermediateField.fixedField J))).fixingSubgroup ≠ ⊤ := by
  intro ht
  have hfix : (IntermediateField.extendScalars (le_sup_left : IntermediateField.fixedField P ≤
      (IntermediateField.fixedField P ⊔ IntermediateField.fixedField J))).fixingSubgroup =
      ((IntermediateField.fixedField P ⊔ IntermediateField.fixedField J).fixingSubgroup.subgroupOf
          (A).fixingSubgroup).comap
        (A).fixingSubgroupEquiv.symm.toMonoidHom := by
    rw [← wild_compositum_fixing_map K L J, Subgroup.map_equiv_eq_comap_symm']
  have hle : P ≤ J := by
    intro g hg
    let gA : (A).fixingSubgroup := ⟨g, by
      simpa only [IntermediateField.fixingSubgroup_fixedField] using hg⟩
    have hm : (A).fixingSubgroupEquiv gA ∈ (IntermediateField.extendScalars (le_sup_left :
        IntermediateField.fixedField P ≤ (IntermediateField.fixedField P ⊔
            IntermediateField.fixedField J))).fixingSubgroup := ht ▸ Subgroup.mem_top _
    rw [hfix] at hm
    change g ∈ (IntermediateField.fixedField P ⊔
      IntermediateField.fixedField J).fixingSubgroup at hm
    rw [IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField] at hm
    exact hm.2
  exact hH (by simpa only [sup_eq_left.mpr hle] using hHP)

private theorem wild_compositum_upper_product_eq_top_iff (J : Subgroup G)
    (hHP : J ⊔ P = ⊤) {u : ℝ} (hu : 0 < u) :
    J ⊔ U u = ⊤ ↔ (IntermediateField.extendScalars (le_sup_left : IntermediateField.fixedField P ≤
        (IntermediateField.fixedField P ⊔ IntermediateField.fixedField J))).fixingSubgroup ⊔
      upperRamificationGroup (R := spectralIntegerRing A L) (L ≃ₐ[A] L)
        ((e : ℝ) * u) = ⊤ := by
  have hpsi : apfPsi K A u = (e : ℝ) * u := by
    rw [apfPsi_eq_inverseHerbrandFunction K A (by linarith),
      wild_fixedField_inverseHerbrandFunction K L hu.le]
  rw [← hpsi, finiteBase_upperRamificationGroup_of_finiteGalois K L A (by linarith),
    ← wild_compositum_fixing_map K L J, ← Subgroup.map_sup]
  have hsub : (IntermediateField.fixedField P ⊔ IntermediateField.fixedField
      J).fixingSubgroup.subgroupOf (A).fixingSubgroup =
      J.subgroupOf (A).fixingSubgroup := by
    ext g
    simp only [Subgroup.mem_subgroupOf, IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField, Subgroup.mem_inf]
    exact and_iff_right (by
      simpa only [IntermediateField.fixingSubgroup_fixedField] using g.property)
  rw [hsub]
  have hmap : ∀ S : Subgroup (A).fixingSubgroup,
      S.map (A).fixingSubgroupEquiv.toMonoidHom = ⊤ ↔ S = ⊤ := by
    intro S
    constructor
    · intro ht
      apply Subgroup.map_injective (f := (A).fixingSubgroupEquiv.toMonoidHom)
        (A).fixingSubgroupEquiv.injective
      rw [ht, Subgroup.map_top_of_surjective _ (A).fixingSubgroupEquiv.surjective]
    · intro ht
      rw [ht, Subgroup.map_top_of_surjective _ (A).fixingSubgroupEquiv.surjective]
  rw [hmap]
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact sup_eq_top_iff_subgroupOf_sup_eq_top J P (U u)
      (upperRamificationGroup_le_lower_one G hu) hHP

/-- The intrinsic first bounds before and after the actual tame compositum
are finite and differ by the actual tame ramification index. -/
theorem exists_apfRamificationBound_wild_compositum (J : Subgroup G)
    (hJ : J ≠ ⊤) (hJP : J ⊔ P = ⊤) :
    letI := wildFirstBound_discreteValuationRing K L
    ∃ b : ℝ, 0 ≤ b ∧
      apfRamificationBound K (IntermediateField.fixedField J) = (b : EReal) ∧
      apfRamificationBound A (IntermediateField.extendScalars
        (le_sup_left : A ≤ A ⊔ IntermediateField.fixedField J)) =
          (((e : ℝ) * b : ℝ) : EReal) := by
  let := wildFirstBound_discreteValuationRing K L
  let := wildFirstBound_perfectField K L
  have hz : J ⊔ lowerRamificationGroup G
      (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 0 = ⊤ := by
    apply top_unique
    rw [← hJP]
    exact sup_le_sup_left (lowerRamificationGroup_antitone G
      (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) (by norm_num : (0 : ℤ) ≤ 1)) J
  have hJ' : (IntermediateField.fixedField J).fixingSubgroup = J :=
    IntermediateField.fixingSubgroup_fixedField J
  obtain ⟨b, hb, hbound, hprofile⟩ :=
    exists_apfRamificationBound_eq_coe_of_fixingSubgroup K L
      (IntermediateField.fixedField J)
      (by simpa only [hJ'] using hJ) (by simpa only [hJ'] using hz)
  let N := IntermediateField.extendScalars
    (le_sup_left : A ≤ A ⊔ IntermediateField.fixedField J)
  have hproper : N.fixingSubgroup ≠ ⊤ := wild_compositum_fixing_proper K L J hJ hJP
  have hz' : N.fixingSubgroup ⊔ lowerRamificationGroup (L ≃ₐ[A] L)
      (IsLocalRing.maximalIdeal (spectralIntegerRing A L)) 0 = ⊤ := by
    rw [wildField_lower_zero_eq_top K L A le_rfl, sup_top_eq]
  obtain ⟨c, hc, hbound', hprofile'⟩ :=
    exists_apfRamificationBound_eq_coe_of_fixingSubgroup A L N hproper hz'
  have hepos : 0 < (e : ℝ) := by
    rw [← spectralIntegerRing_card_lower_zero K A]
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup (A ≃ₐ[K] A)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K A)) 0))
  have hiff (u : ℝ) (hu : 0 < u) : u ≤ b ↔ (e : ℝ) * u ≤ c := by
    have hpos : 0 ≤ (e : ℝ) * u := mul_nonneg hepos.le hu.le
    rw [← hprofile u (by linarith), hJ']
    exact (wild_compositum_upper_product_eq_top_iff K L J hJP hu).trans
      (hprofile' ((e : ℝ) * u) (by linarith))
  have hscale : c = (e : ℝ) * b := by
    apply le_antisymm
    · by_cases hc0 : c = 0
      · rw [hc0]
        exact mul_nonneg hepos.le hb
      · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
        have h := (hiff (c / (e : ℝ)) (div_pos hcpos hepos)).mpr
          (by rw [mul_div_cancel₀ _ (ne_of_gt hepos)])
        exact (div_le_iff₀ hepos).mp h |>.trans_eq (mul_comm _ _)
    · by_cases hb0 : b = 0
      · simpa only [hb0, mul_zero] using hc
      · exact (hiff b (lt_of_le_of_ne hb (Ne.symm hb0))).mp le_rfl
  refine ⟨b, hb, hbound, ?_⟩
  rw [hbound', hscale]

/-- A nontrivial actual totally ramified p-power subextension satisfies the
same intrinsic first-bound scaling, using proved wild-inertia transitivity. -/
theorem exists_apfRamificationBound_wild_compositum_of_totallyRamified
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K L)) p]
    (J : Subgroup G)
    (he : (IsLocalRing.maximalIdeal (Valuation.valuationSubring
      (Valuation.comap (algebraMap (IntermediateField.fixedField J) L)
        (spectralValuation K L)))).ramificationIdx
          (NormedField.valuation (K := K)).valuationSubring =
            Module.finrank K (IntermediateField.fixedField J))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField J) = p ^ n)
    (hdegree : 1 < Module.finrank K (IntermediateField.fixedField J)) :
    letI := wildFirstBound_discreteValuationRing K L
    ∃ b : ℝ, 0 ≤ b ∧
      apfRamificationBound K (IntermediateField.fixedField J) = (b : EReal) ∧
      apfRamificationBound A (IntermediateField.extendScalars
        (le_sup_left : A ≤ A ⊔ IntermediateField.fixedField J)) =
          (((e : ℝ) * b : ℝ) : EReal) := by
  apply exists_apfRamificationBound_wild_compositum K L J
  · intro ht
    have hi : Module.finrank K (IntermediateField.fixedField J) = 1 := by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        IntermediateField.fixingSubgroup_fixedField, ht, Subgroup.index_top]
    omega
  · exact fixedField_sup_wild_eq_top K L p J he n hd

end FontaineWintenberger
