/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import FontaineWintenberger.APF.Elementary.FirstBreak
public import FontaineWintenberger.APF.Finite.Slope
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Fields.Wild

/-!
# The tame compositum and its Herbrand scaling

The same intrinsic first bound is compared before and after the
wild-fixed-field compositum. Positive upper groups and the subgroup
product condition give the scaling, including a zero first break.

The compositum of an intermediate field with the wild fixed field
is the wild fixed field over that intermediate base. All fields, own integer
rings, and Herbrand functions in these comparisons are the ones.

## Main results

* `exists_apfRamificationBound_wild_compositum`: The intrinsic first bounds before and after the
  tame compositum are finite and differ by the tame ramification index.
* `exists_apfRamificationBound_wild_compositum_of_totallyRamified`: A nontrivial totally ramified
  p-power subextension satisfies the same intrinsic first-bound scaling, using proved wild-inertia
  transitivity.
* `wild_compositum_extendScalars_eq_fixedField`: The tame compositum, over any intermediate base, is
  its own wild fixed field.
* `wild_fixedField_apfPsi`: The tame fixed field has the linear APF integral.
* `wild_compositum_apfPsi_over_right`: Over the right-hand base the compositum has its tame
  ramification index as its Herbrand slope.
* `wild_compositum_ramificationIdx_eq`: Wild-inertia transitivity identifies the tame ramification
  indices in the two towers, with no normality assumption on `F`.
* `wild_compositum_apfPsi_over_right_of_sup_eq_top`: Over the right-hand base, the tame slope equals
  the ramification index of the wild fixed field.
* `wild_compositum_apfPsi_scaling`: The two finite-base compositions give the full inverse Herbrand
  scaling for the same compositum and intermediate field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
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
    [PerfectField 𝓀[K]]

local notation "G" => L ≃ₐ[K] L
local notation "P" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 1
local notation "A" => IntermediateField.fixedField P
local notation "U" => upperRamificationGroup (R := spectralIntegerRing K L) G

local notation "e" => Ideal.ramificationIdx
  (IsLocalRing.maximalIdeal (spectralIntegerRing K A))
  𝒪[K]

local instance wildFirstBound_completeSpace : CompleteSpace A := FiniteDimensional.complete K A
local instance wildFirstBound_discreteValuationRing : IsCompleteDiscreteValuedField A :=
  normedAlgebra_isCompleteDiscreteValuedField K A
local instance wildFirstBound_perfectField : PerfectField 𝓀[A] :=
  Algebra.IsAlgebraic.perfectField 𝓀[K]

local instance wildFirstBound_finiteDimensional : FiniteDimensional A L :=
  FiniteDimensional.right K A L
local instance wildFirstBound_isGalois : IsGalois A L :=
  IsGalois.tower_top_of_isGalois K A L
local instance wildFirstBound_spectralDVR : IsDiscreteValuationRing
    (spectralIntegerRing A L) := by
  rw [← finiteBase_spectralIntegerRing_eq K L A]
  infer_instance

omit [IsUltrametricDist L] [FiniteDimensional K L]
  [PerfectField 𝓀[K]] in
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
  [PerfectField 𝓀[K]] in
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

/-- The intrinsic first bounds before and after the tame compositum
are finite and differ by the tame ramification index. -/
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

/-- A nontrivial totally ramified p-power subextension satisfies the
same intrinsic first-bound scaling, using proved wild-inertia transitivity. -/
theorem exists_apfRamificationBound_wild_compositum_of_totallyRamified
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K L)) p]
    (J : Subgroup G)
    (he : (IsLocalRing.maximalIdeal (Valuation.valuationSubring
      (Valuation.comap (algebraMap (IntermediateField.fixedField J) L)
        (spectralValuation K L)))).ramificationIdx
          𝒪[K] =
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

noncomputable section

namespace FontaineWintenberger

private theorem relIndex_inf_of_sup_eq_top
    {G : Type*} [Group G] (H P D : Subgroup G) [P.Normal]
    (hPD : P ≤ D) (hHP : H ⊔ P = ⊤) :
    P.relIndex (D ⊓ H) = P.relIndex D := by
  have hD : (H ⊓ D) ⊔ P = D := by
    apply le_antisymm (sup_le inf_le_right hPD)
    intro g hg
    have hg' : g ∈ H ⊔ P := hHP ▸ Subgroup.mem_top g
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hg'
    have haD : a ∈ D := by
      have h := D.mul_mem hg (D.inv_mem (hPD hb))
      simpa only [← hab, mul_inv_cancel_right] using h
    rw [← hab]
    exact ((H ⊓ D) ⊔ P).mul_mem
      ((show H ⊓ D ≤ _ from le_sup_left) ⟨ha, haD⟩)
      ((show P ≤ _ from le_sup_right) hb)
  calc
    _ = P.relIndex (H ⊓ D) := by rw [inf_comm]
    _ = P.relIndex ((H ⊓ D) ⊔ P) := (Subgroup.relIndex_sup_right (H ⊓ D) P).symm
    _ = P.relIndex D := congrArg P.relIndex hD

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω
local notation "P" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1
local notation "A" => IntermediateField.fixedField P
local notation "e" => Ideal.ramificationIdx
  (IsLocalRing.maximalIdeal (spectralIntegerRing K A))
  𝒪[K]

local instance (E : IntermediateField K Ω) : CompleteSpace E :=
  FiniteDimensional.complete K E
local instance (E : IntermediateField K Ω) :
    IsCompleteDiscreteValuedField E :=
  normedAlgebra_isCompleteDiscreteValuedField K E
local instance (E : IntermediateField K Ω) : PerfectField 𝓀[E] :=
  normedAlgebra_residueField_perfectField K E
local instance (E : IntermediateField K Ω) : FiniteDimensional E Ω :=
  Module.Finite.right K E Ω
local instance (E : IntermediateField K Ω) : IsGalois E Ω :=
  IsGalois.tower_top_of_isGalois K E Ω

omit [PerfectField 𝓀[K]] in
/-- The tame compositum, over any intermediate base, is its
own wild fixed field. No normality of the intermediate base is needed. -/
theorem wild_compositum_extendScalars_eq_fixedField (F : IntermediateField K Ω) :
    IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right) =
      IntermediateField.fixedField (lowerRamificationGroup (Ω ≃ₐ[F] Ω)
        (IsLocalRing.maximalIdeal (spectralIntegerRing F Ω)) 1) := by
  ext x
  change x ∈ A ⊔ F ↔ _
  rw [← IsGalois.fixedField_fixingSubgroup (A ⊔ F),
    IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff,
    IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField,
    ← finiteBase_lower_map_restrictScalars K Ω F 1]
  constructor
  · intro h g hg
    exact h ((AlgEquiv.restrictScalarsHom K) g) ⟨g, hg, rfl⟩
  · intro h g hg
    obtain ⟨g, hg, rfl⟩ := hg
    exact h g hg

omit [IsUltrametricDist Ω] in
/-- The tame fixed field has the linear APF integral. -/
theorem wild_fixedField_apfPsi {u : ℝ} (hu : 0 ≤ u) :
    apfPsi K A u =
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K A)).ramificationIdx
        𝒪[K] : ℝ) * u := by
  rw [apfPsi_eq_inverseHerbrandFunction K A (by linarith),
    wild_fixedField_inverseHerbrandFunction K Ω hu]

/-- Over the right-hand base the compositum has its tame
ramification index as its Herbrand slope. -/
theorem wild_compositum_apfPsi_over_right (F : IntermediateField K Ω)
    {u : ℝ} (hu : 0 ≤ u) :
    apfPsi F (IntermediateField.extendScalars
        (show F ≤ A ⊔ F from le_sup_right)) u =
      ((IsLocalRing.maximalIdeal (spectralIntegerRing F
        (IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)))).ramificationIdx
          𝒪[F] : ℝ) * u := by
  rw [wild_compositum_extendScalars_eq_fixedField K Ω F]
  exact wild_fixedField_apfPsi F Ω hu

/-- Wild-inertia transitivity identifies the tame ramification
indices in the two towers, with no normality assumption on `F`. -/
theorem wild_compositum_ramificationIdx_eq (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing F
      (IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)))).ramificationIdx
        𝒪[F] =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K A)).ramificationIdx
        𝒪[K] := by
  let M := A ⊔ F
  let N := IntermediateField.extendScalars (show F ≤ M from le_sup_right)
  have hfix : N.fixingSubgroup =
      (M.fixingSubgroup.subgroupOf F.fixingSubgroup).map
        F.fixingSubgroupEquiv.toMonoidHom := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    ext g
    rfl
  have hsub : M.fixingSubgroup.subgroupOf F.fixingSubgroup =
      (P).subgroupOf F.fixingSubgroup := by
    ext g
    simp only [M, Subgroup.mem_subgroupOf, IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField, Subgroup.mem_inf]
    exact and_iff_left g.property
  change (IsLocalRing.maximalIdeal (spectralIntegerRing F N)).ramificationIdx
      𝒪[F] = _
  rw [intermediate_spectral_ramificationIdx_eq_relIndex F Ω N, hfix,
    ← finiteBase_lower_map_fixingSubgroupEquiv K Ω F 0,
    Subgroup.relIndex_map_map_of_injective _ _ F.fixingSubgroupEquiv.injective,
    hsub]
  change ((P).comap F.fixingSubgroup.subtype).relIndex
      ((lowerRamificationGroup G (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω))
        0).subgroupOf F.fixingSubgroup) = _
  rw [Subgroup.relIndex_comap, Subgroup.subgroupOf_map_subtype,
    wild_fixedField_ramificationIdx_eq_relIndex K Ω]
  exact relIndex_inf_of_sup_eq_top F.fixingSubgroup P _
    (lowerRamificationGroup_antitone G (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω))
      (by norm_num : (0 : ℤ) ≤ 1)) hFP

/-- Over the right-hand base, the tame slope equals the
ramification index of the wild fixed field. -/
theorem wild_compositum_apfPsi_over_right_of_sup_eq_top (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) {u : ℝ} (hu : 0 ≤ u) :
    apfPsi F (IntermediateField.extendScalars
      (show F ≤ A ⊔ F from le_sup_right)) u = (e : ℝ) * u := by
  rw [wild_compositum_apfPsi_over_right K Ω F hu,
    wild_compositum_ramificationIdx_eq K Ω F hFP]

/-- The two finite-base compositions give the full inverse Herbrand
scaling for the same compositum and intermediate field. -/
theorem wild_compositum_apfPsi_scaling (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) {u : ℝ} (hu : 0 ≤ u) :
    apfPsi A (IntermediateField.extendScalars
      (show A ≤ A ⊔ F from le_sup_left)) ((e : ℝ) * u) =
        (e : ℝ) * apfPsi K F u := by
  let MA := IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)
  let MF := IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)
  let : Algebra.IsSeparable K MA := by
    change Algebra.IsSeparable K (A ⊔ F : IntermediateField K Ω)
    infer_instance
  let : Algebra.IsSeparable K MF := by
    change Algebra.IsSeparable K (A ⊔ F : IntermediateField K Ω)
    infer_instance
  let : FiniteDimensional K MA := by
    change FiniteDimensional K (A ⊔ F : IntermediateField K Ω)
    infer_instance
  let : FiniteDimensional K MF := by
    change FiniteDimensional K (A ⊔ F : IntermediateField K Ω)
    infer_instance
  have hA := IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K A MA
    u
  have hF := IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K F MF
    u
  calc
    _ = apfPsi K MA u := by
      rw [← wild_fixedField_apfPsi K Ω hu]
      exact hA
    _ = apfPsi K MF u := rfl
    _ = apfPsi F MF (apfPsi K F u) := hF.symm
    _ = _ := wild_compositum_apfPsi_over_right_of_sup_eq_top K Ω F hFP
      (hu.trans (IsAPF.le_apfPsi K F u))

/-- Inverting the scaled Herbrand equality gives the same scaling
for the Herbrand moduli, including zero. -/
theorem wild_compositum_apfPhi_scaling (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) {u : ℝ} (hu : 0 ≤ u) :
    apfPhi A (IntermediateField.extendScalars
        (show A ≤ A ⊔ F from le_sup_left)) ((e : ℝ) * u) =
      (e : ℝ) * apfPhi K F u := by
  let MA := IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)
  have hv : 0 ≤ apfPhi K F u := by
    by_contra h
    have hneg : apfPhi K F u < 0 := lt_of_not_ge h
    have heq := apfPsi_of_nonpos K F hneg.le
    rw [apfPsi_apfPhi] at heq
    linarith
  apply (IsAPF.strictMono_apfPsi A MA).injective
  calc
    _ = (e : ℝ) * u := apfPsi_apfPhi A MA _
    _ = (e : ℝ) * apfPsi K F (apfPhi K F u) := by
      rw [apfPsi_apfPhi]
    _ = _ := (wild_compositum_apfPsi_scaling K Ω F hFP hv).symm

/-- Total ramification and prime-power degree supply wild-inertia
transitivity, and hence all three Herbrand scalings for the fields.
Trivial steps are included; the intermediate field may be nonnormal. -/
theorem wild_compositum_herbrand_scaling_of_totallyRamified
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal ((spectralValuation K Ω).comap
      (algebraMap (IntermediateField.fixedField H) Ω)).valuationSubring).ramificationIdx
        𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n) :
    let F := IntermediateField.fixedField H
    let MA := IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)
    let MF := IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)
    (IsLocalRing.maximalIdeal (spectralIntegerRing F MF)).ramificationIdx
      𝒪[F] = e ∧
    ∀ u : ℝ, 0 ≤ u →
      apfPsi F MF u = (e : ℝ) * u ∧
      apfPsi A MA ((e : ℝ) * u) = (e : ℝ) * apfPsi K F u ∧
      apfPhi A MA ((e : ℝ) * u) =
        (e : ℝ) * apfPhi K F u := by
  let F := IntermediateField.fixedField H
  have hFP : F.fixingSubgroup ⊔ P = ⊤ := by
    simpa only [F, IntermediateField.fixingSubgroup_fixedField] using
      fixedField_sup_wild_eq_top K Ω p H he n hd
  exact ⟨wild_compositum_ramificationIdx_eq K Ω F hFP, fun u hu =>
    ⟨wild_compositum_apfPsi_over_right_of_sup_eq_top K Ω F hFP hu,
      wild_compositum_apfPsi_scaling K Ω F hFP hu,
      wild_compositum_apfPhi_scaling K Ω F hFP hu⟩⟩

end FontaineWintenberger
