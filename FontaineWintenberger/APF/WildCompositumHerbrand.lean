/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.AbstractFiniteBase
public import FontaineWintenberger.APF.FiniteTail
public import FontaineWintenberger.Ramification.WildTower

/-!
# Herbrand scaling for the actual tame compositum

The compositum of an intermediate field with the original wild fixed field
is the wild fixed field over that intermediate base. All fields, own integer
rings, and Herbrand functions in these comparisons are the original ones.
-/

@[expose] public section

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
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω
local notation "P" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1
local notation "A" => IntermediateField.fixedField P
local notation "e" => Ideal.ramificationIdx
  (IsLocalRing.maximalIdeal (spectralIntegerRing K A))
  (Valuation.valuationSubring (NormedField.valuation (K := K)))

local instance (E : IntermediateField K Ω) : CompleteSpace E :=
  FiniteDimensional.complete K E
local instance (E : IntermediateField K Ω) :
    IsCompleteDiscreteValuedField E :=
  normedAlgebra_isCompleteDiscreteValuedField K E
local instance (E : IntermediateField K Ω) : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := E)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K E
local instance (E : IntermediateField K Ω) : FiniteDimensional E Ω :=
  Module.Finite.right K E Ω
local instance (E : IntermediateField K Ω) : IsGalois E Ω :=
  IsGalois.tower_top_of_isGalois K E Ω

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- The actual tame compositum, over any actual intermediate base, is its
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
/-- The original tame fixed field has the actual linear APF integral. -/
theorem wild_fixedField_apfPsi {u : ℝ} (hu : 0 ≤ u) :
    apfPsi K A u =
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K A)).ramificationIdx
        (NormedField.valuation (K := K)).valuationSubring : ℝ) * u := by
  rw [apfPsi_eq_inverseHerbrandFunction K A (by linarith),
    wild_fixedField_inverseHerbrandFunction K Ω hu]

/-- Over the original right-hand base the compositum has its genuine tame
ramification index as its Herbrand slope. -/
theorem wild_compositum_apfPsi_over_right (F : IntermediateField K Ω)
    {u : ℝ} (hu : 0 ≤ u) :
    apfPsi F (IntermediateField.extendScalars
        (show F ≤ A ⊔ F from le_sup_right)) u =
      ((IsLocalRing.maximalIdeal (spectralIntegerRing F
        (IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)))).ramificationIdx
          (NormedField.valuation (K := F)).valuationSubring : ℝ) * u := by
  rw [wild_compositum_extendScalars_eq_fixedField K Ω F]
  exact wild_fixedField_apfPsi F Ω hu

/-- Wild-inertia transitivity identifies the actual tame ramification
indices in the two original towers, with no normality assumption on `F`. -/
theorem wild_compositum_ramificationIdx_eq (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) :
    (IsLocalRing.maximalIdeal (spectralIntegerRing F
      (IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)))).ramificationIdx
        (NormedField.valuation (K := F)).valuationSubring =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K A)).ramificationIdx
        (NormedField.valuation (K := K)).valuationSubring := by
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
      (NormedField.valuation (K := F)).valuationSubring = _
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

/-- Over the original right-hand base, the tame slope equals the actual
ramification index of the original wild fixed field. -/
theorem wild_compositum_apfPsi_over_right_of_sup_eq_top (F : IntermediateField K Ω)
    (hFP : F.fixingSubgroup ⊔ P = ⊤) {u : ℝ} (hu : 0 ≤ u) :
    apfPsi F (IntermediateField.extendScalars
      (show F ≤ A ⊔ F from le_sup_right)) u = (e : ℝ) * u := by
  rw [wild_compositum_apfPsi_over_right K Ω F hu,
    wild_compositum_ramificationIdx_eq K Ω F hFP]

/-- The two actual finite-base compositions give the full inverse Herbrand
scaling for the same compositum and original intermediate field. -/
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

/-- Inverting the actual scaled Herbrand equality gives the same scaling
for the original Herbrand moduli, including zero. -/
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

/-- Actual total ramification and prime-power degree supply wild-inertia
transitivity, and hence all three Herbrand scalings for the original fields.
Trivial steps are included; the original intermediate field may be nonnormal. -/
theorem wild_compositum_herbrand_scaling_of_totallyRamified
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal ((spectralValuation K Ω).comap
      (algebraMap (IntermediateField.fixedField H) Ω)).valuationSubring).ramificationIdx
        (NormedField.valuation (K := K)).valuationSubring =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n) :
    let F := IntermediateField.fixedField H
    let MA := IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)
    let MF := IntermediateField.extendScalars (show F ≤ A ⊔ F from le_sup_right)
    (IsLocalRing.maximalIdeal (spectralIntegerRing F MF)).ramificationIdx
      (NormedField.valuation (K := F)).valuationSubring = e ∧
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
