/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.Elementary.Basic
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.APF.Finite.Slope

/-!
# Upper products across an elementary step

Finite base change translates an elementary extension into a single new jump of the absolute
upper products. Below its transformed level the product agrees with that of the base field.
Above the transformed level it is the fixing subgroup, provided the preceding field has no
remaining ramification at that parameter.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]

local instance finiteProfileNormedField : NontriviallyNormedField E :=
  spectralNorm.nontriviallyNormedField K E
local instance finiteProfileNormedAlgebra : NormedAlgebra K E := spectralNorm.normedAlgebra K E
local instance finiteProfileUltrametric : IsUltrametricDist E :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))
local instance finiteProfileCompleteSpace : CompleteSpace E := spectralNorm.completeSpace K E
local instance finiteProfileDiscreteValuedField : IsCompleteDiscreteValuedField E :=
  normedAlgebra_isCompleteDiscreteValuedField K E
local instance finiteProfileClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra'

variable (F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)

private def stepEmbedding : (IntermediateField.extendScalars hEF) →ₐ[E] SeparableClosure E :=
  (separableClosureBaseChangeEquiv K E).symm.toAlgHom.comp
    (IntermediateField.extendScalars hEF).val

omit [IsCompleteDiscreteValuedField K] [PerfectField 𝓀[K]] [FiniteDimensional K E] in
private theorem stepEmbedding_fieldRange :
    (baseChangedSeparableEmbedding K E (stepEmbedding K E F hEF)).fieldRange = F := by
  have he (x : IntermediateField.extendScalars hEF) :
      baseChangedSeparableEmbedding K E (stepEmbedding K E F hEF) x =
        (x : SeparableClosure K) := by
    change (separableClosureBaseChangeEquiv K E)
      ((separableClosureBaseChangeEquiv K E).symm (x : SeparableClosure K)) = _
    exact (separableClosureBaseChangeEquiv K E).apply_symm_apply x
  ext x
  constructor
  · rintro ⟨y, hy⟩
    change baseChangedSeparableEmbedding K E (stepEmbedding K E F hEF) y = x at hy
    rw [he] at hy
    exact hy ▸ y.property
  · intro hx
    exact ⟨⟨x, hx⟩, he _⟩

local notation "ρ" =>
  MonoidHom.comp (Subgroup.subtype (IntermediateField.fixingSubgroup E))
    (MulEquiv.toMonoidHom (absoluteGaloisBaseChangeEquiv K E))

private theorem comap_apfSubgroup_stepEmbedding {u : ℝ} (hu : -1 ≤ u) :
    (apfSubgroup K F u).comap ρ =
      apfSubgroup E (stepEmbedding K E F hEF).fieldRange (apfPsi K E u) := by
  exact (congrArg (fun M ↦ (apfSubgroup K M u).comap ρ)
    (stepEmbedding_fieldRange K E F hEF)).symm.trans
      (comap_apfSubgroup_finiteBase K E (stepEmbedding K E F hEF) hu)

omit [IsCompleteDiscreteValuedField K] [PerfectField 𝓀[K]] [FiniteDimensional K E] in
private theorem comap_fixingSubgroup_stepEmbedding :
    F.fixingSubgroup.comap ρ = (stepEmbedding K E F hEF).fieldRange.fixingSubgroup := by
  exact (congrArg (fun M : IntermediateField K (SeparableClosure K) ↦
    M.fixingSubgroup.comap ρ) (stepEmbedding_fieldRange K E F hEF)).symm.trans
      (comap_fixingSubgroup_baseChangedEmbedding K E (stepEmbedding K E F hEF))

/-- Below the transformed elementary level, adjoining an elementary step leaves the
absolute upper product unchanged. -/
theorem apfSubgroup_eq_of_isElementary {i u : ℝ}
    (h : IsElementary E (IntermediateField.extendScalars hEF) i)
    (hu : -1 ≤ u) (hui : apfPsi K E u ≤ i) :
    apfSubgroup K F u = apfSubgroup K E u := by
  let j := stepEmbedding K E F hEF
  have hcomap : (apfSubgroup K F u).comap ρ = ⊤ := by
    rw [comap_apfSubgroup_stepEmbedding K E F hEF hu]
    exact h.apfSubgroup_eq_top_of_le j (IsAPF.apfPsi_mem_Ici K E hu) hui
  have hrange : E.fixingSubgroup ≤ apfSubgroup K F u := by
    rw [← absoluteGaloisBaseChange_range K E]
    rintro g ⟨σ, rfl⟩
    have hσ : σ ∈ (apfSubgroup K F u).comap ρ := by rw [hcomap]; trivial
    exact hσ
  exact le_antisymm (sup_le_sup_right (IntermediateField.fixingSubgroup_le hEF) _)
    (sup_le hrange le_sup_right)

/-- Above an elementary step's level, an upper group already fixing the preceding field
also fixes the new field. -/
theorem apfSubgroup_eq_fixingSubgroup_of_isElementary {i u : ℝ}
    (h : IsElementary E (IntermediateField.extendScalars hEF) i)
    (hu : -1 ≤ u) (hiu : i < apfPsi K E u)
    (hU : absoluteUpperRamificationGroup K u ≤ E.fixingSubgroup) :
    apfSubgroup K F u = F.fixingSubgroup := by
  let j := stepEmbedding K E F hEF
  have hcomap : (apfSubgroup K F u).comap ρ = F.fixingSubgroup.comap ρ := by
    rw [comap_apfSubgroup_stepEmbedding K E F hEF hu,
      comap_fixingSubgroup_stepEmbedding K E F hEF]
    exact h.apfSubgroup_eq_fixingSubgroup j _ hiu
  have hle : apfSubgroup K F u ≤ (ρ).range := by
    rw [absoluteGaloisBaseChange_range K E]
    exact sup_le (IntermediateField.fixingSubgroup_le hEF) hU
  have hfix : F.fixingSubgroup ≤ (ρ).range := by
    rw [absoluteGaloisBaseChange_range K E]
    exact IntermediateField.fixingSubgroup_le hEF
  have heq := congrArg (Subgroup.map ρ) hcomap
  simpa only [Subgroup.map_comap_eq_self hle, Subgroup.map_comap_eq_self hfix] using heq

/-- The inverse Herbrand functions agree up to the transformed elementary level. -/
theorem apfPsi_eq_of_isElementary {i u : ℝ}
    (h : IsElementary E (IntermediateField.extendScalars hEF) i)
    (hui : apfPsi K E u ≤ i) : apfPsi K F u = apfPsi K E u := by
  by_cases hu : u ≤ 0
  · rw [apfPsi_of_nonpos K F hu, apfPsi_of_nonpos K E hu]
  · have hu := (lt_of_not_ge hu).le
    rw [apfPsi_eq_integral_index K F hu, apfPsi_eq_integral_index K E hu]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hu]
    intro v hv
    change (apfIndex K F v : ℝ) = (apfIndex K E v : ℝ)
    apply congrArg (fun n : ℕ ↦ (n : ℝ))
    rw [apfIndex_eq_embedding K F F.val, apfIndex_eq_embedding K E E.val]
    simp only [IntermediateField.fieldRange_val, apfInertiaIndex,
      apfInertiaSubgroup_eq_inf K _ v hv.1]
    rw [apfSubgroup_eq_of_isElementary K E F hEF h (by linarith [hv.1])
      (((IsAPF.strictMono_apfPsi K E).monotone hv.2).trans hui)]

variable [FiniteDimensional K F]

/-- Adjoining an elementary extension does not change the forward Herbrand function at
its elementary level. -/
theorem apfPhi_eq_of_isElementary {i : ℝ}
    (h : IsElementary E (IntermediateField.extendScalars hEF) i) :
    apfPhi K F i = apfPhi K E i := by
  apply (IsAPF.strictMono_apfPsi K F).injective
  rw [apfPsi_apfPhi, apfPsi_eq_of_isElementary K E F hEF h
    (by rw [apfPsi_apfPhi]), apfPsi_apfPhi]

/-- Increasing elementary levels give strictly increasing transformed levels in a tower. -/
theorem apfPhi_lt_of_isElementary {i j : ℝ}
    (h : IsElementary E (IntermediateField.extendScalars hEF) i) (hij : i < j) :
    apfPhi K E i < apfPhi K F j := by
  rw [← apfPhi_eq_of_isElementary K E F hEF h]
  exact strictMono_apfPhi K F hij

/-- A finite absolute product with one jump over the preceding fixing subgroup gives an
elementary extension over that preceding field. -/
theorem isElementary_of_apfSubgroup_profile {b : ℝ} (hb : 0 < b)
    (hfull : apfSubgroup K F b = E.fixingSubgroup)
    (htail : ∀ u : ℝ, b < u → apfSubgroup K F u = F.fixingSubgroup) :
    IsElementary E (IntermediateField.extendScalars hEF) (apfPsi K E b) := by
  let j := stepEmbedding K E F hEF
  let : FiniteDimensional K (IntermediateField.extendScalars hEF) :=
    inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E (IntermediateField.extendScalars hEF) :=
    Module.Finite.right K E (IntermediateField.extendScalars hEF)
  apply IsElementary.of_embedding j (hb.trans_le (IsAPF.le_apfPsi K E b))
  · refine (comap_apfSubgroup_stepEmbedding K E F hEF (show -1 ≤ b by linarith)).symm.trans ?_
    rw [hfull]
    apply top_unique
    intro g _
    change (ρ) g ∈ E.fixingSubgroup
    exact (absoluteGaloisBaseChangeEquiv K E g).property
  · intro v hv
    have hbu : b < apfPhi K E v := by
      apply (IsAPF.strictMono_apfPsi K E).lt_iff_lt.mp
      simpa only [apfPsi_apfPhi] using hv
    have hu : -1 ≤ apfPhi K E v := by linarith
    have hc := (comap_apfSubgroup_stepEmbedding K E F hEF hu).trans
      (congrArg (apfSubgroup E j.fieldRange) (apfPsi_apfPhi K E v))
    exact hc.symm.trans ((congrArg (Subgroup.comap ρ) (htail _ hbu)).trans
      (comap_fixingSubgroup_stepEmbedding K E F hEF))

omit [FiniteDimensional K F] in
/-- At a strict upper jump, the corresponding finite fixed field has relative first
ramification bound equal to the transformed jump, even when the upper extension is infinite. -/
theorem apfRamificationBound_eq_of_apfSubgroup_jump {b : ℝ} (hb : 0 < b)
    (hfull : apfSubgroup K F b = E.fixingSubgroup)
    (hjump : ∀ u : ℝ, b < u → apfSubgroup K F u ≠ E.fixingSubgroup) :
    apfRamificationBound E (IntermediateField.extendScalars hEF) =
      (apfPsi K E b : EReal) := by
  let j := stepEmbedding K E F hEF
  have hψ : 0 < apfPsi K E b := hb.trans_le (IsAPF.le_apfPsi K E b)
  have htop : apfSubgroup E j.fieldRange (apfPsi K E b) = ⊤ := by
    refine (comap_apfSubgroup_stepEmbedding K E F hEF (show -1 ≤ b by linarith)).symm.trans ?_
    rw [hfull]
    apply top_unique
    intro g _
    exact (absoluteGaloisBaseChangeEquiv K E g).property
  apply le_antisymm _
    (le_apfRamificationBound E (IntermediateField.extendScalars hEF) j (by linarith) htop)
  rw [apfRamificationBound_eq_embedding E (IntermediateField.extendScalars hEF) j]
  apply sSup_le
  rintro x ⟨v, _hv, hvtop, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  by_contra! hlt
  have hbu : b < apfPhi K E v := by
    apply (IsAPF.strictMono_apfPsi K E).lt_iff_lt.mp
    simpa only [apfPsi_apfPhi] using hlt
  have hu : -1 ≤ apfPhi K E v := by linarith
  have hc := (comap_apfSubgroup_stepEmbedding K E F hEF hu).trans
    ((congrArg (apfSubgroup E j.fieldRange) (apfPsi_apfPhi K E v)).trans hvtop)
  have hle : apfSubgroup K F (apfPhi K E v) ≤ E.fixingSubgroup := by
    rw [← hfull]
    exact apfSubgroup_antitoneOn K F (show -1 ≤ b by linarith) hu hbu.le
  have hge : E.fixingSubgroup ≤ apfSubgroup K F (apfPhi K E v) := by
    intro g hg
    have hr : g ∈ (ρ).range := (absoluteGaloisBaseChange_range K E).symm ▸ hg
    obtain ⟨σ, rfl⟩ := hr
    have hσ : σ ∈ (apfSubgroup K F (apfPhi K E v)).comap ρ := by rw [hc]; trivial
    exact hσ
  exact hjump _ hbu (le_antisymm hle hge)

omit [FiniteDimensional K F] in
/-- Once an absolute upper group fixes a finite field, its inertia index is the field's
ramification index. -/
theorem apfIndex_eq_ramificationIdx_of_absoluteUpper_le {u : ℝ} (hu : 0 ≤ u)
    (hU : absoluteUpperRamificationGroup K u ≤ E.fixingSubgroup) :
    apfIndex K E u =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K E)).ramificationIdx 𝒪[K] := by
  obtain ⟨v, hv, htail⟩ := exists_apfIndex_eq_spectral_ramificationIdx K E
  have hU' : absoluteUpperRamificationGroup K (max v u) ≤ E.fixingSubgroup :=
    (upperRamificationGroupInfinite_antitoneOn K (SeparableClosure K)
      (show -1 ≤ u by linarith)
      (show -1 ≤ max v u by linarith [le_max_right v u]) (le_max_right v u)).trans hU
  rw [← htail (max v u) (le_max_left v u)]
  rw [apfIndex_eq_embedding K E E.val, apfIndex_eq_embedding K E E.val]
  simp only [IntermediateField.fieldRange_val, apfInertiaIndex,
    apfInertiaSubgroup_eq_inf K _ u hu,
    apfInertiaSubgroup_eq_inf K _ (max v u) (hu.trans (le_max_right v u)), apfSubgroup,
    sup_eq_left.mpr hU, sup_eq_left.mpr hU']

omit [FiniteDimensional K F] in
/-- Above the last ramification of a finite field, the Herbrand integral has slope equal
to its ramification index; the left endpoint need not belong to the constant-index interval. -/
theorem apfPsi_sub_of_absoluteUpper_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hU : ∀ u : ℝ, a < u → absoluteUpperRamificationGroup K u ≤ E.fixingSubgroup) :
    apfPsi K E b - apfPsi K E a = (b - a) *
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K E)).ramificationIdx 𝒪[K] : ℝ) := by
  apply apfPsi_sub_apfPsi_of_apfIndex_eq K E ha hab
  intro u hu
  exact apfIndex_eq_ramificationIdx_of_absoluteUpper_le K E
    (ha.trans hu.1.le) (hU u hu.1)

end FontaineWintenberger
