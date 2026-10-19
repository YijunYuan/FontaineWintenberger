/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Upper.ResidueEquiv
public import FontaineWintenberger.Ramification.Lower.SpectralMaps

/-!
# Residue degrees of APF finite stages

The full zero-level APF index is the residue degree, retaining the
residue factor omitted from the inertia-relative APF index. The zero
stage therefore stabilizes residue degrees in the extension.

## Main results

* `apfSubgroup_index_zero_eq_residueDegree_of_finiteGalois`: The full zero index in a finite Galois
  overfield equals the residue degree of the intermediate field.
* `apfSubgroup_index_zero_eq_residueDegree`: The full zero APF index of any specified separable
  embedding is the residue degree of the finite separable extension.
* `apfSubgroup_zero_eq_of_apfFiniteStage_le`: Beyond the zero stage, the zero APF product is
  unchanged.
* `residueDegree_eq_zeroStage_of_apfFiniteStage_le`: The residue degree over K is constant beyond
  the finite zero stage of an APF extension.
* `spectralResidueInclusion_zeroStage_surjective`: The residue inclusion from the zero stage onto a
  finite stage above it is surjective.
* `spectralResidueInclusion_surjective_of_zeroStage_le`: Finite inclusions beyond the zero stage
  induce surjective residue maps, without normality of either field.
* `IsAPF.exists_finiteIntermediateField_residueDegree_stable`: In the abstract APF extension,
  residue degrees stabilize above a finite intermediate field pulled back from its zero stage.
* `IsAPF.exists_finiteIntermediateField_residueInclusion_surjective`: The abstract APF extension has
  a finite residue-stable tail: every inclusion on that tail induces a surjection on residues.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]


/-- The full zero index in a finite Galois overfield equals the
residue degree of the intermediate field. -/
theorem apfSubgroup_index_zero_eq_residueDegree_of_finiteGalois
    (Ω : Type*) [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (M : IntermediateField K Ω) (j : Ω →ₐ[K] SeparableClosure K) :
    (apfSubgroup K (j.comp M.val).fieldRange 0).index =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K M)) := by
  rw [apfSubgroup_fieldRange_index_eq_fixingSubgroup_sup_upper_index K Ω M j (by norm_num),
    upperRamificationGroup_zero, ← lowerRamificationGroup_zero,
    intermediate_spectral_zeroOrbitIndex_eq_residueDegree K Ω M]
  exact extensionValuationSubring_residueDegree_eq_spectral K M
    ((spectralValuation K Ω).comap (algebraMap M Ω))

/-- The full zero APF index of any specified separable embedding is the
residue degree of the finite separable extension. -/
theorem apfSubgroup_index_zero_eq_residueDegree
    (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (j : M →ₐ[K] SeparableClosure K) :
    (apfSubgroup K j.fieldRange 0).index =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K M)) := by
  let Ω := IntermediateField.normalClosure K M (SeparableClosure K)
  let i : M →ₐ[K] Ω :=
    j.codRestrict Ω.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let N := i.fieldRange
  let e : M ≃ₐ[K] N := i.equivFieldRange
  have : FiniteDimensional K N := Module.Finite.equiv e.toLinearEquiv
  have hr : (Ω.val.comp N.val).fieldRange = j.fieldRange := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := e.surjective y
      exact ⟨z, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, rfl⟩
  rw [← hr, apfSubgroup_index_zero_eq_residueDegree_of_finiteGalois K Ω N Ω.val,
    spectral_residueDegree_algEquiv K M e]

omit [PerfectField 𝓀[K]] in
/-- Beyond the zero stage, the zero APF product is unchanged. -/
theorem apfSubgroup_zero_eq_of_apfFiniteStage_le
    (L E : IntermediateField K (SeparableClosure K))
    (hEL : E ≤ L) (hstage : apfFiniteStage K L 0 ≤ E) :
    apfSubgroup K E 0 = apfSubgroup K L 0 := by
  apply le_antisymm
  · exact sup_le
      ((IntermediateField.fixingSubgroup_le hstage).trans_eq
        (fixingSubgroup_apfFiniteStage K L 0)) le_sup_right
  · exact sup_le ((IntermediateField.fixingSubgroup_le hEL).trans le_sup_left) le_sup_right

/-- The residue degree over K is constant beyond the finite
zero stage of an APF extension. -/
theorem residueDegree_eq_zeroStage_of_apfFiniteStage_le
    (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (hEL : E ≤ L) (hstage : apfFiniteStage K L 0 ≤ E) :
    Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K E)) =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField (spectralIntegerRing K (apfFiniteStage K L 0))) := by
  have := finiteDimensional_apfFiniteStage K L (by norm_num : -1 ≤ (0 : ℝ))
  rw [← apfSubgroup_index_zero_eq_residueDegree K E E.val,
    ← apfSubgroup_index_zero_eq_residueDegree K (apfFiniteStage K L 0)
      (apfFiniteStage K L 0).val]
  simp only [IntermediateField.fieldRange_val]
  rw [apfSubgroup_zero_eq_of_apfFiniteStage_le K L E hEL hstage,
    apfSubgroup_zero_eq_of_apfFiniteStage_le K L (apfFiniteStage K L 0)
      (apfFiniteStage_le K L 0) le_rfl]

/-- The residue inclusion from the zero stage onto a finite stage
above it is surjective. The tower uses its residue map. -/
theorem spectralResidueInclusion_zeroStage_surjective
    (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (hEL : E ≤ L) (hstage : apfFiniteStage K L 0 ≤ E) :
    Function.Surjective (spectralResidueInclusion K (IntermediateField.inclusion hstage)) := by
  have := finiteDimensional_apfFiniteStage K L (by norm_num : -1 ≤ (0 : ℝ))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (residueDegree_eq_zeroStage_of_apfFiniteStage_le K L E hEL hstage).symm
    (f := (spectralResidueInclusion K (IntermediateField.inclusion hstage)).toLinearMap)).mp
      (spectralResidueInclusion K (IntermediateField.inclusion hstage)).injective

/-- Finite inclusions beyond the zero stage induce surjective
residue maps, without normality of either field. -/
theorem spectralResidueInclusion_surjective_of_zeroStage_le
    (L : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K L]
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F]
    (hFL : F ≤ L) (hstage : apfFiniteStage K L 0 ≤ E) (hEF : E ≤ F) :
    Function.Surjective (spectralResidueInclusion K (IntermediateField.inclusion hEF)) := by
  have hdim := (residueDegree_eq_zeroStage_of_apfFiniteStage_le K L E
    (hEF.trans hFL) hstage).trans
      (residueDegree_eq_zeroStage_of_apfFiniteStage_le K L F hFL (hstage.trans hEF)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (spectralResidueInclusion K (IntermediateField.inclusion hEF)).toLinearMap)).mp
      (spectralResidueInclusion K (IntermediateField.inclusion hEF)).injective

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- In the abstract APF extension, residue degrees stabilize above
a finite intermediate field pulled back from its zero stage. -/
theorem IsAPF.exists_finiteIntermediateField_residueDegree_stable [IsAPF K L] :
    ∃ E₀ : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, E₀ ≤ F →
      Module.finrank (IsLocalRing.ResidueField 𝒪[K])
          (IsLocalRing.ResidueField (spectralIntegerRing K F.val)) =
        Module.finrank (IsLocalRing.ResidueField 𝒪[K])
          (IsLocalRing.ResidueField (spectralIntegerRing K E₀.val)) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨E₀, hE₀⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (by norm_num : -1 ≤ (0 : ℝ))
  refine ⟨E₀, fun F hF => ?_⟩
  have : FiniteDimensional K (F.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap F.val j).toLinearEquiv
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have hstage : apfFiniteStage K j.fieldRange 0 ≤ F.val.map j := by
    rw [← hE₀]
    exact IntermediateField.map_mono j hF
  have hd := residueDegree_eq_zeroStage_of_apfFiniteStage_le K j.fieldRange
    (F.val.map j) hFL hstage
  rw [← hE₀, spectral_residueDegree_algEquiv K F.val (IntermediateField.equivMap F.val j),
    spectral_residueDegree_algEquiv K E₀.val (IntermediateField.equivMap E₀.val j)] at hd
  exact hd

/-- The abstract APF extension has a finite residue-stable
tail: every inclusion on that tail induces a surjection on residues. -/
theorem IsAPF.exists_finiteIntermediateField_residueInclusion_surjective [IsAPF K L] :
    ∃ E₀ : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, E₀ ≤ E → ∀ hEF : E ≤ F,
      Function.Surjective
        (spectralResidueInclusion K (IntermediateField.inclusion hEF)) := by
  obtain ⟨E₀, hE₀⟩ := IsAPF.exists_finiteIntermediateField_residueDegree_stable K L
  refine ⟨E₀, fun E F hE hEF => ?_⟩
  have hdim := (hE₀ E hE).trans (hE₀ F (hE.trans hEF)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (spectralResidueInclusion K (IntermediateField.inclusion hEF)).toLinearMap)).mp
      (spectralResidueInclusion K (IntermediateField.inclusion hEF)).injective

end FontaineWintenberger
