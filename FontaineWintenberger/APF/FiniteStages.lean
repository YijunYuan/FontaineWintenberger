/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Abstract
public import FontaineWintenberger.APF.CofinalBase
public import FontaineWintenberger.FieldOfNorms.Multiplicative

/-!
# Actual finite stages of an APF extension

The closed actual APF product has an actual finite fixed field. These stages
are increasing and cofinal. Restricting the inverse of an original separable
embedding gives genuine finite subfields of the original abstract extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]


/-- Absolute upper groups eventually fix every actual finite subfield. -/
theorem exists_absoluteUpper_le_fixingSubgroup_of_finite
    (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M] :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      absoluteUpperRamificationGroup K u ≤ M.fixingSubgroup := by
  let E := finiteGaloisNormalClosure K M
  obtain ⟨U, hU⟩ := upperRamificationGroup_eventually_eq_bot
    (R := spectralIntegerRing K E) (E ≃ₐ[K] E)
  refine ⟨max U 0, le_max_right _ _, fun u hu => ?_⟩
  apply le_trans ?_ (IntermediateField.fixingSubgroup_le (le_finiteGaloisNormalClosure K M))
  rw [← E.toIntermediateField.restrictNormalHom_ker]
  intro g hg
  have hx := (mem_upperRamificationGroupInfinite K (SeparableClosure K) u g).mp hg E
  rw [hU u ((le_max_left _ _).trans hu)] at hx
  exact Subgroup.mem_bot.mp hx

/-- The actual fixed field of the actual APF product. -/
def apfFiniteStage (L : IntermediateField K (SeparableClosure K)) (u : ℝ) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField (apfSubgroup K L u)

/-- Closedness gives the exact fixing subgroup, without a finiteness shortcut. -/
theorem fixingSubgroup_apfFiniteStage (L : IntermediateField K (SeparableClosure K)) (u : ℝ) :
    (apfFiniteStage K L u).fixingSubgroup = apfSubgroup K L u :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨apfSubgroup K L u, isClosed_apfSubgroup K L u⟩

/-- Each actual stage lies inside the original separable subextension. -/
theorem apfFiniteStage_le (L : IntermediateField K (SeparableClosure K)) (u : ℝ) :
    apfFiniteStage K L u ≤ L :=
  (IntermediateField.fixedField_le (show L.fixingSubgroup ≤ apfSubgroup K L u from
    le_sup_left)).trans_eq (InfiniteGalois.fixedField_fixingSubgroup L)

/-- APF openness proves genuine finite degree of every actual stage. -/
theorem finiteDimensional_apfFiniteStage (L : IntermediateField K (SeparableClosure K))
    [IsAPFSubextension K L] {u : ℝ} (hu : -1 ≤ u) :
    FiniteDimensional K (apfFiniteStage K L u) := by
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [fixingSubgroup_apfFiniteStage]
  exact IsAPFSubextension.isOpen_apfSubgroup u hu

/-- The actual finite-stage fields increase with the upper parameter. -/
theorem apfFiniteStage_mono (L : IntermediateField K (SeparableClosure K))
    {u v : ℝ} (hu : -1 ≤ u) (hv : -1 ≤ v) (huv : u ≤ v) :
    apfFiniteStage K L u ≤ apfFiniteStage K L v :=
  IntermediateField.fixedField_le (apfSubgroup_antitoneOn K L hu hv huv)

/-- Every actual finite subfield occurs in a genuine stage. -/
theorem exists_le_apfFiniteStage (L M : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K M] (hML : M ≤ L) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → M ≤ apfFiniteStage K L u := by
  obtain ⟨U, hU, hfix⟩ := exists_absoluteUpper_le_fixingSubgroup_of_finite K M
  refine ⟨U, hU, fun u hu => ?_⟩
  have hprod : apfSubgroup K L u ≤ M.fixingSubgroup :=
    sup_le (IntermediateField.fixingSubgroup_le hML) (hfix u hu)
  exact (InfiniteGalois.fixedField_fixingSubgroup M).symm.trans_le
    (IntermediateField.fixedField_le hprod)

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual stage pulls back to a finite intermediate field of the
original abstract L, with a proved equality of its original embedded image. -/
theorem exists_finiteLayer_map_eq_apfFiniteStage [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    ∃ E : FiniteLayer K L, E.val.map j = apfFiniteStage K j.fieldRange u := by
  let A := apfFiniteStage K j.fieldRange u
  have : FiniteDimensional K A := finiteDimensional_apfFiniteStage K j.fieldRange hu
  let f : A →ₐ[K] L := j.equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion (apfFiniteStage_le K j.fieldRange u))
  let E : FiniteLayer K L :=
    ⟨f.fieldRange, Module.Finite.equiv f.equivFieldRange.toLinearEquiv⟩
  refine ⟨E, ?_⟩
  change f.fieldRange.map j = A
  rw [AlgHom.map_fieldRange]
  have he : j.comp f = A.val := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun z : j.fieldRange => (z : SeparableClosure K))
      (j.equivFieldRange.apply_symm_apply
        (IntermediateField.inclusion (apfFiniteStage_le K j.fieldRange u) x))
  rw [he, IntermediateField.fieldRange_val]

/-- The actual pulled-back stages are cofinal among finite subfields of
an arbitrary original abstract separable APF extension. -/
theorem IsAPF.exists_finiteLayer_ge_map_eq_apfFiniteStage [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) (D : FiniteLayer K L) :
    ∃ (u : ℝ) (E : FiniteLayer K L), 0 ≤ u ∧ D ≤ E ∧
      E.val.map j = apfFiniteStage K j.fieldRange u := by
  have : FiniteDimensional K (D.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap D.val j).toLinearEquiv
  have hD : D.val.map j ≤ j.fieldRange := by
    rintro z ⟨x, _, rfl⟩
    exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
  obtain ⟨u, hu, hstage⟩ := exists_le_apfFiniteStage K j.fieldRange (D.val.map j) hD
  obtain ⟨E, hE⟩ := exists_finiteLayer_map_eq_apfFiniteStage K L j
    (by linarith : -1 ≤ u)
  refine ⟨u, E, hu, ?_, hE⟩
  intro x hx
  have hjx : j x ∈ apfFiniteStage K j.fieldRange u :=
    hstage u le_rfl ⟨x, hx, rfl⟩
  rw [← hE] at hjx
  obtain ⟨y, hy, he⟩ := hjx
  exact (j.injective he) ▸ hy

end FontaineWintenberger
