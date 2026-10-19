/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Defs
public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField
public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.RamificationBound

/-!
# Finite stages of an APF extension

## Actual finite stages of an APF extension

The closed actual APF product has an actual finite fixed field. These stages
are increasing and cofinal. Restricting the inverse of an original separable
embedding gives genuine finite subfields of the original abstract extension.

## Countable cofinal finite intermediate fields of an APF extension

The genuine APF fixed fields at integer parameters pull back to a monotone
cofinal sequence in the original abstract extension. No finite-residue or
normality assumption is used.

## Cofinal growth of the actual relative first ramification bounds

The original finite-base closure homomorphism carries an actual stage
containment to a full relative APF product. Its actual Herbrand parameter
therefore bounds the extended first ramification bound from below. The
extended-real statement includes trivial finite steps.
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
theorem exists_finiteIntermediateField_map_eq_apfFiniteStage [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) {u : ℝ} (hu : -1 ≤ u) :
    ∃ E : FiniteIntermediateField K L, E.val.map j = apfFiniteStage K j.fieldRange u := by
  let A := apfFiniteStage K j.fieldRange u
  have : FiniteDimensional K A := finiteDimensional_apfFiniteStage K j.fieldRange hu
  let f : A →ₐ[K] L := j.equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion (apfFiniteStage_le K j.fieldRange u))
  let E : FiniteIntermediateField K L :=
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
theorem IsAPF.exists_finiteIntermediateField_ge_map_eq_apfFiniteStage [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) (D : FiniteIntermediateField K L) :
    ∃ (u : ℝ) (E : FiniteIntermediateField K L), 0 ≤ u ∧ D ≤ E ∧
      E.val.map j = apfFiniteStage K j.fieldRange u := by
  have : FiniteDimensional K (D.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap D.val j).toLinearEquiv
  have hD : D.val.map j ≤ j.fieldRange := by
    rintro z ⟨x, _, rfl⟩
    exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
  obtain ⟨u, hu, hstage⟩ := exists_le_apfFiniteStage K j.fieldRange (D.val.map j) hD
  obtain ⟨E, hE⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (by linarith : -1 ≤ u)
  refine ⟨u, E, hu, ?_, hE⟩
  intro x hx
  have hjx : j x ∈ apfFiniteStage K j.fieldRange u :=
    hstage u le_rfl ⟨x, hx, rfl⟩
  rw [← hE] at hjx
  obtain ⟨y, hy, he⟩ := hjx
  exact (j.injective he) ▸ hy

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual integer-parameter APF stages give a monotone cofinal
sequence of original finite fields, with exact original embedded images. -/
theorem IsAPF.exists_monotone_cofinal_finiteIntermediateFields_map [IsAPF K L]
    (j : L →ₐ[K] SeparableClosure K) :
    ∃ E : ℕ → FiniteIntermediateField K L, Monotone E ∧
      (∀ n : ℕ, (E n).val.map j = apfFiniteStage K j.fieldRange (n : ℝ)) ∧
      ∀ D : FiniteIntermediateField K L, ∃ n : ℕ, D ≤ E n := by
  choose E hE using fun n : ℕ =>
    exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 ≤ (n : ℝ))
  refine ⟨E, ?_, hE, ?_⟩
  · intro m n hmn x hx
    have hjx : j x ∈ apfFiniteStage K j.fieldRange (m : ℝ) := by
      rw [← hE m]
      exact ⟨x, hx, rfl⟩
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hstage := apfFiniteStage_mono K j.fieldRange
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : -1 ≤ (m : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 ≤ (n : ℝ)) hmn'
    have hxn := hstage hjx
    rw [← hE n] at hxn
    obtain ⟨y, hy, he⟩ := hxn
    exact (j.injective he) ▸ hy
  · intro D
    have : FiniteDimensional K (D.val.map j) :=
      Module.Finite.equiv (IntermediateField.equivMap D.val j).toLinearEquiv
    have hDL : D.val.map j ≤ j.fieldRange := by
      rintro x ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    obtain ⟨U, _hU, hUstage⟩ := exists_le_apfFiniteStage K j.fieldRange (D.val.map j) hDL
    refine ⟨Nat.ceil U, fun x hx => ?_⟩
    have hjx := hUstage (Nat.ceil U) (Nat.le_ceil U) ⟨x, hx, rfl⟩
    rw [← hE (Nat.ceil U)] at hjx
    obtain ⟨y, hy, he⟩ := hjx
    exact (j.injective he) ▸ hy

/-- Every original abstract separable APF extension has a countable
monotone cofinal sequence among all of its actual finite intermediate fields. -/
theorem IsAPF.exists_monotone_cofinal_finiteIntermediateFields [IsAPF K L] :
    ∃ E : ℕ → FiniteIntermediateField K L, Monotone E ∧ ∀ D : FiniteIntermediateField K L, ∃ n : ℕ,
        D ≤ E n := by
  obtain ⟨j⟩ := nonempty_separableClosure_embeddings K L
  obtain ⟨E, hmono, _hmap, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_finiteIntermediateFields_map K L j
  exact ⟨E, hmono, hcofinal⟩

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger.AbstractFiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsCompleteDiscreteValuedField M]
    [NormedAlgebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := M)).valuationSubring)]
    [Algebra M (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]
variable (N : Type*) [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable M N]

/-- Containment of the actual finite-base fixing range in the old APF
product gives an actual extended relative first bound at the original
finite-base Herbrand parameter. -/
theorem apfPsi_le_apfRamificationBound_of_range_le
    (i : N →ₐ[M] SeparableClosure M) {u : ℝ} (hu : 0 ≤ u)
    (h : (closureHom K M).range ≤ apfSubgroup K (embedding K M i).fieldRange u) :
    (apfPsi K M u : EReal) ≤ apfRamificationBound M N := by
  have hu' : -1 ≤ u := by linarith
  have htop : (apfSubgroup K (embedding K M i).fieldRange u).comap
      (closureHom K M) = ⊤ := by
    apply top_unique
    intro g _
    exact h ⟨g, rfl⟩
  rw [comap_apf K M i hu'] at htop
  exact le_apfRamificationBound M N i
    (IsAPF.apfPsi_mem_Ici K M hu') htop

end FontaineWintenberger.AbstractFiniteBase

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A genuine APF-stage containment gives the actual relative extended
first bound on the original finite fields and their canonical spectral norm. -/
theorem apfPsi_le_relativeFirstBound_of_apfFiniteStage_le
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F) (j : L →ₐ[K] SeparableClosure K)
    {u : ℝ} (hu : 0 ≤ u) (hstage : apfFiniteStage K j.fieldRange u ≤ E.val.map j) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
    (apfPsi K E.val u : EReal) ≤
      apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := normedAlgebra_residueField_perfectField K E.val
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  let jE := j.comp E.val.val
  let : Algebra E.val (SeparableClosure K) := jE.toRingHom.toAlgebra
  let : IsScalarTower K E.val (SeparableClosure K) := IsScalarTower.of_algHom jE
  let e := AbstractFiniteBase.closureEquiv K E.val
  let jF : F.val →ₐ[E.val] SeparableClosure K :=
    { (j.comp F.val.val).toRingHom with commutes' := fun _ => rfl }
  let i := e.symm.toAlgHom.comp jF
  have he : AbstractFiniteBase.embedding K E.val i = j.comp F.val.val := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply (jF x)
  have hr : (AbstractFiniteBase.closureHom K E.val).range = (E.val.map j).fixingSubgroup := by
    rw [AbstractFiniteBase.closureHom_range K E.val]
    have hjE : IsScalarTower.toAlgHom K E.val (SeparableClosure K) = jE := by
      ext x
      rfl
    rw [hjE, IntermediateField.fieldRange_comp_val]
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have hfix : (AbstractFiniteBase.closureHom K E.val).range ≤
      apfSubgroup K (AbstractFiniteBase.embedding K E.val i).fieldRange u := by
    rw [hr, he, IntermediateField.fieldRange_comp_val]
    exact ((IntermediateField.fixingSubgroup_le hstage).trans_eq
      (fixingSubgroup_apfFiniteStage K j.fieldRange u)).trans
        (sup_le_sup_right (IntermediateField.fixingSubgroup_le hFL) _)
  exact AbstractFiniteBase.apfPsi_le_apfRamificationBound_of_range_le K E.val F.val i hu hfix

/-- The actual relative first bounds become arbitrarily large on a genuine
finite-layer tail of the original abstract separable APF extension. Trivial
steps retain their extended bound `∞`. -/
theorem IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge [IsAPF K L] (c : ℝ) :
    ∃ T : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, T ≤ E → ∀ hEF : E ≤ F,
      letI := spectralNorm.nontriviallyNormedField K E.val
      letI := spectralNorm.normedAlgebra K E.val
      letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := E.val))
      letI := spectralNorm.completeSpace K E.val
      letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
      (c : EReal) ≤ apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let u := max c 0
  have hu : 0 ≤ u := le_max_right _ _
  obtain ⟨T, hT⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (by linarith : -1 ≤ u)
  refine ⟨T, fun E F hTE hEF ↦ ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  have hstage : apfFiniteStage K j.fieldRange u ≤ E.val.map j := by
    rw [← hT]
    exact IntermediateField.map_mono j hTE
  have hb := apfPsi_le_relativeFirstBound_of_apfFiniteStage_le K L E F hEF j hu hstage
  have hpsi : c ≤ apfPsi K E.val u :=
    (le_max_left c 0).trans (IsAPF.le_apfPsi K E.val u)
  exact (EReal.coe_le_coe_iff.mpr hpsi).trans hb

end FontaineWintenberger
