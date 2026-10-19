/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.FieldOfNorms.Basic.Defs
public import FontaineWintenberger.FieldOfNorms.Estimates.Integral
public import FontaineWintenberger.Ramification.Norm.Valuation
public import FontaineWintenberger.APF.Tower.Tame

/-!
# The valuation of the field of norms

## The stable valuation on the multiplicative field of norms

Residue inclusions on an APF finite tail are bijective, so field
norms preserve their normalized valuations. The multiplicative limit
therefore has a single coordinate-independent normalized valuation.

## The normalization above the maximal unramified field

The existing stable valuation is computed at every finite field above
the maximal unramified subfield, as in Wintenberger, paragraph 2.1.2.

## Main definitions

* `FieldOfNorms.coordinateValuation`: Evaluate the multiplicative limit and then use the normalized
  valuation of that finite field.
* `FieldOfNorms.valuation`: The stable normalized multiplicative valuation on the single field of
  norms carrier.

## Main results

* `normalizedValuation_norm_of_residueInclusion_surjective`: Field norms preserve normalized
  valuations whenever their residue inclusion is surjective.
* `FieldOfNorms.exists_coordinateValuation_stable`: The normalized coordinate valuations agree on an
  APF finite tail.
* `FieldOfNorms.exists_valuation_eq_coordinateValuation`: The same normalized valuation is computed
  by every sufficiently large finite coordinate.
* `FieldOfNorms.valuation_eq_zero_iff`: The stable normalized valuation detects zero on the field of
  norms.
* `FieldOfNorms.valuation_eq_coordinate_of_maximalUnramified_le`: The same stable valuation is
  computed at every finite intermediate field above the maximal unramified subfield, not merely
  above a chosen stable witness.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

namespace FiniteIntermediateField


/-- Field norms preserve normalized valuations whenever their
residue inclusion is surjective. No normality is required. -/
theorem normalizedValuation_norm_of_residueInclusion_surjective
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (hs : Function.Surjective
      (spectralResidueInclusion K (IntermediateField.inclusion hEF))) (x : F.val) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
        (norm E F hEF x) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation F.val x := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite 𝒪[K] _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have hf : Module.finrank (IsLocalRing.ResidueField (spectralIntegerRing K E.val))
      (IsLocalRing.ResidueField (spectralIntegerRing K F.val)) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨(spectralResidueInclusion K
        (IntermediateField.inclusion hEF)).injective, hs⟩
  have hv := normalizedValuation_norm (spectralIntegerRing K E.val)
    (spectralIntegerRing K F.val) E.val F.val x
  rw [local_inertiaDeg_eq_finrank_residueField, hf, pow_one] at hv
  convert hv using 1
  congr 1

end FiniteIntermediateField

/-- Evaluate the multiplicative limit and then use the
normalized valuation of that finite field. -/
def FieldOfNorms.coordinateValuation (E : FiniteIntermediateField K L) : FieldOfNorms K L →*₀
    WithZero (Multiplicative
    ℤ) :=
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  v.toMonoidWithZeroHom.comp (FieldOfNorms.coord K L E)

variable [PerfectField 𝓀[K]]

/-- The normalized coordinate valuations agree on an APF finite tail. -/
theorem FieldOfNorms.exists_coordinateValuation_stable [IsAPF K L] :
    ∃ E₀ : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, E₀ ≤ E → E₀ ≤ F →
      ∀ x : FieldOfNorms K L,
        FieldOfNorms.coordinateValuation K L E x = FieldOfNorms.coordinateValuation K L F x := by
  obtain ⟨E₀, hE₀⟩ := IsAPF.exists_finiteIntermediateField_residueInclusion_surjective K L
  refine ⟨E₀, fun E F hE hF x => ?_⟩
  let G := FiniteIntermediateField.sup E F
  have hEG : E ≤ G := FiniteIntermediateField.le_sup_left E F
  have hFG : F ≤ G := FiniteIntermediateField.le_sup_right E F
  have hvE := FiniteIntermediateField.normalizedValuation_norm_of_residueInclusion_surjective K L E
      G hEG
    (hE₀ E G hE hEG) (FieldOfNorms.coord K L G x)
  have hvF := FiniteIntermediateField.normalizedValuation_norm_of_residueInclusion_surjective K L F
      G hFG
    (hE₀ F G hF hFG) (FieldOfNorms.coord K L G x)
  rw [FieldOfNorms.coord_norm] at hvE hvF
  exact hvE.trans hvF.symm

/-- The stable normalized multiplicative valuation on the single
field of norms carrier. APF supplies and proves the finite stable tail. -/
def FieldOfNorms.valuation [IsAPF K L] : FieldOfNorms K L →*₀ WithZero (Multiplicative ℤ) :=
  FieldOfNorms.coordinateValuation K L
    (FieldOfNorms.exists_coordinateValuation_stable K L).choose

/-- The same normalized valuation is computed by every sufficiently large
finite coordinate. -/
theorem FieldOfNorms.exists_valuation_eq_coordinateValuation [IsAPF K L] :
    ∃ E₀ : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, E₀ ≤ E → ∀ x :
        FieldOfNorms K L,
      FieldOfNorms.valuation K L x = FieldOfNorms.coordinateValuation K L E x := by
  let hex := FieldOfNorms.exists_coordinateValuation_stable K L
  exact ⟨hex.choose, fun E hE x => hex.choose_spec hex.choose E le_rfl hE x⟩

/-- The stable normalized valuation detects zero on the field of norms. -/
@[simp]
theorem FieldOfNorms.valuation_eq_zero_iff [IsAPF K L] (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L x = 0 ↔ x = 0 := by
  simp [FieldOfNorms.valuation, FieldOfNorms.coordinateValuation]

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The same stable valuation is computed at every finite intermediate field above
the maximal unramified subfield, not merely above a chosen stable witness. -/
theorem FieldOfNorms.valuation_eq_coordinate_of_maximalUnramified_le [IsAPF K L]
    (E : FiniteIntermediateField K L) (hE : apfMaximalUnramified K L ≤ E) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L x = FieldOfNorms.coordinateValuation K L E x := by
  obtain ⟨D, hD⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  let F := FiniteIntermediateField.sup D E
  have hEF : E ≤ F := FiniteIntermediateField.le_sup_right D E
  have hs := spectralResidueInclusion_surjective_of_apfMaximalUnramified_le
    K L E F hE hEF
  have hv := FiniteIntermediateField.normalizedValuation_norm_of_residueInclusion_surjective
    K L E F hEF hs (FieldOfNorms.coord K L F x)
  rw [FieldOfNorms.coord_norm] at hv
  exact (hD F (FiniteIntermediateField.le_sup_left D E) x).trans hv.symm

end FontaineWintenberger
