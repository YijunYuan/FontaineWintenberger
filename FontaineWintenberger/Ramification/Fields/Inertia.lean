/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Fields.Nonnormal

/-!
# The field fixed by inertia

The inertia fixed field is unramified over the base, and its
residue inclusion into the top field is an isomorphism.

## Main definitions

* `inertiaFixedFieldResidueEquiv`: The canonical residue map of the inertia fixed field is an
  residue-field isomorphism over the base residue field.

## Main results

* `inertia_fixedField_ramificationIdx`: The field fixed by the zero lower group has ramification
  index one over the base.
* `inertia_fixedField_top_ramificationIdx`: The restricted inertia action has every inertia element,
  and hence its order is the top relative ramification index.
* `inertia_fixedField_top_ramificationIdx_eq_finrank`: The integer ring is totally ramified over the
  inertia fixed-field integers.
* `inertia_fixedField_top_ramificationIdx_eq_field_finrank`: The same relative index is the degree
  of the field extension.
* `inertia_fixedField_residue_surjective`: The residue inclusion from the inertia fixed field is
  onto.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField 𝓀[K]]

local notation "B" => spectralIntegerRing K L
local notation "G" => L ≃ₐ[K] L
local notation "I" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0
local notation "U" => IntermediateField.fixedField I
local notation "A" => Valuation.valuationSubring
  (Valuation.comap (algebraMap U L) (spectralValuation K L))

/-- The field fixed by the zero lower group has ramification
index one over the base. -/
theorem inertia_fixedField_ramificationIdx :
    (IsLocalRing.maximalIdeal A).ramificationIdx 𝒪[K] = 1 := by
  rw [fixedField_ramificationIdx_eq_relIndex K L I]
  simp

/-- The restricted inertia action has every inertia element,
and hence its order is the top relative ramification index. -/
theorem inertia_fixedField_top_ramificationIdx :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Nat.card I := by
  rw [← fixedField_card_inertia K L I,
    card_lowerRamificationGroup_zero_subgroup]
  simp

/-- The integer ring is totally ramified over the
inertia fixed-field integers. -/
theorem inertia_fixedField_top_ramificationIdx_eq_finrank :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank A B := by
  have := fixedField_integer_isGaloisGroup K L I
  rw [inertia_fixedField_top_ramificationIdx K L]
  exact IsGaloisGroup.card_eq_finrank' I A B

/-- The same relative index is the degree of the field extension. -/
theorem inertia_fixedField_top_ramificationIdx_eq_field_finrank :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank U L := by
  rw [inertia_fixedField_top_ramificationIdx K L]
  exact IsGaloisGroup.card_eq_finrank I U L

/-- The residue inclusion from the inertia fixed field is onto. -/
theorem inertia_fixedField_residue_surjective :
    Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
  have := intermediate_spectral_isDiscreteValuationRing K L U
  have := fixedField_integer_moduleFinite K L I
  exact (ramificationIdx_eq_finrank_iff_residue_surjective A B).mp
    (inertia_fixedField_top_ramificationIdx_eq_finrank K L)

/-- The canonical residue map of the inertia fixed field is an
residue-field isomorphism over the base residue field. -/
def inertiaFixedFieldResidueEquiv :
    IsLocalRing.ResidueField A ≃ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField B :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom (IsLocalRing.ResidueField 𝒪[K])
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    ⟨(algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective,
      inertia_fixedField_residue_surjective K L⟩

@[simp]
theorem inertia_fixedField_residueEquiv_apply (x : IsLocalRing.ResidueField A) :
    inertiaFixedFieldResidueEquiv K L x =
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) x := rfl

end FontaineWintenberger
