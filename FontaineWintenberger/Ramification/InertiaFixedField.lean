/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Nonnormal

/-!
# The original field fixed by inertia

The actual inertia fixed field is unramified over the base, and its
original residue inclusion into the top field is an isomorphism.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "B" => spectralIntegerRing K L
local notation "G" => L ≃ₐ[K] L
local notation "I" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0
local notation "U" => IntermediateField.fixedField I
local notation "A" => Valuation.valuationSubring
  (Valuation.comap (algebraMap U L) (spectralValuation K L))

/-- The actual field fixed by the original zero lower group has ramification
index one over the original base. -/
theorem inertia_fixedField_ramificationIdx :
    (IsLocalRing.maximalIdeal A).ramificationIdx R = 1 := by
  rw [fixedField_ramificationIdx_eq_relIndex K L I]
  simp

/-- The restricted inertia action has every original inertia element,
and hence its actual order is the top relative ramification index. -/
theorem inertia_fixedField_top_ramificationIdx :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Nat.card I := by
  rw [← fixedField_card_inertia K L I,
    card_lowerRamificationGroup_zero_subgroup]
  simp

/-- The original integer ring is totally ramified over the actual
inertia fixed-field integers. -/
theorem inertia_fixedField_top_ramificationIdx_eq_finrank :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank A B := by
  have := fixedField_integer_isGaloisGroup K L I
  rw [inertia_fixedField_top_ramificationIdx K L]
  exact IsGaloisGroup.card_eq_finrank' I A B

/-- The same relative index is the degree of the original field extension. -/
theorem inertia_fixedField_top_ramificationIdx_eq_field_finrank :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank U L := by
  rw [inertia_fixedField_top_ramificationIdx K L]
  exact IsGaloisGroup.card_eq_finrank I U L

/-- The actual residue inclusion from the actual inertia fixed field is onto. -/
theorem inertia_fixedField_residue_surjective :
    Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
  have := intermediate_spectral_isDiscreteValuationRing K L U
  have := fixedField_integer_moduleFinite K L I
  exact (ramificationIdx_eq_finrank_iff_residue_surjective A B).mp
    (inertia_fixedField_top_ramificationIdx_eq_finrank K L)

/-- The canonical residue map of the original inertia fixed field is an
actual residue-field isomorphism over the original base residue field. -/
def inertia_fixedField_residueEquiv :
    IsLocalRing.ResidueField A ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField B :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    ⟨(algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective,
      inertia_fixedField_residue_surjective K L⟩

@[simp]
theorem inertia_fixedField_residueEquiv_apply (x : IsLocalRing.ResidueField A) :
    inertia_fixedField_residueEquiv K L x =
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) x := rfl

end FontaineWintenberger
