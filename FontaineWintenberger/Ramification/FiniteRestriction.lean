/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.FieldEquiv
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Upper ramification under ordinary restriction in finite Galois towers

Each field keeps its own spectral integers. The canonical field-range
isomorphism identifies the ordinary restriction maps pointwise.
-/

@[expose] public section

namespace FontaineWintenberger

section Tower

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (F L : Type*) [Field F] [Field L] [Algebra K F] [Algebra K L]
    [Algebra F L] [IsScalarTower K F L] [IsGalois K F] [IsGalois K L]
    [FiniteDimensional K F] [FiniteDimensional K L]
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Ordinary restriction preserves actual upper groups in every finite Galois field tower. -/
theorem restrictNormalHom_map_upperRamificationGroup_tower (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).map
      (AlgEquiv.restrictNormalHom F) =
        upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
  let i := IsScalarTower.toAlgHom K F L
  let E := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  have : IsGalois K E := IsGalois.of_algEquiv e
  have hcomp : e.autCongr.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom F : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)) =
        AlgEquiv.restrictNormalHom E := by
    ext s x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    change algebraMap F L (s.restrictNormal F y) =
      algebraMap E L (s.restrictNormal E (e y))
    rw [AlgEquiv.restrictNormal_commutes]
    exact (AlgEquiv.restrictNormal_commutes s E (e y)).symm
  apply Subgroup.map_injective (f := e.autCongr.toMonoidHom) e.autCongr.injective
  rw [Subgroup.map_map, hcomp, restrictNormalHom_map_upperRamificationGroup K L E u hu,
    upperRamificationGroup_map_autCongr K e hu]

end Tower

section FiniteIntermediateFields

open CategoryTheory Opposite

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω]
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Mathlib's actual finite Galois transition maps preserve the actual upper groups. -/
theorem finGaloisGroupMap_map_upperRamificationGroup
    {A B : (FiniteGaloisIntermediateField K Ω)ᵒᵖ} (f : A ⟶ B)
    (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing K A.unop) (A.unop ≃ₐ[K] A.unop) u).map
      (finGaloisGroupMap f).hom.hom =
        upperRamificationGroup (R := spectralIntegerRing K B.unop) (B.unop ≃ₐ[K] B.unop) u := by
  let : Algebra B.unop A.unop :=
    RingHom.toAlgebra (Subsemiring.inclusion (leOfHom f.1))
  have : IsScalarTower K B.unop A.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact restrictNormalHom_map_upperRamificationGroup_tower K B.unop A.unop u hu

end FiniteIntermediateFields

end FontaineWintenberger
