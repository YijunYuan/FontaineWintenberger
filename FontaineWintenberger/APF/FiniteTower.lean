/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteBaseChange

/-!
# Finite upper base change for an abstract embedded base

The scalar tower and its actual field image are identified by the canonical
surjective scalar-change equivalence. The own-ring actions are preserved.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

noncomputable local instance : NontriviallyNormedField E :=
  spectralNorm.nontriviallyNormedField K E
noncomputable local instance : NormedAlgebra K E := spectralNorm.normedAlgebra K E
local instance : IsUltrametricDist E :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))

variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M]
    [Algebra M E] [IsScalarTower K M E]

local instance : FiniteDimensional M E := Module.Finite.right K M E

local instance : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.tower_top (K := K) M

noncomputable local instance : NormedAlgebra M E := spectralNorm.normedAlgebra' K M E

local notation "S₀" => AlgHom.fieldRange (IsScalarTower.toAlgHom K M E)
local notation "e₀" => AlgHom.equivFieldRange (IsScalarTower.toAlgHom K M E)

noncomputable local instance : Algebra M S₀ := (e₀).toAlgHom.toRingHom.toAlgebra
local instance : IsScalarTower K M S₀ := IsScalarTower.of_algHom (e₀).toAlgHom
local instance : IsScalarTower M S₀ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance : FiniteDimensional S₀ E := Module.Finite.right K S₀ E
local instance : Algebra.IsAlgebraic S₀ E := Algebra.IsAlgebraic.tower_top (K := K) S₀
local instance : CompleteSpace S₀ := IntermediateField.completeSpace_of_finiteDimensional S₀

noncomputable local instance :
    MulSemiringAction (E ≃ₐ[S₀] E) (spectralIntegerRing S₀ E) :=
  spectralIntegerRing_galoisAction S₀ E

/-- Changing from the abstract scalar field to its actual image preserves automorphisms. -/
noncomputable def finiteTower_autEquivImage : (E ≃ₐ[M] E) ≃* (E ≃ₐ[S₀] E) :=
  AlgEquiv.extendScalarsHomOfSurjective (R := M) (S := S₀) (A := E) (e₀).surjective

/-- The own spectral constructions over an embedded field and its image agree as subrings. -/
theorem finiteTower_spectralIntegerRing_eq :
    spectralIntegerRing M E = spectralIntegerRing S₀ E :=
  (spectralIntegerRing_eq_normedUnitBall M E).trans
    (spectralIntegerRing_eq_normedUnitBall S₀ E).symm

/-- The actual field identity gives the integer-ring equivalence for scalar change. -/
noncomputable def finiteTower_spectralIntegerRingEquiv :
    spectralIntegerRing M E ≃+* spectralIntegerRing S₀ E :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (finiteTower_spectralIntegerRing_eq K E M))

/-- Scalar change and integer-ring identification preserve the actual field action. -/
theorem finiteTower_spectralIntegerRingEquiv_smul (g : E ≃ₐ[M] E)
    (x : spectralIntegerRing M E) :
    finiteTower_spectralIntegerRingEquiv K E M (g • x) =
      finiteTower_autEquivImage K E M g • finiteTower_spectralIntegerRingEquiv K E M x := by
  apply Subtype.ext
  rfl


local instance : IsDiscreteValuationRing (spectralIntegerRing M E) := by
  rw [spectralIntegerRing_eq_normedUnitBall M E,
    ← spectralIntegerRing_eq_normedUnitBall K E]
  infer_instance

local instance : IsDiscreteValuationRing (spectralIntegerRing S₀ E) := by
  rw [spectralIntegerRing_eq_normedUnitBall S₀ E,
    ← spectralIntegerRing_eq_normedUnitBall K E]
  infer_instance

/-- Scalar change transports the actual own-ring upper group to the image-base upper group. -/
theorem finiteTower_upper_map_autEquivImage {v : ℝ} (hv : -1 ≤ v) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E) v).map
        (finiteTower_autEquivImage K E M).toMonoidHom =
      upperRamificationGroup (R := spectralIntegerRing S₀ E) (E ≃ₐ[S₀] E) v :=
  upperRamificationGroup_map_equivariant
    (finiteTower_spectralIntegerRingEquiv K E M) (finiteTower_autEquivImage K E M)
    (finiteTower_spectralIntegerRingEquiv_smul K E M) hv

omit [IsCompleteDiscreteValuedField K] [IsUltrametricDist M] [CompleteSpace M]
     in
/-- The canonical image-base automorphism equivalence restricts to the original field map. -/
theorem finiteTower_fixingSubtype_comp :
    (S₀).fixingSubgroup.subtype.comp
        ((S₀).fixingSubgroupEquiv.symm.toMonoidHom.comp
          (finiteTower_autEquivImage K E M).toMonoidHom) =
      AlgEquiv.restrictScalarsHom K (S := M) (A := E) := by
  ext g x
  rfl

omit [IsCompleteDiscreteValuedField K] [IsUltrametricDist M] [CompleteSpace M]
     in
/-- The restriction-of-scalars image is the actual subgroup fixing the embedded scalar field. -/
theorem finiteTower_range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom K (S := M) (A := E)).range = (S₀).fixingSubgroup := by
  rw [← finiteTower_fixingSubtype_comp K E M, MonoidHom.range_comp]
  have hs : Function.Surjective
      ((S₀).fixingSubgroupEquiv.symm.toMonoidHom.comp
        (finiteTower_autEquivImage K E M).toMonoidHom) :=
    (S₀).fixingSubgroupEquiv.symm.surjective.comp
      (finiteTower_autEquivImage K E M).surjective
  rw [MonoidHom.range_eq_top.mpr hs, Subgroup.map_top, Subgroup.range_subtype]

variable [FiniteDimensional K M] [Algebra.IsSeparable K M]

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

/-- Finite base change for the abstract embedded base, mapped to its actual fixing subgroup. -/
theorem finiteTower_upper_map_restrictScalars {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
      (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) =
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u ⊓
        (S₀).fixingSubgroup := by
  have hpsi : apfPsi K M u = apfPsi K S₀ u := apfPsi_algEquiv K M e₀ u
  have hnonneg : -1 ≤ apfPsi K M u :=
    IsAPF.apfPsi_mem_Ici K M hu
  rw [← finiteTower_fixingSubtype_comp K E M, ← Subgroup.map_map,
    ← Subgroup.map_map, finiteTower_upper_map_autEquivImage K E M hnonneg, hpsi,
    finiteBase_upperRamificationGroup K E S₀ hu, Subgroup.map_map]
  have hc : ((S₀).fixingSubgroup.subtype.comp
      (S₀).fixingSubgroupEquiv.symm.toMonoidHom).comp
        (S₀).fixingSubgroupEquiv.toMonoidHom = (S₀).fixingSubgroup.subtype := by
    ext g x
    rfl
  rw [Subgroup.map_map, hc, Subgroup.subgroupOf_map_subtype]

/-- The upper-group image is the intersection with the actual restriction-of-scalars range. -/
theorem finiteTower_upper_map_restrictScalars_range {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
      (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) =
      (AlgEquiv.restrictScalarsHom K (S := M) (A := E)).range ⊓
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  rw [finiteTower_range_restrictScalarsHom K E M,
    finiteTower_upper_map_restrictScalars K E M hu, inf_comm]

/-- Membership in an own-ring upper group is detected by the actual scalar restriction. -/
theorem finiteTower_mem_upper_iff_restrictScalars {u : ℝ} (hu : -1 ≤ u)
    (g : E ≃ₐ[M] E) :
    g ∈ upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) ↔
      g.restrictScalars K ∈
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  have hm := finiteTower_upper_map_restrictScalars_range K E M hu
  constructor
  · intro h
    have hmap : g.restrictScalars K ∈
        (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
          (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) :=
      Subgroup.mem_map.mpr ⟨g, h, rfl⟩
    rw [hm] at hmap
    exact hmap.2
  · intro h
    have hmap : g.restrictScalars K ∈
        (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
          (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) := by
      rw [hm]
      exact ⟨⟨g, rfl⟩, h⟩
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hmap
    have hag' : a = g := by
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun f : E ≃ₐ[K] E => f x) hag
    exact hag' ▸ ha

end FontaineWintenberger
