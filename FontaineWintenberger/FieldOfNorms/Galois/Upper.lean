/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Infinite
public import FontaineWintenberger.APF.Tower.Herbrand
public import FontaineWintenberger.FieldOfNorms.Galois.Ramification
public import FontaineWintenberger.FieldOfNorms.Relative.Defs
public import FontaineWintenberger.FieldOfNorms.Relative.UpperStage
public import FontaineWintenberger.Ramification.Infinite.FiniteRestriction

/-!
# Finite upper ramification comparison for the field of norms

The finite descent of a relative Galois extension can be chosen beyond any prescribed
Herbrand parameter. At such a layer its finite base has the same inverse Herbrand value as
the APF extension.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Corollary 3.3.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FiniteScalarTower

variable (K C E : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [NontriviallyNormedField C] [NormedAlgebra K C] [IsCompleteDiscreteValuedField C]
    [FiniteDimensional K C] [Field E] [Algebra K E] [Algebra C E]
    [IsScalarTower K C E] [FiniteDimensional K E] [Algebra.IsSeparable K E]

omit [FiniteDimensional K C] in
/-- The intrinsic upper groups over a finite scalar extension can be computed on the
original spectral integer ring: both rings are the same valuation subring. -/
theorem upperRamificationGroup_restrictScalars_eq {u : ℝ} (hu : -1 ≤ u) :
    letI : FiniteDimensional C E := Module.Finite.right K C E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K C E
    letI := MulSemiringAction.compHom (spectralIntegerRing K E)
      (AlgEquiv.restrictScalarsHom K (S := C) (A := E))
    upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[C] E) u =
      upperRamificationGroup (R := spectralIntegerRing C E) (E ≃ₐ[C] E) u := by
  let : FiniteDimensional C E := Module.Finite.right K C E
  let := Algebra.isSeparable_tower_top_of_isSeparable K C E
  let := MulSemiringAction.compHom (spectralIntegerRing K E)
    (AlgEquiv.restrictScalarsHom K (S := C) (A := E))
  let := spectralNorm.nontriviallyNormedField K E
  let := spectralNorm.normedAlgebra K E
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))
  let := spectralNorm.normedAlgebra' K C E
  let r : spectralIntegerRing K E ≃+* spectralIntegerRing C E :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      ((spectralIntegerRing_eq_normedUnitBall K E).trans
        (spectralIntegerRing_eq_normedUnitBall C E).symm))
  have h := upperRamificationGroup_map_equivariant r (MulEquiv.refl (E ≃ₐ[C] E))
    (fun _ _ ↦ Subtype.ext rfl) hu
  change (upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[C] E) u).map
    (MonoidHom.id _) = _ at h
  simpa only [Subgroup.map_id] using h

end FiniteScalarTower

section Descent

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L N : Type*) [Field L] [Field N] [Algebra K L] [Algebra K N]
    [Algebra L N] [IsScalarTower K L N] [Algebra.IsSeparable K L]
    [Module.Finite L N] [IsGalois L N] [Algebra.IsSeparable K N]
    [IsAPF K L] [IsAPF K N] [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K N)]

omit [Fact (¬ Module.Finite K L)] in
/-- The finite descent may be chosen with the same inverse Herbrand value as the APF
base, while preserving all ramification numbers of the relative Galois group. -/
theorem exists_galois_stable_goodFiniteLayer_apfPsi_eq
    (E : FiniteIntermediateField K N) (u : ℝ) :
    ∃ D : FiniteIntermediateField K N, E ≤ D ∧ IsGoodFiniteLayer K L D ∧
      (∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧
      (∃ α : N, α ∈ D.val ∧ IntermediateField.adjoin L {α} = ⊤) ∧
      apfPsi K (FiniteIntermediateField.pullback K L D) u = apfPsi K L u ∧
      ∀ σ : N ≃ₐ[L] N,
        FiniteIntermediateField.ramificationNumber K N (σ.restrictScalars K) D =
          FieldOfNorms.ramificationNumber K N (σ.restrictScalars K) := by
  obtain ⟨C, hC⟩ := IsAPF.exists_finiteIntermediateField_apfPsi_eq K L u
  let C' := FiniteIntermediateField.map (IsScalarTower.toAlgHom K L N) C
  obtain ⟨D, hD, hg, hs, hα, hr⟩ :=
    exists_galois_stable_goodFiniteLayer_ramificationNumber_eq K L N
      (FiniteIntermediateField.sup E C')
  have hCD : C ≤ FiniteIntermediateField.pullbackLayer K L D := by
    intro x hx
    exact hD (FiniteIntermediateField.le_sup_right E C' ⟨x, hx, rfl⟩)
  exact ⟨D, (FiniteIntermediateField.le_sup_left E C').trans hD, hg, hs, hα,
    hC (FiniteIntermediateField.pullbackLayer K L D) hCD u le_rfl, hr D le_rfl⟩

end Descent

section AmbientComparison

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L N M : Type*) [Field M] [Algebra K M] [IsGalois K M]
    [Field L] [Field N] [Algebra K L] [Algebra K N]
    [Algebra L N] [IsScalarTower K L N] [Algebra.IsSeparable K L]
    [Module.Finite L N] [IsGalois L N] [Algebra.IsSeparable K N]
    [IsAPF K L] [IsAPF K N] [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K N)]
    [Algebra L M] [Algebra N M] [IsScalarTower K L M] [IsScalarTower K N M]
    [IsScalarTower L N M] [Algebra M (SeparableClosure K)]
    [Algebra L (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]
    [IsScalarTower K L (SeparableClosure K)] [IsScalarTower L M (SeparableClosure K)]

attribute [local instance]
  FiniteIntermediateField.instNontriviallyNormedField
  FiniteIntermediateField.instNormedAlgebra
  FiniteIntermediateField.instIsUltrametricDist
  FiniteIntermediateField.instCompleteSpace
  FiniteIntermediateField.instIsPerfectResidueLocalField
  FiniteIntermediateField.instIsSeparable

omit [Fact (¬ Module.Finite K L)] [IsScalarTower K N M] in
/-- Restriction of an upper automorphism fixing the APF extension belongs to
the shifted upper group of every finite relative norm-field extension. -/
theorem FieldOfNorms.restrictNormal_mem_upperRamificationGroup_tower
    {u : ℝ} (hu : -1 ≤ u) (σ : M ≃ₐ[L] M)
    (hσ : σ.restrictScalars K ∈ upperRamificationGroupInfinite K M u) :
    σ.restrictNormal N ∈ FieldOfNorms.upperRamificationGroup K L N (apfPsi K L u) := by
  obtain ⟨D, _, _, hs, ⟨α, hαD, hα⟩, hψ, hr⟩ :=
    exists_galois_stable_goodFiniteLayer_apfPsi_eq K L N ⟨⊥, inferInstance⟩ u
  let C := FiniteIntermediateField.pullbackLayer K L D
  let : Algebra C.val D.val := FiniteIntermediateField.pullbackAlgebra K L D
  let : IsScalarTower K C.val D.val := FiniteIntermediateField.pullback_scalarTower K L D
  let : FiniteDimensional C.val D.val := FiniteIntermediateField.overPullback_finite K L D
  let : IsScalarTower C.val D.val M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ IsScalarTower.algebraMap_apply L N M x
  let : IsGalois C.val D.val := isGalois_galoisStableFiniteLayer K L N D hs
  let σC := σ.restrictScalars C.val
  have hσC : σC ∈ upperRamificationGroupInfinite C.val M
      (apfPsi K C.val u) :=
    (mem_upperRamificationGroupInfinite_finiteBase_tower_iff K C.val M hu σC).mpr hσ
  have hv : -1 ≤ apfPsi K C.val u := IsAPF.apfPsi_mem_Ici K C.val hu
  have hD := restrictNormal_mem_upperRamificationGroup_of_finite C.val
    M D.val hv σC hσC
  let := MulSemiringAction.compHom (spectralIntegerRing K D.val)
    (AlgEquiv.restrictScalarsHom K (S := C.val) (A := D.val))
  rw [← upperRamificationGroup_restrictScalars_eq K C.val D.val hv] at hD
  change apfPsi K C.val u = apfPsi K L u at hψ
  rw [hψ] at hD
  let e : (N ≃ₐ[L] N) ≃* (D.val ≃ₐ[C.val] D.val) :=
    galoisFiniteLayerEquiv K L N D hs α hα hαD
  have hm : (FieldOfNorms.upperRamificationGroup K L N (apfPsi K L u)).map
        e.toMonoidHom =
      FontaineWintenberger.upperRamificationGroup (R := spectralIntegerRing K D.val)
        (D.val ≃ₐ[C.val] D.val) (apfPsi K L u) :=
    galoisFiniteLayerEquiv_map_upperRamificationGroup K L N D hs α hα hαD hr
      (IsAPF.apfPsi_mem_Ici K L hu)
  rw [← hm] at hD
  have hD' := (Subgroup.mem_map_equiv (f := e)).mp hD
  have he : e (σ.restrictNormal N) =
      σC.restrictNormal D.val := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap D.val M).injective
    exact (AlgEquiv.restrictNormal_commutes σ N (x : N)).trans
      (AlgEquiv.restrictNormal_commutes σC D.val x).symm
  rw [← he, MulEquiv.symm_apply_apply] at hD'
  exact hD'

end AmbientComparison

section AbsoluteComparison

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L N : Type*) [Field L] [Field N] [Algebra K L] [Algebra K N]
    [Algebra L N] [IsScalarTower K L N] [Algebra.IsSeparable K L]
    [Module.Finite L N] [IsGalois L N] [Algebra.IsSeparable K N]
    [IsAPF K L] [IsAPF K N] [Fact (¬ Module.Finite K N)]
    [Algebra L (SeparableClosure K)] [Algebra N (SeparableClosure K)]
    [IsScalarTower K L (SeparableClosure K)] [IsScalarTower K N (SeparableClosure K)]
    [IsScalarTower L N (SeparableClosure K)]

omit [IsScalarTower K N (SeparableClosure K)] in
/-- The finite upper comparison in a separable closure. -/
theorem FieldOfNorms.restrictNormal_mem_upperRamificationGroup
    {u : ℝ} (hu : -1 ≤ u) (σ : SeparableClosure K ≃ₐ[L] SeparableClosure K)
    (hσ : σ.restrictScalars K ∈ absoluteUpperRamificationGroup K u) :
    σ.restrictNormal N ∈ FieldOfNorms.upperRamificationGroup K L N (apfPsi K L u) :=
  FieldOfNorms.restrictNormal_mem_upperRamificationGroup_tower K L N (SeparableClosure K) hu σ hσ

end AbsoluteComparison

end FontaineWintenberger
