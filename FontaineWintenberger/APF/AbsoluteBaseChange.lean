/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.FiniteTower
public import FontaineWintenberger.APF.CofinalBase
public import FontaineWintenberger.LocalField.ResidueField
public import FontaineWintenberger.Ramification.Cofinal
public import FontaineWintenberger.Ramification.InfiniteEquiv

/-!
# Absolute upper ramification after finite base change

Finite upper conditions are tested on the cofinal old-base normal overfields.
Every finite comparison uses the actual scalar-tower and integer-ring actions.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

noncomputable local instance : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
noncomputable local instance : NormedAlgebra K M := spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsDiscreteValuationRing (NormedField.valuation (K := M)).valuationSubring :=
  normedAlgebra_unitBall_isDiscreteValuationRing K M
local instance : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := M)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K M

/-- New-base upper conditions can be tested on the old-base normal overfields. -/
theorem mem_upperRamificationGroupInfinite_base_iff
    {v : ℝ} (hv : -1 ≤ v) (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) v ↔
      ∀ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (hME : M ≤ E.toIntermediateField),
        g.restrictNormal (finiteGaloisLayerOverBase K M E hME) ∈
          upperRamificationGroup
            (R := spectralIntegerRing M (finiteGaloisLayerOverBase K M E hME))
            (finiteGaloisLayerOverBase K M E hME ≃ₐ[M]
              finiteGaloisLayerOverBase K M E hME) v := by
  let F (j : {E : FiniteGaloisIntermediateField K (SeparableClosure K) //
      M ≤ E.toIntermediateField}) := finiteGaloisLayerOverBase K M j.1 j.2
  have hF : ∀ D : FiniteGaloisIntermediateField M (SeparableClosure K), ∃ j, D ≤ F j := by
    intro D
    obtain ⟨E, hME, hDE⟩ := exists_finiteGalois_over_base_layer K M D
    exact ⟨⟨E, hME⟩, hDE⟩
  rw [mem_upperRamificationGroupInfinite_iff_cofinal M (SeparableClosure K) F hF hv g]
  exact ⟨fun h E hME => h ⟨E, hME⟩, fun h j => h j.1 j.2⟩

/-- Old-base upper conditions can be tested on finite layers containing the new base. -/
theorem mem_upperRamificationGroupInfinite_containing_base_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite K (SeparableClosure K) u ↔
      ∀ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (_ : M ≤ E.toIntermediateField),
        g.restrictNormal E ∈
          upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  let F (j : {E : FiniteGaloisIntermediateField K (SeparableClosure K) //
      M ≤ E.toIntermediateField}) := j.1
  have hF : ∀ D : FiniteGaloisIntermediateField K (SeparableClosure K), ∃ j, D ≤ F j := by
    intro D
    obtain ⟨E, hME, hDE⟩ := exists_finiteGalois_containing_base K M D
    exact ⟨⟨E, hME⟩, hDE⟩
  rw [mem_upperRamificationGroupInfinite_iff_cofinal K (SeparableClosure K) F hF hu g]
  exact ⟨fun h E hME => h ⟨E, hME⟩, fun h j => h j.1 j.2⟩

/-- Finite restrictions compare the two actual own-ring upper conditions. -/
theorem finiteBase_restriction_mem_upper_iff
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : M ≤ E.toIntermediateField) {u : ℝ} (hu : -1 ≤ u)
    (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g.restrictNormal (finiteGaloisLayerOverBase K M E hME) ∈
        upperRamificationGroup
          (R := spectralIntegerRing M (finiteGaloisLayerOverBase K M E hME))
          (finiteGaloisLayerOverBase K M E hME ≃ₐ[M]
            finiteGaloisLayerOverBase K M E hME) (apfPsi K M u) ↔
      (g.restrictScalars K).restrictNormal E ∈
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  let : Algebra M E := (IntermediateField.inclusion hME).toRingHom.toAlgebra
  let : IsScalarTower K M E := IsScalarTower.of_algHom (IntermediateField.inclusion hME)
  let _ : Module M E := Algebra.toModule
  let : FiniteDimensional M E := Module.Finite.right K M E
  let : Algebra.IsSeparable M E := Algebra.isSeparable_tower_top_of_isSeparable K M E
  let : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.tower_top (K := K) M
  let q : E ≃ₐ[M] E := g.restrictNormal (finiteGaloisLayerOverBase K M E hME)
  have hq : q.restrictScalars K = (g.restrictScalars K).restrictNormal E := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes g
      (finiteGaloisLayerOverBase K M E hME) x).trans
        (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) E x).symm
  change q ∈ upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
    (apfPsi K M u) ↔ _
  rw [finiteTower_mem_upper_iff_restrictScalars K E M hu q, hq]

/-- Changing the finite base changes the parameter in the actual common-closure upper group. -/
theorem mem_upperRamificationGroupInfinite_finiteBase_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) (apfPsi K M u) ↔
      g.restrictScalars K ∈ upperRamificationGroupInfinite K (SeparableClosure K) u := by
  have hv := IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu
  rw [mem_upperRamificationGroupInfinite_base_iff K M hv g,
    mem_upperRamificationGroupInfinite_containing_base_iff K M hu (g.restrictScalars K)]
  exact forall_congr' fun E => forall_congr' fun hME =>
    finiteBase_restriction_mem_upper_iff K M E hME hu g

/-- The actual separable-closure identification preserves the finite-base parameter change. -/
theorem absoluteGaloisBaseChange_mem_upper_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure M ≃ₐ[M] SeparableClosure M) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure M) (apfPsi K M u) ↔
      (absoluteGaloisBaseChangeEquiv K M g).1 ∈
        upperRamificationGroupInfinite K (SeparableClosure K) u := by
  have hv := IsAPF.apfPsi_mem_Ici K M (isAPF_of_finite K M) hu
  exact (mem_upperRamificationGroupInfinite_autCongr_iff M
    (separableClosureBaseChangeEquiv K M) hv g).symm.trans
      (mem_upperRamificationGroupInfinite_finiteBase_iff K M hu
        ((separableClosureBaseChangeEquiv K M).autCongr g))

/-- The actual absolute new-base upper group maps onto the old upper group's fixing intersection. -/
theorem absoluteGaloisBaseChange_map_upper {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite M (SeparableClosure M) (apfPsi K M u)).map
        (M.fixingSubgroup.subtype.comp (absoluteGaloisBaseChangeEquiv K M).toMonoidHom) =
      M.fixingSubgroup ⊓ upperRamificationGroupInfinite K (SeparableClosure K) u := by
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(absoluteGaloisBaseChangeEquiv K M g).property,
      (absoluteGaloisBaseChange_mem_upper_iff K M hu g).mp hg⟩
  · intro hs
    let g := (absoluteGaloisBaseChangeEquiv K M).symm ⟨s, hs.1⟩
    have hgs : (absoluteGaloisBaseChangeEquiv K M g).1 = s :=
      congrArg Subtype.val ((absoluteGaloisBaseChangeEquiv K M).apply_symm_apply ⟨s, hs.1⟩)
    refine ⟨g, ?_, hgs⟩
    apply (absoluteGaloisBaseChange_mem_upper_iff K M hu g).mpr
    rw [hgs]
    exact hs.2

end FontaineWintenberger
