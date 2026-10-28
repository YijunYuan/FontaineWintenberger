/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.Ramification.Infinite.ScalarTower

/-!
# Finite base change inside an arbitrary Galois extension

Upper ramification changes by the inverse Herbrand function of the finite base extension.
The common separable closure is only used to lift automorphisms; the resulting equality is
in the Galois group of the given ambient extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K C M : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [NontriviallyNormedField C] [NormedAlgebra K C] [IsCompleteDiscreteValuedField C]
    [PerfectField 𝓀[C]] [FiniteDimensional K C] [Algebra.IsSeparable K C]
    [Field M] [Algebra K M] [Algebra C M] [IsScalarTower K C M] [IsGalois K M]
    [Algebra M (SeparableClosure K)] [Algebra C (SeparableClosure K)]
    [IsScalarTower K M (SeparableClosure K)] [IsScalarTower K C (SeparableClosure K)]
    [IsScalarTower C M (SeparableClosure K)]

/-- Finite base change for upper ramification in any Galois ambient extension. -/
theorem mem_upperRamificationGroupInfinite_finiteBase_tower_iff
    {u : ℝ} (hu : -1 ≤ u) (σ : M ≃ₐ[C] M) :
    σ ∈ upperRamificationGroupInfinite C M (apfPsi K C u) ↔
      σ.restrictScalars K ∈ upperRamificationGroupInfinite K M u := by
  let := IsGalois.tower_top_of_isGalois K C M
  let := AbstractFiniteBase.isSepClosure K C
  have hv := IsAPF.apfPsi_mem_Ici K C hu
  constructor
  · intro hσ
    obtain ⟨τ, hτ, he⟩ := exists_lift_upperRamificationGroupInfinite_tower C
      (SeparableClosure K) M hv σ hσ
    have hτK := (AbstractFiniteBase.mem_upper_finiteBase_iff K C hu τ).mp hτ
    have hM := restrictNormal_mem_upperRamificationGroupInfinite_tower K
      (SeparableClosure K) M hu (τ.restrictScalars K) hτK
    rwa [AlgEquiv.restrictNormal_restrictScalars, he] at hM
  · intro hσ
    obtain ⟨τ, hτ, he⟩ := exists_lift_upperRamificationGroupInfinite_tower K
      (SeparableClosure K) M hu (σ.restrictScalars K) hσ
    have hfix (x : C) : τ (algebraMap C (SeparableClosure K) x) =
        algebraMap C (SeparableClosure K) x := by
      rw [IsScalarTower.algebraMap_apply C M (SeparableClosure K)]
      rw [← AlgEquiv.restrictNormal_commutes τ M, he]
      change algebraMap M (SeparableClosure K) (σ (algebraMap C M x)) = _
      rw [σ.commutes]
    let τC : SeparableClosure K ≃ₐ[C] SeparableClosure K :=
      { τ.toRingEquiv with commutes' := hfix }
    have hτC := (AbstractFiniteBase.mem_upper_finiteBase_iff K C hu τC).mpr hτ
    have hM := restrictNormal_mem_upperRamificationGroupInfinite_tower C
      (SeparableClosure K) M hv τC hτC
    have hres : τC.restrictNormal M = σ := by
      apply AlgEquiv.restrictScalars_injective K
      rw [← AlgEquiv.restrictNormal_restrictScalars]
      exact he
    exact hres ▸ hM

end FontaineWintenberger
