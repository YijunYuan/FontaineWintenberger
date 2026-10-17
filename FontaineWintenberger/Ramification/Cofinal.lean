/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Absolute

/-!
# Testing actual infinite upper groups on cofinal finite layers
-/

@[expose] public section

namespace FontaineWintenberger

variable (K Ω : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field Ω] [Algebra K Ω]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- A cofinal family of actual finite layers tests all infinite upper conditions. -/
theorem mem_upperRamificationGroupInfinite_iff_cofinal
    {ι : Type*} (E : ι → FiniteGaloisIntermediateField K Ω)
    (hE : ∀ D : FiniteGaloisIntermediateField K Ω, ∃ j, D ≤ E j)
    {u : ℝ} (hu : -1 ≤ u) (g : Ω ≃ₐ[K] Ω) :
    g ∈ upperRamificationGroupInfinite K Ω u ↔
      ∀ j, g.restrictNormal (E j) ∈
        upperRamificationGroup (R := spectralIntegerRing K (E j)) (E j ≃ₐ[K] E j) u := by
  rw [mem_upperRamificationGroupInfinite]
  constructor
  · exact fun h j => h (E j)
  · intro h D
    obtain ⟨j, hj⟩ := hE D
    let f : Opposite.op (E j) ⟶ Opposite.op D := (CategoryTheory.homOfLE hj).op
    have hres := (InfiniteGalois.algEquivToLimit K Ω g).property f
    change (finGaloisGroupMap f).hom.hom (g.restrictNormal (E j)) =
      g.restrictNormal D at hres
    rw [← finGaloisGroupMap_map_upperRamificationGroup K Ω f u hu]
    exact Subgroup.mem_map.mpr ⟨g.restrictNormal (E j), h j, hres⟩

end FontaineWintenberger
