module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Finite-index restriction and normal products
-/

@[expose] public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G'] (f : G' →* G)

/-- A finite-index image detects finite index of every subgroup by preimage. -/
theorem finiteIndex_iff_comap_of_range (J : Subgroup G) [f.range.FiniteIndex] :
    J.FiniteIndex ↔ (J.comap f).FiniteIndex := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    have hrel : J.IsFiniteRelIndex f.range := by
      rw [isFiniteRelIndex_iff_relIndex_ne_zero, ← index_comap]
      exact h.index_ne_zero
    exact isFiniteRelIndex_top_iff.mp
      (hrel.trans (isFiniteRelIndex_top_iff.mpr inferInstance))

/-- One factor in the actual range suffices to pull back a normal product. -/
theorem comap_sup_eq_of_normal_right_of_le_range
    (A U : Subgroup G) [U.Normal] (hA : A ≤ f.range) :
    A.comap f ⊔ U.comap f = (A ⊔ U).comap f := by
  apply le_antisymm (comap_sup_comap_le A U f)
  intro g hg
  obtain ⟨a, ha, u, hu, hau⟩ := mem_sup_of_normal_right.mp hg
  obtain ⟨a', rfl⟩ := hA ha
  have hu' : f (a'⁻¹ * g) ∈ U := by
    rw [map_mul, map_inv, ← hau]
    simpa only [inv_mul_cancel_left] using hu
  exact mem_sup_of_normal_right.mpr ⟨a', ha, a'⁻¹ * g, hu', by simp⟩

end Subgroup
