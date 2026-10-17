module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Relative indices of actual normal products
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] (A B U : Subgroup G) [U.Normal]

/-- Adding a common normal factor changes neither of these relative coset sets. -/
theorem relIndex_sup_sup_normal :
    (A ⊔ U).relIndex (B ⊔ U) = (A ⊔ U).relIndex B := by
  let q := QuotientGroup.mk' U
  have hker : q.ker = U := QuotientGroup.ker_mk' U
  have hpre : (A.map q).comap q = A ⊔ U := by
    rw [comap_map_eq, hker]
  have hm := relIndex_map_map q A B
  rw [hker] at hm
  calc
    (A ⊔ U).relIndex (B ⊔ U) = (A.map q).relIndex (B.map q) := hm.symm
    _ = ((A.map q).comap q).relIndex B := (relIndex_comap (A.map q) q B).symm
    _ = (A ⊔ U).relIndex B := by rw [hpre]

/-- Intersecting a normal product with a containing subgroup gives its actual product there. -/
theorem sup_inf_eq_sup_inf_of_le_of_normal (hAB : A ≤ B) :
    (A ⊔ U) ⊓ B = A ⊔ (U ⊓ B) := by
  apply le_antisymm
  · rintro g ⟨hg, hgB⟩
    obtain ⟨a, ha, u, hu, rfl⟩ := mem_sup_of_normal_right.mp hg
    have huB : u ∈ B := by
      have h := B.mul_mem (B.inv_mem (hAB ha)) hgB
      simpa only [inv_mul_cancel_left] using h
    exact (A ⊔ (U ⊓ B)).mul_mem
      ((show A ≤ A ⊔ (U ⊓ B) from le_sup_left) ha)
      ((show U ⊓ B ≤ A ⊔ (U ⊓ B) from le_sup_right) ⟨hu, huB⟩)
  · exact sup_le (le_inf le_sup_left hAB)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- The relative index of two normal products is the index of their actual intersection. -/
theorem relIndex_sup_sup_eq_inf (hAB : A ≤ B) :
    (A ⊔ U).relIndex (B ⊔ U) = (A ⊔ (U ⊓ B)).relIndex B := by
  rw [relIndex_sup_sup_normal, ← inf_relIndex_right,
    sup_inf_eq_sup_inf_of_le_of_normal A B U hAB]

end Subgroup
