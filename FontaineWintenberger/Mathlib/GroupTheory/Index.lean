/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index

/-!
# Indices of subgroup products

This file relates finite index to preimages of subgroups and computes relative indices after
adjoining a common normal subgroup.

## Main results

* `finiteIndex_iff_comap_of_range`: A finite-index image detects finite index of every subgroup by
  preimage.
* `comap_sup_eq_of_normal_right_of_le_range`: One factor in the range suffices to pull back a normal
  product.
* `relIndex_eq_index_of_sup_eq_top`: A full product with a normal subgroup identifies its relative
  coset index with the absolute index.
* `relIndex_sup_sup_normal`: Adding a common normal factor changes neither of these relative coset
  sets.
* `sup_inf_eq_sup_inf_of_le_of_normal`: Intersecting a normal product with a containing subgroup
  gives its product there.
* `relIndex_sup_sup_eq_inf`: The relative index of two normal products is the index of their
  intersection.
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

/-- One factor in the range suffices to pull back a normal product. -/
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

namespace Subgroup

variable {G : Type*} [Group G] (A B U : Subgroup G) [U.Normal]

/-- If a subgroup and a normal subgroup generate the whole group, restricting the coset
space to the normal subgroup does not change its cardinality. -/
theorem relIndex_eq_index_of_sup_eq_top (h : A ⊔ U = ⊤) : A.relIndex U = A.index := by
  have key (x y : U) : QuotientGroup.leftRel (A.subgroupOf U) x y ↔
      QuotientGroup.leftRel A (x : G) (y : G) := by
    simp only [QuotientGroup.leftRel_apply, mem_subgroupOf, coe_mul, coe_inv]
  let f : U ⧸ A.subgroupOf U → G ⧸ A :=
    Quotient.map' Subtype.val (fun x y ha ↦ (key x y).mp ha)
  have hinj : Function.Injective f := by
    refine Quotient.ind₂' ?_
    intro a b hab
    exact Quotient.sound ((key a b).mpr (Quotient.exact hab))
  have hsurj : Function.Surjective f := by
    refine Quotient.ind' ?_
    intro g
    have hg : g ∈ U ⊔ A := by rw [sup_comm, h]; trivial
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨Quotient.mk'' (⟨u, hu⟩ : U), ?_⟩
    change (QuotientGroup.mk u : G ⧸ A) = QuotientGroup.mk (u * a)
    exact QuotientGroup.eq.mpr (by simpa using ha)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

/-- Restricting cosets of a normal product to the normal factor preserves the relative
index of the other factor. -/
theorem relIndex_sup_left_of_normal_right : A.relIndex (A ⊔ U) = A.relIndex U := by
  let f := quotientSubgroupOfEmbeddingOfLE A (show U ≤ A ⊔ U from le_sup_right)
  have hsurj : Function.Surjective f := by
    refine Quotient.ind' ?_
    intro g
    have hg : (g : G) ∈ U ⊔ A := by simpa only [sup_comm] using g.property
    obtain ⟨u, hu, a, ha, he⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨QuotientGroup.mk (⟨u, hu⟩ : U), ?_⟩
    apply QuotientGroup.eq.mpr
    change u⁻¹ * (g : G) ∈ A
    rw [← he]
    simpa using ha
  exact (Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hsurj⟩)).symm

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

/-- Intersecting a normal product with a containing subgroup gives its product there. -/
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

/-- The relative index of two normal products is the index of their intersection. -/
theorem relIndex_sup_sup_eq_inf (hAB : A ≤ B) :
    (A ⊔ U).relIndex (B ⊔ U) = (A ⊔ (U ⊓ B)).relIndex B := by
  rw [relIndex_sup_sup_normal, ← inf_relIndex_right,
    sup_inf_eq_sup_inf_of_le_of_normal A B U hAB]

end Subgroup
