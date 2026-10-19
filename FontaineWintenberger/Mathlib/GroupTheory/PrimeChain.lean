/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Atoms.Finite

/-!
# Relative prime-step chains in finite p-groups

Each proper subgroup is contained in a maximal subgroup, which is normal
of index `p`. Recursion in the finite subgroup lattice gives a finite chain
of inclusions, represented by the canonical reflexive transitive closure.

## Main results

* `exists_normal_index_prime_le`: A maximal subgroup containing a given proper subgroup of a finite
  p-group is a normal subgroup of index `p`.
* `subgroup_prime_chain_of_isPGroup`: A finite p-group has normal index-prime steps between any two
  of its subgroups.
* `subgroup_prime_chain`: Relative prime-step refinement inside any finite p-group.

## References

* Mathlib; this file is an upstream candidate and has no project-specific reference.
-/

@[expose] public section

namespace FontaineWintenberger

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A maximal subgroup containing a given proper subgroup of a finite p-group
is a normal subgroup of index `p`. -/
theorem exists_normal_index_prime_le (hG : IsPGroup p G) (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ M < ⊤ ∧ M.Normal ∧ M.index = p := by
  let : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  exact ⟨M, hHM, hM.lt_top,
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM,
    hG.isCoatom_iff_index_eq_prime.mp hM⟩

/-- A finite p-group has normal index-prime steps between any two
of its subgroups. The reflexive case is the length-zero chain. -/
theorem subgroup_prime_chain_of_isPGroup (K H : Subgroup G) (hK : IsPGroup p K) (hHK : H ≤ K) :
    Relation.ReflTransGen
      (fun M N : Subgroup G => N ≤ M ∧ (N.subgroupOf M).Normal ∧
        (N.subgroupOf M).index = p) K H := by
  classical
  induction K using WellFoundedLT.induction with
  | ind K ih =>
    by_cases heq : H = K
    · subst H
      exact Relation.ReflTransGen.refl
    have hproper : H.subgroupOf K ≠ ⊤ := by
      intro h
      have hm := congrArg (fun S : Subgroup K => S.map K.subtype) h
      rw [Subgroup.map_subgroupOf_eq_of_le hHK, Subgroup.map_top, K.range_subtype] at hm
      exact heq hm
    obtain ⟨M, hHM, hM, hnormal, hindex⟩ :=
      exists_normal_index_prime_le hK (H.subgroupOf K) hproper
    let N := M.map K.subtype
    have hNK : N < K := by
      have h := Subgroup.map_subtype_lt_map_subtype.mpr hM
      simpa only [Subgroup.map_top, K.range_subtype] using h
    have hHN : H ≤ N := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hHK]
      exact Subgroup.map_mono hHM
    have hNM : N.subgroupOf K = M := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hNK.le]
    apply Relation.ReflTransGen.head (b := N)
    · exact ⟨hNK.le, hNM ▸ hnormal, hNM ▸ hindex⟩
    · exact ih N hNK (hK.of_injective (Subgroup.inclusion hNK.le)
        (Subgroup.inclusion_injective _)) hHN

/-- Relative prime-step refinement inside any finite p-group. -/
theorem subgroup_prime_chain (hG : IsPGroup p G) (K H : Subgroup G) (hHK : H ≤ K) :
    Relation.ReflTransGen
      (fun M N : Subgroup G => N ≤ M ∧ (N.subgroupOf M).Normal ∧
        (N.subgroupOf M).index = p) K H :=
  subgroup_prime_chain_of_isPGroup K H (hG.to_subgroup K) hHK

end FontaineWintenberger
