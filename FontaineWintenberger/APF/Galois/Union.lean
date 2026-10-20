/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Defs
public import FontaineWintenberger.Mathlib.Topology.CompactGroupSup

/-!
# The APF subgroups of a directed union

For an increasing sequence of subextensions `D n` of `K^sep/K`,
`apfSubgroup K (⨆ n, D n) u = ⨅ n, apfSubgroup K (D n) u`: the fixing subgroup of the union is
the intersection of the fixing subgroups, and the supremum with the closed normal upper
ramification group commutes with this intersection by compactness.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.2.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

theorem apfSubgroup_iSup_eq_iInf
    (D : ℕ → IntermediateField K (SeparableClosure K)) (hD : Monotone D) (u : ℝ) :
    apfSubgroup K (⨆ n, D n) u = ⨅ n, apfSubgroup K (D n) u := by
  let : T2Space (SeparableClosure K ≃ₐ[K] SeparableClosure K) := krullTopology_t2
  have hfix : (⨆ n, D n).fixingSubgroup = ⨅ n, (D n).fixingSubgroup := by
    change fixingSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      ((⨆ n, D n : IntermediateField K (SeparableClosure K)) : Set (SeparableClosure K)) =
      ⨅ n, fixingSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K)
        (D n : Set (SeparableClosure K))
    rw [IntermediateField.coe_iSup_of_directed hD.directed_le, fixingSubgroup_iUnion]
  unfold apfSubgroup
  rw [hfix]
  exact Subgroup.iInf_sup_eq_iInf_sup_of_isClosed (fun n => (D n).fixingSubgroup)
    (fun m n hmn => IntermediateField.fixingSubgroup_le (hD hmn))
    (fun n => InfiniteGalois.fixingSubgroup_isClosed (D n))
    (absoluteUpperRamificationGroup K u)
    (isCompact_upperRamificationGroupInfinite K (SeparableClosure K) u).isClosed

end FontaineWintenberger
