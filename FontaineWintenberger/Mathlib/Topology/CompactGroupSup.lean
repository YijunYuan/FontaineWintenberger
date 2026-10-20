/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Suprema of closed subgroups with a decreasing intersection

In a compact topological group, `(⨅ n, H n) ⊔ U = ⨅ n, (H n ⊔ U)` for a decreasing sequence of
closed subgroups `H n` and a closed normal subgroup `U`: the sets `{h ∈ H n | h⁻¹ g ∈ U}` form a
decreasing sequence of nonempty compact sets.

Upstream candidate: `Mathlib.Topology.Algebra.Group.Compact`.
-/

@[expose] public section

namespace Subgroup

theorem iInf_sup_eq_iInf_sup_of_isClosed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : ℕ → Subgroup G) (hH : Antitone H) (hclosed : ∀ n, IsClosed (H n : Set G))
    (U : Subgroup G) [U.Normal] (hU : IsClosed (U : Set G)) :
    (⨅ n, H n) ⊔ U = ⨅ n, H n ⊔ U := by
  apply le_antisymm
  · exact le_iInf fun n => sup_le_sup_right (iInf_le H n) U
  · intro g hg
    let C : ℕ → Set G := fun n => {h | h ∈ H n ∧ h⁻¹ * g ∈ U}
    have hCclosed (n : ℕ) : IsClosed (C n) :=
      (hclosed n).inter (hU.preimage (continuous_inv.mul continuous_const))
    have hCnonempty (n : ℕ) : (C n).Nonempty := by
      obtain ⟨h, hh, u, hu, hhu⟩ :=
        Subgroup.mem_sup_of_normal_right.mp (Subgroup.mem_iInf.mp hg n)
      refine ⟨h, hh, ?_⟩
      rw [← hhu]
      simpa only [inv_mul_cancel_left] using hu
    obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n x hx => ⟨hH (Nat.le_succ n) hx.1, hx.2⟩) hCnonempty
      (hCclosed 0).isCompact hCclosed
    have hh' : ∀ n, h ∈ C n := Set.mem_iInter.mp hh
    apply Subgroup.mem_sup_of_normal_right.mpr
    exact ⟨h, Subgroup.mem_iInf.mpr (fun n => (hh' n).1), h⁻¹ * g, (hh' 0).2,
      mul_inv_cancel_left h g⟩

end Subgroup
