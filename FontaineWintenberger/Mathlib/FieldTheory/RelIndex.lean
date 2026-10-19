/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Relative fixing indices

The fixing index of two intermediate fields in any algebraic Galois
ambient extension equals their relative field degree. The natural-valued
identity includes infinite degree and index, both represented by zero.
-/

@[expose] public section

namespace FontaineWintenberger

section Fields

variable (K : Type*) [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (M N : IntermediateField K Ω)
    (hMN : M ≤ N)

/-- The relative fixing index equals the field degree over the intermediate base. -/
theorem fixingSubgroup_relIndex_eq_finrank :
    N.fixingSubgroup.relIndex M.fixingSubgroup =
      Module.finrank M (IntermediateField.extendScalars hMN) := by
  let ρ := M.fixingSubgroup.subtype.comp M.fixingSubgroupEquiv.symm.toMonoidHom
  have hrange : ρ.range = M.fixingSubgroup := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr M.fixingSubgroupEquiv.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hfix : N.fixingSubgroup.comap ρ = (IntermediateField.extendScalars hMN).fixingSubgroup := by
    ext g
    rfl
  rw [← hrange, ← Subgroup.index_comap, hfix]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω
    (IntermediateField.extendScalars hMN)).symm

/-- A finite extension of the intermediate field gives a nonzero fixing index. -/
theorem fixingSubgroup_relIndex_pos [FiniteDimensional M (IntermediateField.extendScalars hMN)] :
    0 < N.fixingSubgroup.relIndex M.fixingSubgroup := by
  rw [fixingSubgroup_relIndex_eq_finrank K M N hMN]
  exact Module.finrank_pos

end Fields

end FontaineWintenberger
