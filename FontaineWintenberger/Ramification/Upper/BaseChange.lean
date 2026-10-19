/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.BaseChange
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Upper.CosetMax

/-!
# Lower ramification for intermediate-field automorphisms

The integer ring over a finite intermediate base is the same subring.
The canonical fixing-subgroup equivalence therefore transports displacement
orders and lower groups to the ordinary automorphism group over that base.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (E : Type*) [NontriviallyNormedField E] [NormedAlgebra K E] [IsUltrametricDist E]
    [Algebra.IsAlgebraic K E]
variable (M : IntermediateField K E) [FiniteDimensional K M]

local instance : CompleteSpace M := FiniteDimensional.complete K M

variable [IsDiscreteValuationRing (spectralIntegerRing K E)]

local instance : IsDiscreteValuationRing (spectralIntegerRing M E) := by
  rw [← finiteBase_spectralIntegerRing_eq K E M]
  infer_instance

/-- The order over the intermediate base is the displacement order. -/
theorem finiteBase_ramificationOrder (g : M.fixingSubgroup) :
    ramificationOrder (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (M.fixingSubgroupEquiv g) =
      ramificationOrder (R := spectralIntegerRing K E) (E ≃ₐ[K] E) g.1 := by
  rw [ramificationOrder_equivariant (finiteBase_spectralIntegerRingEquiv K E M)
    M.fixingSubgroupEquiv (finiteBase_spectralIntegerRingEquiv_smul K E M)]
  rfl

/-- Real lower groups transport through the fixing-subgroup equivalence. -/
theorem finiteBase_lowerReal_map_fixingSubgroupEquiv (t : ℝ) :
    ((lowerRamificationGroupReal (E ≃ₐ[K] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) t).subgroupOf
          M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom =
      lowerRamificationGroupReal (E ≃ₐ[M] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing M E)) t := by
  rw [lowerRamificationGroupReal_subgroupOf]
  exact lowerRamificationGroupReal_map_equivariant
    (finiteBase_spectralIntegerRingEquiv K E M) M.fixingSubgroupEquiv
    (finiteBase_spectralIntegerRingEquiv_smul K E M) t

/-- Integer lower groups use the same canonical ideal-inertia filtration. -/
theorem finiteBase_lower_map_fixingSubgroupEquiv (n : ℤ) :
    ((lowerRamificationGroup (E ≃ₐ[K] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) n).subgroupOf
          M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom =
      lowerRamificationGroup (E ≃ₐ[M] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing M E)) n := by
  simpa only [lowerRamificationGroupReal_intCast] using
    finiteBase_lowerReal_map_fixingSubgroupEquiv K E M (n : ℝ)

/-- Inside the automorphism group, the lower group is the intersection. -/
theorem finiteBase_lowerReal_map_restrictScalars (t : ℝ) :
    (lowerRamificationGroupReal (E ≃ₐ[M] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing M E)) t).map
          (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroupReal (E ≃ₐ[K] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) t ⊓ M.fixingSubgroup := by
  rw [← finiteBase_lowerReal_map_fixingSubgroupEquiv K E M, Subgroup.map_map]
  have hc : (AlgEquiv.restrictScalarsHom K).comp
      M.fixingSubgroupEquiv.toMonoidHom = M.fixingSubgroup.subtype := by
    ext g x
    rfl
  rw [hc, Subgroup.subgroupOf_map_subtype]

/-- Integer lower numbering is compatible with the restriction of scalars. -/
theorem finiteBase_lower_map_restrictScalars (n : ℤ) :
    (lowerRamificationGroup (E ≃ₐ[M] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing M E)) n).map
          (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup (E ≃ₐ[K] E)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) n ⊓ M.fixingSubgroup := by
  simpa only [lowerRamificationGroupReal_intCast] using
    finiteBase_lowerReal_map_restrictScalars K E M (n : ℝ)

/-- If the fixing group lies in the inertia, the own-ring
intermediate-base action has full inertia. -/
theorem finiteBase_lower_zero_eq_top
    (hM : M.fixingSubgroup ≤ lowerRamificationGroup (E ≃ₐ[K] E)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K E)) 0) :
    lowerRamificationGroup (E ≃ₐ[M] E)
      (IsLocalRing.maximalIdeal (spectralIntegerRing M E)) 0 = ⊤ := by
  rw [← finiteBase_lower_map_fixingSubgroupEquiv K E M]
  rw [Subgroup.subgroupOf_eq_top.mpr hM, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr M.fixingSubgroupEquiv.surjective]

variable [FiniteDimensional K E]

/-- Upper groups transport through the identity of integer subrings. -/
theorem finiteBase_upper_map_fixingSubgroupEquiv {v : ℝ} (hv : -1 ≤ v) :
    (upperRamificationGroup (R := spectralIntegerRing K E) M.fixingSubgroup v).map
        M.fixingSubgroupEquiv.toMonoidHom =
      upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E) v :=
  upperRamificationGroup_map_equivariant
    (finiteBase_spectralIntegerRingEquiv K E M) M.fixingSubgroupEquiv
    (finiteBase_spectralIntegerRingEquiv_smul K E M) hv

end FontaineWintenberger
