/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.InfiniteRestriction
public import FontaineWintenberger.Ramification.UpperLimit
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Absolute upper ramification and its actual Galois images

The absolute group uses mathlib's actual separable closure. Finite and
infinite restriction are the existing ordinary algebra-automorphism maps.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- Absolute upper numbering inside the actual automorphism group of the separable closure. -/
noncomputable abbrev absoluteUpperRamificationGroup (u : ℝ) :
    Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  upperRamificationGroupInfinite K (SeparableClosure K) u

variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Absolute upper projection onto every actual finite Galois subextension. -/
theorem absolute_map_upperRamificationGroup
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (u : ℝ) (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).map (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u :=
  map_upperRamificationGroupInfinite K (SeparableClosure K) E u hu

/-- Absolute upper projection onto every actual algebraic Galois subextension. -/
theorem absolute_restrict_map_upperRamificationGroupInfinite
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] (u : ℝ) (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroupInfinite K L u :=
  restrictNormalHom_map_upperRamificationGroupInfinite K (SeparableClosure K) L u hu

/-- The actual absolute upper image is canonically the inverse limit of the finite upper groups. -/
noncomputable def absoluteUpperImageEquivToLimit
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] (u : ℝ) (hu : -1 ≤ u) :
    (absoluteUpperRamificationGroup K u).map (AlgEquiv.restrictNormalHom L) ≃ₜ*
      ProfiniteGrp.limit (finiteUpperRamificationGroupFunctor K L u hu) := by
  rw [absolute_restrict_map_upperRamificationGroupInfinite K L u hu]
  exact upperRamificationEquivToLimit K L u hu

/-- The absolute-image equivalence retains the ordinary restriction in every finite coordinate. -/
@[simp]
theorem absoluteUpperImageEquivToLimit_apply_val
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] (u : ℝ) (hu : -1 ≤ u)
    (s : (absoluteUpperRamificationGroup K u).map (AlgEquiv.restrictNormalHom L))
    (E : FiniteGaloisIntermediateField K L) :
    ((absoluteUpperImageEquivToLimit K L u hu s).val (Opposite.op E)).val =
      s.val.restrictNormal E := by
  let T := ProfiniteGrp.limit (finiteUpperRamificationGroupFunctor K L u hu)
  have hcast (P Q : Subgroup (L ≃ₐ[K] L)) (h : P = Q) (e : Q ≃ₜ* T) (x : P) :
      (cast (congrArg (fun A : Subgroup (L ≃ₐ[K] L) => A ≃ₜ* T) h.symm) e) x =
        e ⟨x.val, h ▸ x.property⟩ := by
    cases h
    rfl
  have h := absolute_restrict_map_upperRamificationGroupInfinite K L u hu
  have hh := hcast _ _ h (upperRamificationEquivToLimit K L u hu) s
  have hc := congrArg (fun z : T => (z.val (Opposite.op E)).val) hh
  exact hc.trans (upperRamificationEquivToLimit_apply_val K L u hu _ E)

end FontaineWintenberger
