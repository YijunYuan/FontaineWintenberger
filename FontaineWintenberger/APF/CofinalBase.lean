/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseClosure
public import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Cofinal finite Galois layers after finite base change

Normal closure is taken inside the actual separable closure. Changing the
base preserves the actual carrier of a finite intermediate field containing the new base.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [Field K]

/-- The actual finite normal closure of a finite separable subextension. -/
noncomputable def finiteGaloisNormalClosure
    (D : IntermediateField K (SeparableClosure K)) [FiniteDimensional K D] :
    FiniteGaloisIntermediateField K (SeparableClosure K) :=
  { IntermediateField.normalClosure K D (SeparableClosure K) with }

/-- The normal closure contains the actual original field. -/
theorem le_finiteGaloisNormalClosure
    (D : IntermediateField K (SeparableClosure K)) [FiniteDimensional K D] :
    D ≤ (finiteGaloisNormalClosure K D).toIntermediateField :=
  IntermediateField.le_normalClosure D

variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- Finite Galois layers over the new base lie in actual finite Galois layers over the old base. -/
theorem exists_finiteGalois_over_base_layer
    (D : FiniteGaloisIntermediateField M (SeparableClosure K)) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      M ≤ E.toIntermediateField ∧ D.toIntermediateField.restrictScalars K ≤ E.toIntermediateField :=
          by
  let : FiniteDimensional K D := FiniteDimensional.trans K M D
  let S := D.toIntermediateField.restrictScalars K
  let : FiniteDimensional K S := inferInstanceAs (FiniteDimensional K D)
  refine ⟨finiteGaloisNormalClosure K S, ?_, le_finiteGaloisNormalClosure K S⟩
  have hMD : M ≤ S := fun x hx => D.toIntermediateField.algebraMap_mem ⟨x, hx⟩
  exact hMD.trans (le_finiteGaloisNormalClosure K S)

/-- The old-base finite Galois layers containing the new base are cofinal on the old-base side. -/
theorem exists_finiteGalois_containing_base
    (D : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      M ≤ E.toIntermediateField ∧ D ≤ E := by
  let E := finiteGaloisNormalClosure K M ⊔ D
  refine ⟨E, (le_finiteGaloisNormalClosure K M).trans ?_, le_sup_right⟩
  exact le_sup_left

/-- An actual finite old-base Galois layer is finite Galois over every contained base. -/
noncomputable def finiteGaloisLayerOverBase
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : M ≤ E.toIntermediateField) :
    FiniteGaloisIntermediateField M (SeparableClosure K) := by
  let S := IntermediateField.extendScalars hME
  letI : Algebra K S := inferInstanceAs (Algebra K (S.restrictScalars K))
  letI : IsScalarTower K M S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : FiniteDimensional K S := inferInstanceAs (FiniteDimensional K E)
  letI : FiniteDimensional M S := Module.Finite.right K M S
  letI : IsGalois K (S.restrictScalars K) := by
    change IsGalois K E
    infer_instance
  letI : IsGalois K S := inferInstanceAs (IsGalois K (S.restrictScalars K))
  letI : IsGalois M S := IsGalois.tower_top_of_isGalois K M S
  exact { S with }

omit [FiniteDimensional K M] in
/-- Rebasing a finite intermediate field keeps its actual ambient field. -/
theorem finiteGaloisLayerOverBase_restrictScalars
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : M ≤ E.toIntermediateField) :
    (finiteGaloisLayerOverBase K M E hME).toIntermediateField.restrictScalars K =
      E.toIntermediateField := rfl

end FontaineWintenberger
