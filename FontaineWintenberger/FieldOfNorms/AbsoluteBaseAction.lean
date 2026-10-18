/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.ActionContinuity
public import FontaineWintenberger.FieldOfNorms.FaithfulAction
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The absolute base action on the original norm field

For a normal intermediate field of the actual separable closure, compose
ordinary Galois restriction with the existing original norm-field action.
The action preserves the original coordinates and valuation, has continuous
orbits, and has exactly the pointwise fixer of the intermediate field as kernel.

This is the restriction to the base norm field in Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The actual absolute Galois group acts on the original norm field through
its ordinary restriction to the given normal APF extension. -/
def FieldOfNorms.absoluteAut :
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →*
      (FieldOfNorms K L ≃+* FieldOfNorms K L) := by
  exact (FieldOfNorms.aut K L).comp (AlgEquiv.restrictNormalHom L)

/-- The absolute base action factors through the actual Galois restriction. -/
@[simp]
theorem FieldOfNorms.absoluteAut_apply (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : FieldOfNorms K L) :
    FieldOfNorms.absoluteAut K L σ x =
      FieldOfNorms.aut K L (AlgEquiv.restrictNormalHom L σ) x := rfl

/-- The original coordinate formula, viewed in the same actual separable closure. -/
theorem coe_fieldOfNormsEval_fieldOfNormsAbsoluteAut
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : FieldOfNorms K L) (E : FiniteIntermediateField K L) :
    ((FieldOfNorms.coord K L E (FieldOfNorms.absoluteAut K L σ x) : L) :
        SeparableClosure K) =
      σ ((FieldOfNorms.coord K L
        (FiniteIntermediateField.map (AlgEquiv.restrictNormalHom L σ).symm.toAlgHom E) x : L) :
          SeparableClosure K) := by
  let τ := AlgEquiv.restrictNormalHom L σ
  change ((FieldOfNorms.coord K L E (FieldOfNorms.map τ x) : L) : SeparableClosure K) = _
  calc
    _ = ((τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.symm.toAlgHom E) x) : L) :
        SeparableClosure K) :=
      congrArg (fun y : L => (y : SeparableClosure K))
        (coe_fieldOfNormsEval_fieldOfNormsMap τ x E)
    _ = _ := AlgEquiv.restrictNormalHom_apply L σ _

/-- Absolute Galois transport preserves the original normalized valuation. -/
theorem FieldOfNorms.absoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.absoluteAut K L σ x) =
      FieldOfNorms.valuation K L x :=
  FieldOfNorms.aut_valuation K (AlgEquiv.restrictNormalHom L σ) x

/-- Every absolute Galois orbit is continuous for the original Krull and
norm-field valuation topologies. -/
theorem continuous_fieldOfNormsAbsoluteAut_apply :
    ∀ x : FieldOfNorms K L,
      Continuous (fun σ : SeparableClosure K ≃ₐ[K] SeparableClosure K =>
        FieldOfNorms.absoluteAut K L σ x) := by
  intro x
  exact (continuous_fieldOfNormsAut_apply K L x).comp
    (InfiniteGalois.restrictNormalHom_continuous L)

/-- The kernel is exactly the original pointwise fixer of the actual field `L`. -/
theorem FieldOfNorms.absoluteAut_ker :
    (FieldOfNorms.absoluteAut K L).ker = L.fixingSubgroup := by
  rw [← L.restrictNormalHom_ker]
  ext σ
  change FieldOfNorms.aut K L (AlgEquiv.restrictNormalHom L σ) = 1 ↔
    AlgEquiv.restrictNormalHom L σ = 1
  constructor
  · intro h
    apply FieldOfNorms.aut_injective K L
    simpa only [_root_.map_one] using h
  · intro h
    rw [h, _root_.map_one]

/-- Extension of actual normal-field automorphisms to the same separable
closure shows that restricting the absolute action does not change its image. -/
theorem FieldOfNorms.absoluteAut_range :
    (FieldOfNorms.absoluteAut K L).range =
      (FieldOfNorms.aut K L).range := by
  ext e
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨AlgEquiv.restrictNormalHom L σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := L) (SeparableClosure K) τ
    exact ⟨σ, congrArg (FieldOfNorms.aut K L) hσ⟩

end FontaineWintenberger
