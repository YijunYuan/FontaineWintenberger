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
def normLimitAbsoluteAut :
    letI := normLimitField K L
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →*
      (NormLimit K L ≃+* NormLimit K L) := by
  letI := normLimitField K L
  exact (normLimitAut K L).comp (AlgEquiv.restrictNormalHom L)

/-- The absolute base action factors through the actual Galois restriction. -/
@[simp]
theorem normLimitAbsoluteAut_apply (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : NormLimit K L) :
    letI := normLimitField K L
    normLimitAbsoluteAut K L σ x =
      normLimitAut K L (AlgEquiv.restrictNormalHom L σ) x := rfl

/-- The original coordinate formula, viewed in the same actual separable closure. -/
theorem coe_normLimitEval_normLimitAbsoluteAut
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : NormLimit K L) (E : FiniteLayer K L) :
    letI := normLimitField K L
    ((normLimitEval K L E (normLimitAbsoluteAut K L σ x) : L) :
        SeparableClosure K) =
      σ ((normLimitEval K L
        (FiniteLayer.map (AlgEquiv.restrictNormalHom L σ).symm.toAlgHom E) x : L) :
          SeparableClosure K) := by
  let := normLimitField K L
  let τ := AlgEquiv.restrictNormalHom L σ
  change ((normLimitEval K L E (normLimitMap τ x) : L) : SeparableClosure K) = _
  calc
    _ = ((τ (normLimitEval K L (FiniteLayer.map τ.symm.toAlgHom E) x) : L) :
        SeparableClosure K) :=
      congrArg (fun y : L => (y : SeparableClosure K))
        (coe_normLimitEval_normLimitMap τ x E)
    _ = _ := AlgEquiv.restrictNormalHom_apply L σ _

/-- Absolute Galois transport preserves the original normalized valuation. -/
theorem normLimitAbsoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : NormLimit K L) :
    letI := normLimitField K L
    normLimitValuation K L (normLimitAbsoluteAut K L σ x) =
      normLimitValuation K L x :=
  normLimitAut_valuation K (AlgEquiv.restrictNormalHom L σ) x

/-- Every absolute Galois orbit is continuous for the original Krull and
norm-field valuation topologies. -/
theorem continuous_normLimitAbsoluteAut_apply :
    letI := normLimitField K L
    letI := normLimitValued K L
    ∀ x : NormLimit K L,
      Continuous (fun σ : SeparableClosure K ≃ₐ[K] SeparableClosure K =>
        normLimitAbsoluteAut K L σ x) := by
  let := normLimitField K L
  let := normLimitValued K L
  intro x
  exact (continuous_normLimitAut_apply K L x).comp
    (InfiniteGalois.restrictNormalHom_continuous L)

/-- The kernel is exactly the original pointwise fixer of the actual field `L`. -/
theorem normLimitAbsoluteAut_ker :
    letI := normLimitField K L
    (normLimitAbsoluteAut K L).ker = L.fixingSubgroup := by
  let := normLimitField K L
  rw [← L.restrictNormalHom_ker]
  ext σ
  change normLimitAut K L (AlgEquiv.restrictNormalHom L σ) = 1 ↔
    AlgEquiv.restrictNormalHom L σ = 1
  constructor
  · intro h
    apply normLimitAut_injective K L
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- Extension of actual normal-field automorphisms to the same separable
closure shows that restricting the absolute action does not change its image. -/
theorem normLimitAbsoluteAut_range :
    letI := normLimitField K L
    (normLimitAbsoluteAut K L).range =
      (normLimitAut K L).range := by
  let := normLimitField K L
  ext e
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨AlgEquiv.restrictNormalHom L σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := L) (SeparableClosure K) τ
    exact ⟨σ, congrArg (normLimitAut K L) hσ⟩

end FontaineWintenberger
