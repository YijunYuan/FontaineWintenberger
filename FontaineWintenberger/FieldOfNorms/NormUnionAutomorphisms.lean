/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionHom
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Automorphisms of the original separable relative field of norms

The actual field-of-norms functor identifies algebraic endomorphism monoids.
Passing to their units gives the canonical automorphism-group correspondence,
with the original finite-image formula and rational valuation preservation.

Reference: Wintenberger, Theorem 3.2.2(ii), and its automorphism consequence.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The original union functor preserves the actual endomorphism monoid. -/
def RelFieldOfNorms.endHom :
    (M →ₐ[L] M) →* (RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  refine { toFun := RelFieldOfNorms.algMap K L M M
           map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro z
    change RelFieldOfNorms.map K L M M (AlgHom.id L M) z = z
    rw [RelFieldOfNorms.map_id]
    rfl
  · intro s t
    apply AlgHom.ext
    intro z
    change RelFieldOfNorms.map K L M M (s.comp t) z =
      RelFieldOfNorms.map K L M M s
        (RelFieldOfNorms.map K L M M t z)
    exact congrArg (fun f => f z)
      (RelFieldOfNorms.map_comp K L M M t M s).symm

/-- Full faithfulness identifies the original endomorphism monoids. -/
def RelFieldOfNorms.endEquiv :
    (M →ₐ[L] M) ≃* (RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  exact MulEquiv.ofBijective (RelFieldOfNorms.endHom K L M)
    (RelFieldOfNorms.algMap_bijective K L M M)

/-- The canonical automorphism-group correspondence on the same original fields. -/
def RelFieldOfNorms.autEquiv :
    (M ≃ₐ[L] M) ≃* (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  exact (AlgEquiv.algHomUnitsEquiv L M).symm.trans
    ((Units.mapEquiv (RelFieldOfNorms.endEquiv K L M)).trans
      (AlgEquiv.algHomUnitsEquiv (FieldOfNorms K L)
        (RelFieldOfNorms K L M)))

/-- The group correspondence has the actual induced algebra map as its forward map. -/
@[simp]
theorem RelFieldOfNorms.autEquiv_toAlgHom (σ : M ≃ₐ[L] M) :
    (RelFieldOfNorms.autEquiv K L M σ).toAlgHom =
      RelFieldOfNorms.algMap K L M M σ.toAlgHom := rfl

/-- Evaluation is the same original union embedding. -/
@[simp]
theorem RelFieldOfNorms.autEquiv_apply (σ : M ≃ₐ[L] M)
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.autEquiv K L M σ z =
      RelFieldOfNorms.map K L M M σ.toAlgHom z := rfl

/-- On every actual finite original stage the automorphism is literal image transport. -/
theorem RelFieldOfNorms.autEquiv_of (σ : M ≃ₐ[L] M)
    (Q : FiniteIntermediateField L M) (x : FieldOfNorms K Q.val) :
    RelFieldOfNorms.autEquiv K L M σ
        (RelFieldOfNorms.of K L M Q x) =
      RelFieldOfNorms.of K L M (FiniteIntermediateField.map σ.toAlgHom Q)
        (RelFieldOfNorms.stageMap K L M M σ.toAlgHom Q x) :=
  RelFieldOfNorms.map_of K L M M σ.toAlgHom Q x

/-- Every original algebra automorphism preserves the compatible rational valuation. -/
theorem RelFieldOfNorms.autEquiv_valuation (σ : M ≃ₐ[L] M)
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L M
        (RelFieldOfNorms.autEquiv K L M σ z) =
      RelFieldOfNorms.valuation K L M z :=
  RelFieldOfNorms.map_valuation K L M M σ.toAlgHom z

/-- Every automorphism of the original target union preserves its rational valuation. -/
theorem RelFieldOfNorms._algEquiv_valuation :
    ∀ (σ : RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
        RelFieldOfNorms K L M)
      (z : RelFieldOfNorms K L M),
      RelFieldOfNorms.valuation K L M (σ z) =
        RelFieldOfNorms.valuation K L M z := by
  intro σ z
  obtain ⟨τ, rfl⟩ := (RelFieldOfNorms.autEquiv K L M).surjective σ
  exact RelFieldOfNorms.autEquiv_valuation K L M τ z

end FontaineWintenberger
