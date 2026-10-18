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
# Automorphisms of the original separable norm-field union

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
def separableNormUnionEndHom :
    (M →ₐ[L] M) →* (SeparableNormUnion K L M →ₐ[NormLimit K L]
      SeparableNormUnion K L M) := by
  refine { toFun := separableNormUnionAlgMap K L M M
           map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro z
    change separableNormUnionMap K L M M (AlgHom.id L M) z = z
    rw [separableNormUnionMap_id]
    rfl
  · intro s t
    apply AlgHom.ext
    intro z
    change separableNormUnionMap K L M M (s.comp t) z =
      separableNormUnionMap K L M M s
        (separableNormUnionMap K L M M t z)
    exact congrArg (fun f => f z)
      (separableNormUnionMap_comp K L M M t M s).symm

/-- Full faithfulness identifies the original endomorphism monoids. -/
def separableNormUnionEndEquiv :
    (M →ₐ[L] M) ≃* (SeparableNormUnion K L M →ₐ[NormLimit K L]
      SeparableNormUnion K L M) := by
  exact MulEquiv.ofBijective (separableNormUnionEndHom K L M)
    (separableNormUnionAlgMap_bijective K L M M)

/-- The canonical automorphism-group correspondence on the same original fields. -/
def separableNormUnionAutEquiv :
    (M ≃ₐ[L] M) ≃* (SeparableNormUnion K L M ≃ₐ[NormLimit K L]
      SeparableNormUnion K L M) := by
  exact (AlgEquiv.algHomUnitsEquiv L M).symm.trans
    ((Units.mapEquiv (separableNormUnionEndEquiv K L M)).trans
      (AlgEquiv.algHomUnitsEquiv (NormLimit K L)
        (SeparableNormUnion K L M)))

/-- The group correspondence has the actual induced algebra map as its forward map. -/
@[simp]
theorem separableNormUnionAutEquiv_toAlgHom (σ : M ≃ₐ[L] M) :
    (separableNormUnionAutEquiv K L M σ).toAlgHom =
      separableNormUnionAlgMap K L M M σ.toAlgHom := rfl

/-- Evaluation is the same original union embedding. -/
@[simp]
theorem separableNormUnionAutEquiv_apply (σ : M ≃ₐ[L] M)
    (z : SeparableNormUnion K L M) :
    separableNormUnionAutEquiv K L M σ z =
      separableNormUnionMap K L M M σ.toAlgHom z := rfl

/-- On every actual finite original stage the automorphism is literal image transport. -/
theorem separableNormUnionAutEquiv_of (σ : M ≃ₐ[L] M)
    (Q : FiniteLayer L M) (x : NormLimit K Q.val) :
    separableNormUnionAutEquiv K L M σ
        (separableNormUnionOf K L M Q x) =
      separableNormUnionOf K L M (FiniteLayer.map σ.toAlgHom Q)
        (separableNormUnionStageMap K L M M σ.toAlgHom Q x) :=
  separableNormUnionMap_of K L M M σ.toAlgHom Q x

/-- Every original algebra automorphism preserves the compatible rational valuation. -/
theorem separableNormUnionAutEquiv_valuation (σ : M ≃ₐ[L] M)
    (z : SeparableNormUnion K L M) :
    separableNormUnionValuation K L M
        (separableNormUnionAutEquiv K L M σ z) =
      separableNormUnionValuation K L M z :=
  separableNormUnionMap_valuation K L M M σ.toAlgHom z

/-- Every automorphism of the original target union preserves its rational valuation. -/
theorem separableNormUnion_algEquiv_valuation :
    ∀ (σ : SeparableNormUnion K L M ≃ₐ[NormLimit K L]
        SeparableNormUnion K L M)
      (z : SeparableNormUnion K L M),
      separableNormUnionValuation K L M (σ z) =
        separableNormUnionValuation K L M z := by
  intro σ z
  obtain ⟨τ, rfl⟩ := (separableNormUnionAutEquiv K L M).surjective σ
  exact separableNormUnionAutEquiv_valuation K L M τ z

end FontaineWintenberger
