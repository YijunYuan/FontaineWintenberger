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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- The original union functor preserves the actual endomorphism monoid. -/
def separableNormUnionEndHom :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    (M →ₐ[L] M) →* (SeparableNormUnion K L M p hL hInfinite →ₐ[NormLimit K L]
      SeparableNormUnion K L M p hL hInfinite) := by
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L M p hL hInfinite
  letI := separableNormUnionAlgebra K L M p hL hInfinite
  refine { toFun := separableNormUnionAlgMap K L M p hL hInfinite M
           map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro z
    change separableNormUnionMap K L M p hL hInfinite M (AlgHom.id L M) z = z
    rw [separableNormUnionMap_id]
    rfl
  · intro s t
    apply AlgHom.ext
    intro z
    change separableNormUnionMap K L M p hL hInfinite M (s.comp t) z =
      separableNormUnionMap K L M p hL hInfinite M s
        (separableNormUnionMap K L M p hL hInfinite M t z)
    exact congrArg (fun f => f z)
      (separableNormUnionMap_comp K L M p hL hInfinite M t M s).symm

/-- Full faithfulness identifies the original endomorphism monoids. -/
def separableNormUnionEndEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    (M →ₐ[L] M) ≃* (SeparableNormUnion K L M p hL hInfinite →ₐ[NormLimit K L]
      SeparableNormUnion K L M p hL hInfinite) := by
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L M p hL hInfinite
  letI := separableNormUnionAlgebra K L M p hL hInfinite
  exact MulEquiv.ofBijective (separableNormUnionEndHom K L M p hL hInfinite)
    (separableNormUnionAlgMap_bijective K L M p hL hInfinite M)

/-- The canonical automorphism-group correspondence on the same original fields. -/
def separableNormUnionAutEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    (M ≃ₐ[L] M) ≃* (SeparableNormUnion K L M p hL hInfinite ≃ₐ[NormLimit K L]
      SeparableNormUnion K L M p hL hInfinite) := by
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L M p hL hInfinite
  letI := separableNormUnionAlgebra K L M p hL hInfinite
  exact (AlgEquiv.algHomUnitsEquiv L M).symm.trans
    ((Units.mapEquiv (separableNormUnionEndEquiv K L M p hL hInfinite)).trans
      (AlgEquiv.algHomUnitsEquiv (NormLimit K L)
        (SeparableNormUnion K L M p hL hInfinite)))

/-- The group correspondence has the actual induced algebra map as its forward map. -/
@[simp]
theorem separableNormUnionAutEquiv_toAlgHom (σ : M ≃ₐ[L] M) :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    (separableNormUnionAutEquiv K L M p hL hInfinite σ).toAlgHom =
      separableNormUnionAlgMap K L M p hL hInfinite M σ.toAlgHom := rfl

/-- Evaluation is the same original union embedding. -/
@[simp]
theorem separableNormUnionAutEquiv_apply (σ : M ≃ₐ[L] M)
    (z : SeparableNormUnion K L M p hL hInfinite) :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    separableNormUnionAutEquiv K L M p hL hInfinite σ z =
      separableNormUnionMap K L M p hL hInfinite M σ.toAlgHom z := rfl

/-- On every actual finite original stage the automorphism is literal image transport. -/
theorem separableNormUnionAutEquiv_of (σ : M ≃ₐ[L] M)
    (Q : FiniteLayer L M) (x : NormLimit K Q.val) :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    separableNormUnionAutEquiv K L M p hL hInfinite σ
        (separableNormUnionOf K L M p hL hInfinite Q x) =
      separableNormUnionOf K L M p hL hInfinite (FiniteLayer.map σ.toAlgHom Q)
        (separableNormUnionStageMap K L M p hL hInfinite M σ.toAlgHom Q x) :=
  separableNormUnionMap_of K L M p hL hInfinite M σ.toAlgHom Q x

/-- Every original algebra automorphism preserves the compatible rational valuation. -/
theorem separableNormUnionAutEquiv_valuation (σ : M ≃ₐ[L] M)
    (z : SeparableNormUnion K L M p hL hInfinite) :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    separableNormUnionValuation K L M p hL hInfinite
        (separableNormUnionAutEquiv K L M p hL hInfinite σ z) =
      separableNormUnionValuation K L M p hL hInfinite z :=
  separableNormUnionMap_valuation K L M p hL hInfinite M σ.toAlgHom z

/-- Every automorphism of the original target union preserves its rational valuation. -/
theorem separableNormUnion_algEquiv_valuation :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    ∀ (σ : SeparableNormUnion K L M p hL hInfinite ≃ₐ[NormLimit K L]
        SeparableNormUnion K L M p hL hInfinite)
      (z : SeparableNormUnion K L M p hL hInfinite),
      separableNormUnionValuation K L M p hL hInfinite (σ z) =
        separableNormUnionValuation K L M p hL hInfinite z := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  intro σ z
  obtain ⟨τ, rfl⟩ := (separableNormUnionAutEquiv K L M p hL hInfinite).surjective σ
  exact separableNormUnionAutEquiv_valuation K L M p hL hInfinite τ z

end FontaineWintenberger
