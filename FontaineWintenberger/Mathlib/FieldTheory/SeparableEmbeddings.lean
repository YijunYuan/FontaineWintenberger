/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Extension of embeddings in the separable closure

The canonical normal-extension lifting theorem gives automorphisms
extending embeddings of intermediate fields. Separably closed targets receive
every separable algebraic extension through the existing lifting theorem.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- An embedding of an intermediate field extends to an
automorphism of the normal algebraic ambient field. -/
theorem exists_aut_extends_intermediate_embedding (K Ω : Type*) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω] (S : IntermediateField K Ω) (i : S →ₐ[K] Ω) :
    ∃ σ : Ω ≃ₐ[K] Ω, ∀ x : S, σ (x : Ω) = i x := by
  let σ := AlgEquiv.ofBijective (i.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _)
  refine ⟨σ, fun x => ?_⟩
  exact i.liftNormal_commutes Ω x

/-- The preceding extension theorem applies to the canonical separable
closure without a supplied normality or extension certificate. -/
theorem exists_aut_extends_separableClosure_embedding (K : Type*) [Field K]
    (S : IntermediateField K (SeparableClosure K)) (i : S →ₐ[K] SeparableClosure K) :
    ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      ∀ x : S, σ (x : SeparableClosure K) = i x :=
  exists_aut_extends_intermediate_embedding K (SeparableClosure K) S i

/-- Every separable algebraic extension embeds into any separably closed
extension of its base. -/
theorem nonempty_separablyClosed_embeddings (K L Ω : Type*) [Field K] [Field L]
    [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra.IsSeparable K L] [IsSepClosed Ω] :
    Nonempty (L →ₐ[K] Ω) := ⟨IsSepClosed.lift⟩

end FontaineWintenberger
