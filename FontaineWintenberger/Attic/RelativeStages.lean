/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Galois.RelAction

/-!
# Relative and ambient transport on the finite stages

For an automorphism fixing the base, the ambient image field and
its norm-family transport are those of the relative union map.

Reference: Wintenberger, Remark 3.2.4, restriction to the relative Galois group.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]

/-- Relative and ambient transport give the identical finite image. -/
theorem RelFieldOfNorms.absoluteLayer_restrictScalars (τ : M ≃ₐ[L] M)
    (N : FiniteIntermediateField L M) :
    RelFieldOfNorms.absoluteLayer K M L (τ.restrictScalars K) N =
      FiniteIntermediateField.map τ.toAlgHom N := by
  apply Subtype.ext
  apply SetLike.ext
  intro z
  rfl

end Fields

section NormFields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (M : Type*) [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Forgetting the base scalars transports each family to the same union element. -/
theorem RelFieldOfNorms.absolute_relative_stage (τ : M ≃ₐ[L] M)
    (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.of K L M
        (RelFieldOfNorms.absoluteLayer K M L (τ.restrictScalars K) N)
        (FieldOfNorms.map (RelFieldOfNorms.absoluteLayerEquiv K M L (τ.restrictScalars K) N) x) =
      RelFieldOfNorms.of K L M (FiniteIntermediateField.map τ.toAlgHom N)
        (FieldOfNorms.map ((FiniteIntermediateField.equivMap τ.toAlgHom N).restrictScalars K) x) :=
            by
  exact RelFieldOfNorms.of_transport_congr K L M
    (RelFieldOfNorms.absoluteLayer K M L (τ.restrictScalars K) N) (FiniteIntermediateField.map
        τ.toAlgHom N)
    (RelFieldOfNorms.absoluteLayerEquiv K M L (τ.restrictScalars K) N)
    ((FiniteIntermediateField.equivMap τ.toAlgHom N).restrictScalars K)
    (RelFieldOfNorms.absoluteLayer_restrictScalars K M L τ N) (fun _ => rfl) x

end NormFields

end FontaineWintenberger
