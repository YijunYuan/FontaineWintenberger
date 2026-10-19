/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Residue

/-!
# The residue field of the field of norms through a deep layer

A second identification `𝓀[X_K(L)] ≃+* 𝓀[L]`, obtained by composing the coordinate reduction
`FieldOfNorms.residueLayerEquiv` at the APF residue layer with `integralClosureResidueEquiv`.
The library uses `FieldOfNorms.residueEquiv` (induced by the constants `residueConstants`) instead;
this version is kept for comparison and has no downstream use.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Above the proved APF residue-stable layer, coordinate reduction
identifies the field of norms residue field with the intrinsic residue
field of the canonical integral closure in the extension. -/
def FieldOfNorms.residueLayerComposite :
    IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField
        (integralClosure 𝒪[K] L) := by
  let T := apfResidueLayer K L
  let E := deepFiniteTower K L T 0
  exact (FieldOfNorms.residueLayerEquiv K L T).trans
    (integralClosureResidueEquiv K L E
      (le_deepFiniteTower K L T 0)).toRingEquiv

/-- On residues of integral norm families, the intrinsic residue
isomorphism is the finite residue inclusion after coordinate reduction. -/
@[simp]
theorem FieldOfNorms.residueLayerComposite_residue :
    ∀ α : (FieldOfNorms.fieldValuation K L).valuationSubring,
    FieldOfNorms.residueLayerComposite K L (IsLocalRing.residue _ α) =
      integralClosureResidueFromLayer K L
        (deepFiniteTower K L (apfResidueLayer K L) 0)
        (IsLocalRing.residue _ (FieldOfNorms.integralCoordinate K L
          (apfResidueLayer K L) α 0)) := by
  intro α
  rfl


end FontaineWintenberger

end
