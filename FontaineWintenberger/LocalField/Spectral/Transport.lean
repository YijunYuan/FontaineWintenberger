/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Spectral.Uniqueness

/-!
# Transport between equal valuation subrings

Two equal valuation subrings of `L` over `𝒪[K]` are identified by the identity of `L`, as
`𝒪[K]`-algebras.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
variable [(NormedField.valuation (K := K)).HasExtension w]

/-- The identity of `L` as an `𝒪[K]`-algebra isomorphism between equal valuation subrings. -/
noncomputable def spectralIntegerRingAlgEquivOfEq
    (h : spectralIntegerRing K L = w.valuationSubring) :
    spectralIntegerRing K L ≃ₐ[𝒪[K]] w.valuationSubring :=
  let e : spectralIntegerRing K L ≃+* w.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring h)
  { e with commutes' a := by apply Subtype.ext; rfl }

end FontaineWintenberger
