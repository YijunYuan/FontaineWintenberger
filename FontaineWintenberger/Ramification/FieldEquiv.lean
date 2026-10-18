/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.RingTransport

/-!
# Field isomorphisms and intrinsic ramification

The canonical integral-closure equivalence restricts the original field
isomorphism, and is equivariant for conjugation of actual automorphisms.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

local notation "R₀" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "OM" => spectralIntegerRing K M

/-- A field isomorphism restricts canonically to the actual spectral integer rings. -/
noncomputable def spectralIntegerRingEquiv (f : L ≃ₐ[K] M) : OL ≃ₐ[R₀] OM :=
  ((IsIntegralClosure.equiv R₀ OL L (integralClosure R₀ L)).trans
    (f.restrictScalars R₀).mapIntegralClosure).trans
      (IsIntegralClosure.equiv R₀ (integralClosure R₀ M) M OM)

@[simp]
theorem coe_spectralIntegerRingEquiv (f : L ≃ₐ[K] M) (x : OL) :
    ((spectralIntegerRingEquiv K f x : OM) : M) = f (x : L) := by
  unfold spectralIntegerRingEquiv
  simp only [AlgEquiv.trans_apply]
  rw [show ∀ y : integralClosure R₀ M,
    ((IsIntegralClosure.equiv R₀ (integralClosure R₀ M) M OM y : OM) : M) = (y : M) from
      IsIntegralClosure.algebraMap_equiv R₀ (integralClosure R₀ M) M OM]
  change f (((IsIntegralClosure.equiv R₀ OL L (integralClosure R₀ L)) x :
    integralClosure R₀ L) : L) = f (x : L)
  exact congrArg f (IsIntegralClosure.algebraMap_equiv R₀ OL L (integralClosure R₀ L) x)

/-- The integer-ring equivalence intertwines the original field actions under conjugation. -/
theorem spectralIntegerRingEquiv_smul (f : L ≃ₐ[K] M) (s : L ≃ₐ[K] L) (x : OL) :
    spectralIntegerRingEquiv K f (s • x) = f.autCongr s • spectralIntegerRingEquiv K f x := by
  apply Subtype.ext
  simp only [coe_spectralIntegerRingEquiv, coe_spectralIntegerRing_galois_smul,
    AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

variable [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

theorem spectralIntegerRingEquiv_addVal (f : L ≃ₐ[K] M) (x : OL) :
    IsDiscreteValuationRing.addVal OM (spectralIntegerRingEquiv K f x) =
      IsDiscreteValuationRing.addVal OL x :=
  addVal_ringEquiv (spectralIntegerRingEquiv K f).toRingEquiv x

theorem ramificationOrder_autCongr (f : L ≃ₐ[K] M) (s : L ≃ₐ[K] L) :
    ramificationOrder (R := OM) (M ≃ₐ[K] M) (f.autCongr s) =
      ramificationOrder (R := OL) (L ≃ₐ[K] L) s :=
  ramificationOrder_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) s

theorem herbrandFunction_autCongr (f : L ≃ₐ[K] M) (t : ℝ) :
    herbrandFunction (R := OM) (M ≃ₐ[K] M) t =
      herbrandFunction (R := OL) (L ≃ₐ[K] L) t :=
  herbrandFunction_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) t

theorem upperRamificationGroup_map_autCongr (f : L ≃ₐ[K] M) {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := OL) (L ≃ₐ[K] L) u).map f.autCongr.toMonoidHom =
      upperRamificationGroup (R := OM) (M ≃ₐ[K] M) u :=
  upperRamificationGroup_map_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) hu

end FontaineWintenberger
