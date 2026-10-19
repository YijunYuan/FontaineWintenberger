/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Mathlib.Analysis.SpectralIntegers
public import FontaineWintenberger.Ramification.Lower.Basic

/-!
# The full automorphism action on the actual spectral integer ring

The proved equality of the decomposition group with the full automorphism
group transports the intrinsic action, lower groups and order without changing
any ambient field automorphism or integral displacement.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "D" => ValuationSubring.decompositionSubgroup K (spectralIntegerRing K L)

/-- Inclusion identifies the spectral decomposition subgroup with the full group. -/
noncomputable def spectralDecompositionEquiv : D ≃* (L ≃ₐ[K] L) where
  toFun := Subtype.val
  invFun g := ⟨g, by rw [spectralIntegerRing_decompositionSubgroup]; trivial⟩
  left_inv g := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable instance spectralIntegerRing_galoisAction : MulSemiringAction (L ≃ₐ[K] L) OL :=
  MulSemiringAction.compHom OL (spectralDecompositionEquiv K L).symm.toMonoidHom

@[simp]
theorem coe_spectralIntegerRing_galois_smul (g : L ≃ₐ[K] L) (x : OL) :
    ((g • x : OL) : L) = g (x : L) := rfl

instance spectralIntegerRing_galois_faithfulSMul : FaithfulSMul (L ≃ₐ[K] L) OL where
  eq_of_smul_eq_smul h := by
    have : FaithfulSMul D OL := ValuationSubring.decompositionSubgroup_faithfulSMul K OL
    apply (spectralDecompositionEquiv K L).symm.injective
    exact FaithfulSMul.eq_of_smul_eq_smul (α := OL) h

instance spectralIntegerRing_galois_smulCommClass : SMulCommClass (L ≃ₐ[K] L) OK OL where
  smul_comm g r x := by
    apply Subtype.ext
    change g ((r : K) • (x : L)) = (r : K) • g (x : L)
    exact map_smul g (r : K) (x : L)

variable [IsDiscreteValuationRing (spectralIntegerRing K L)]

omit [IsDiscreteValuationRing (spectralIntegerRing K L)] in
theorem spectralIntegerRing_galois_mem_lower_iff (n : ℤ) (g : L ≃ₐ[K] L) :
    g ∈ lowerRamificationGroup (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal OL) n ↔
      (spectralDecompositionEquiv K L).symm g ∈ (OL).lowerRamificationGroup K n := Iff.rfl

theorem spectralIntegerRing_galois_order (g : L ≃ₐ[K] L) :
    ramificationOrder (R := OL) (L ≃ₐ[K] L) g =
      (OL).ramificationOrder K ((spectralDecompositionEquiv K L).symm g) := rfl

theorem spectralIntegerRing_galois_normalizedValuation (g : L ≃ₐ[K] L) (x : L) :
    (IsDiscreteValuationRing.maximalIdeal OL).valuation L (g x) =
      (IsDiscreteValuationRing.maximalIdeal OL).valuation L x :=
  ValuationSubring.normalizedValuation_apply OL K ((spectralDecompositionEquiv K L).symm g) x

end FontaineWintenberger
