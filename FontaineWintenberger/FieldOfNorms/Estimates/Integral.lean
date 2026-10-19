/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Norm.Tower

/-!
# Integral norms on all finite intermediate fields

The canonical field norms restrict to the spectral integer rings.
Their original-field computation proves identity and composition without
introducing another inverse-limit carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger.FiniteIntermediateField

attribute [local instance] FractionRing.liftAlgebra

variable {K Ω : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω]

local notation "R₀" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The integral norm for an inclusion of finite intermediate fields. -/
def integerNorm (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) :
    spectralIntegerRing K F.val →* spectralIntegerRing K E.val := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  exact Algebra.intNorm (spectralIntegerRing K E.val) (spectralIntegerRing K F.val)

/-- The integral norm is the field norm under inclusion. -/
@[simp]
theorem coe_integerNorm (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F)
    (x : spectralIntegerRing K F.val) :
    (integerNorm E F hEF x : E.val) = norm E F hEF (x : F.val) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  exact Algebra.algebraMap_intNorm (A := spectralIntegerRing K E.val)
    (B := spectralIntegerRing K F.val) (K := E.val) (L := F.val) x

/-- The integral norm of the identity field inclusion is the identity. -/
@[simp]
theorem integerNorm_self (E : FiniteIntermediateField K Ω) (x : spectralIntegerRing K E.val) :
    integerNorm E E le_rfl x = x := by
  apply Subtype.ext
  rw [coe_integerNorm, norm_self]

/-- Integral norms compose because their field norms compose. -/
theorem integerNorm_integerNorm (E F G : FiniteIntermediateField K Ω)
    (hEF : E ≤ F) (hFG : F ≤ G) (x : spectralIntegerRing K G.val) :
    integerNorm E F hEF (integerNorm F G hFG x) = integerNorm E G (hEF.trans hFG) x := by
  apply Subtype.ext
  simp only [coe_integerNorm]
  exact norm_norm E F G hEF hFG (x : G.val)

/-- The integral norm preserves every nonnegative maximal-ideal
precision, on all finite separable layers including nonnormal ones. -/
theorem integerNorm_mem_maximalIdeal_pow (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F)
    {r : ℕ} {x : spectralIntegerRing K F.val}
    (hx : x ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r) :
    integerNorm E F hEF x ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have : Algebra.IsSeparable (FractionRing (spectralIntegerRing K E.val))
      (FractionRing (spectralIntegerRing K F.val)) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (spectralIntegerRing K E.val) E.val).symm.toRingEquiv
      (FractionRing.algEquiv (spectralIntegerRing K F.val) F.val).symm.toRingEquiv
    ext y
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv (spectralIntegerRing K E.val) E.val).symm
      (FractionRing.algEquiv (spectralIntegerRing K F.val) F.val).symm y
  exact intNorm_mem_maximalIdeal_pow
    (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) hx

/-- The integral norm addition congruence composes in a finite-layer
triple, consuming the proved integral-norm tower theorem. -/
theorem integerNorm_add_congruence_tower (E F G : FiniteIntermediateField K Ω)
    (hEF : E ≤ F) (hFG : F ≤ G) {r : ℕ}
    (hE : ∀ x y : spectralIntegerRing K F.val,
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r)
    (hF : ∀ x y : spectralIntegerRing K G.val,
      integerNorm F G hFG (x + y) - integerNorm F G hFG x - integerNorm F G hFG y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r)
    (x y : spectralIntegerRing K G.val) :
    integerNorm E G (hEF.trans hFG) (x + y) - integerNorm E G (hEF.trans hFG) x -
      integerNorm E G (hEF.trans hFG) y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
  let : Algebra E.val G.val :=
    (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K E.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E.val F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := spectralValuation_hasExtension_tower K (E := F.val) (L := G.val)
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := G.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K F.val) (spectralValuation K G.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (spectralValuation K E.val) (spectralValuation K F.val) (spectralValuation K G.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  have : Module.Finite (spectralIntegerRing K F.val) (spectralIntegerRing K G.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have : Algebra.IsSeparable (FractionRing (spectralIntegerRing K E.val))
      (FractionRing (spectralIntegerRing K F.val)) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (spectralIntegerRing K E.val) E.val).symm.toRingEquiv
      (FractionRing.algEquiv (spectralIntegerRing K F.val) F.val).symm.toRingEquiv
    ext z
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv (spectralIntegerRing K E.val) E.val).symm
      (FractionRing.algEquiv (spectralIntegerRing K F.val) F.val).symm z
  exact intNorm_add_congruence_tower (spectralIntegerRing K E.val)
    (spectralIntegerRing K F.val) (spectralIntegerRing K G.val) hE hF x y

/-- Norm congruences at a common precision compose along an
finite chain of intermediate fields. -/
theorem integerNorm_add_congruence_of_chain (r : ℕ) (E F : FiniteIntermediateField K Ω)
    (hchain : Relation.ReflTransGen
      (fun A B : FiniteIntermediateField K Ω => ∃ hAB : A ≤ B,
        ∀ x y : spectralIntegerRing K B.val,
          integerNorm A B hAB (x + y) - integerNorm A B hAB x - integerNorm A B hAB y ∈
            IsLocalRing.maximalIdeal (spectralIntegerRing K A.val) ^ r) E F) :
    ∃ hEF : E ≤ F, ∀ x y : spectralIntegerRing K F.val,
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ r := by
  induction hchain with
  | refl =>
      refine ⟨le_rfl, fun x y => ?_⟩
      simp only [integerNorm_self, add_sub_cancel_left, sub_self, Ideal.zero_mem]
  | @tail F G hchain hstep ih =>
      obtain ⟨hEF, hE⟩ := ih
      obtain ⟨hFG, hF⟩ := hstep
      exact ⟨hEF.trans hFG, integerNorm_add_congruence_tower E F G hEF hFG hE hF⟩

end FontaineWintenberger.FiniteIntermediateField
