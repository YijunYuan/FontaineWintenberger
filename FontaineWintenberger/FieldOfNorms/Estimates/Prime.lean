/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Elementary.NormPrecision
public import FontaineWintenberger.FieldOfNorms.Estimates.Integral
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.BaseChange
public import FontaineWintenberger.Ramification.Upper.Transport

/-!
# Prime-step congruences for the finite-layer integral norms

The spectral integer rings agree with the own-ring constructions.
Their norm maps agree through the field norm, so the proved cyclic
prime congruence applies to the same finite-layer maps used in the norm chain.

## Main results

* `integerNorm_prime_add_congruence_of_bound`: Prime-step congruence for the same finite-layer
  integral norm, with the same intrinsic first bound and the spectral integers.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger.FiniteIntermediateField

variable {K Ω : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [Algebra.IsSeparable K Ω]

local instance primeNorm_completeSpace (E : FiniteIntermediateField K Ω) : CompleteSpace E.val :=
  FiniteDimensional.complete K E.val
local instance primeNorm_discreteValuationRing (E : FiniteIntermediateField K Ω) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val
local instance primeNorm_perfectField (E : FiniteIntermediateField K Ω) : PerfectField
    𝓀[E.val] :=
  Algebra.IsAlgebraic.perfectField 𝓀[K]


/-- Prime-step congruence for the same finite-layer integral norm,
with the same intrinsic first bound and the spectral integers. -/
theorem integerNorm_prime_add_congruence_of_bound
    (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) (p : ℕ) [Fact p.Prime] :
    let F' := IntermediateField.extendScalars hEF
    ∀ (_ : IsGalois E.val F') (_ : Module.finrank E.val F' = p)
      (_ : (IsLocalRing.maximalIdeal (spectralIntegerRing E.val F')).ramificationIdx
        𝒪[E.val] = Module.finrank E.val F')
      (b : ℝ) (_ : (b : EReal) ≤ apfRamificationBound E.val F')
      (x y : spectralIntegerRing K F.val),
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  dsimp only
  intro hgal hd he b hb x y
  let F' := IntermediateField.extendScalars hEF
  let : IsGalois E.val F' := hgal
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  have : IsScalarTower K E.val F' := IsScalarTower.of_algebraMap_eq' rfl
  let : NormedAlgebra K F' := { (inferInstance : Algebra K F') with
    norm_smul_le a z := by
      rw [← IsScalarTower.algebraMap_smul E.val a z]
      simpa only [norm_algebraMap, norm_one, mul_one] using
        norm_smul_le (algebraMap K E.val a) z }
  let T := spectralIntegerRing E.val F'
  let e : spectralIntegerRing K F.val ≃+* T :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      ((spectralIntegerRing_eq_normedUnitBall K F').trans
        (spectralIntegerRing_eq_normedUnitBall E.val F').symm))
  have hc := spectralIntegerRing_prime_norm_add_congruence_of_bound
    E.val F' p hd he b hb (e x) (e y)
  let f : spectralIntegerRing K E.val ≃+*
      𝒪[E.val] :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      (spectralIntegerRing_eq_normedUnitBall K E.val))
  have hnorm (z : spectralIntegerRing K F.val) :
      Algebra.intNorm 𝒪[E.val] T (e z) =
        f (integerNorm E F hEF z) := by
    apply Subtype.ext
    change ((Algebra.intNorm 𝒪[E.val] T (e z)) : E.val)
        =
      ((integerNorm E F hEF z) : E.val)
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm
      (A := 𝒪[E.val])
      (B := T) (K := E.val) (L := F') (e z)
  have hsum :
      Algebra.intNorm 𝒪[E.val] T (e x + e y) =
        f (integerNorm E F hEF (x + y)) :=
    (congrArg (Algebra.intNorm 𝒪[E.val] T)
      (map_add e x y).symm).trans (hnorm (x + y))
  have hdefect := congrArg₂
    (fun a b : 𝒪[E.val] => a - b)
    (congrArg₂ (fun a b : 𝒪[E.val] => a - b)
      hsum (hnorm x)) (hnorm y)
  have hm : f (integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y) ∈
      IsLocalRing.maximalIdeal 𝒪[E.val] ^
        ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
    simpa only [map_sub] using hdefect ▸ hc
  rw [mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv f] at hm
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mpr hm

end FontaineWintenberger.FiniteIntermediateField
