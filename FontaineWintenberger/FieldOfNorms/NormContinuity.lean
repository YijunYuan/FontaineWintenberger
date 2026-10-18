/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.WildNorms
public import FontaineWintenberger.Ramification.NormContinuity
public import FontaineWintenberger.APF.AbstractFiniteBase

/-!
# Actual finite-layer norm continuity at Herbrand precision

Prime norm continuity transports to the original finite-layer integer norms.
The actual inverse Herbrand functions compose in the same original towers,
so their proved moduli compose along the actual wild prime chains.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

private theorem norm_sub_mem_pow_of_commutes
    {R S T U : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Monoid T] [Monoid U]
    (f : R ≃+* S) (N : T →* R) (N' : U →* S) (e : T → U)
    (hN : ∀ z, N' (e z) = f (N z)) (r : ℕ) (x y : T)
    (h : N' (e x) - N' (e y) ∈ IsLocalRing.maximalIdeal S ^ r) :
    N x - N y ∈ IsLocalRing.maximalIdeal R ^ r := by
  rw [hN x, hN y, ← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv] at h
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mpr h

section HerbrandTowers

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
variable (N : Type*) [Field N] [Algebra K N] [Algebra M N]
    [IsScalarTower K M N] [FiniteDimensional K N] [Algebra.IsSeparable K N]

/-- The actual Herbrand moduli compose on the original finite normed bases,
in the reverse order to their actual inverse Herbrand functions. -/
theorem apfPhi_finiteBase_comp_of_normedAlgebra (r : ℝ) :
    letI := normedAlgebra_isCompleteDiscreteValuedField K M
    letI := normedAlgebra_residueField_perfectField K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI : FiniteDimensional M N := Module.Finite.right K M N
    apfPhi K M
        (apfPhi M N r) =
      apfPhi K N r := by
  let := normedAlgebra_isCompleteDiscreteValuedField K M
  let := normedAlgebra_residueField_perfectField K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M N
  let : FiniteDimensional M N := Module.Finite.right K M N
  apply (IsAPF.strictMono_apfPsi K N).injective
  calc
    _ = apfPsi M N (apfPsi K M
        (apfPhi K M
          (apfPhi M N r))) :=
      (IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K M N _).symm
    _ = r := by rw [apfPsi_apfPhi, apfPsi_apfPhi]
    _ = _ := (apfPsi_apfPhi K N r).symm

end HerbrandTowers

namespace FiniteLayer

variable {K Ω : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [Algebra.IsSeparable K Ω]

local instance (E : FiniteLayer K Ω) : CompleteSpace E.val := FiniteDimensional.complete K E.val
local instance (E : FiniteLayer K Ω) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val
local instance (E : FiniteLayer K Ω) : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := E.val)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K E.val

/-- Prime Herbrand continuity applies to the same original finite-layer
norm maps and integer rings used by the actual inverse system. -/
theorem integerNorm_prime_sub_congruence
    (E F : FiniteLayer K Ω) (hEF : E ≤ F) (p : ℕ) [Fact p.Prime] :
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    haveI : IsAPF E.val F' := isAPF_of_finite E.val F'
    ∀ (_ : IsGalois E.val F') (_ : Module.finrank E.val F' = p)
      (_ : (IsLocalRing.maximalIdeal (spectralIntegerRing E.val F')).ramificationIdx
        (NormedField.valuation (K := E.val)).valuationSubring = Module.finrank E.val F')
      (r : ℕ) (x y : spectralIntegerRing K F.val),
      x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r →
        integerNorm E F hEF x - integerNorm E F hEF y ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
            ⌈apfPhi E.val F' (r : ℝ)⌉₊ := by
  dsimp only
  intro hgal hd he r x y hxy
  let F' := IntermediateField.extendScalars hEF
  let : IsGalois E.val F' := hgal
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  have : IsScalarTower K E.val F' := IsScalarTower.of_algebraMap_eq' rfl
  let T := spectralIntegerRing E.val F'
  let e : spectralIntegerRing K F.val ≃+* T :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      ((spectralIntegerRing_eq_normedUnitBall K F.val).trans
        (spectralIntegerRing_eq_normedUnitBall E.val F').symm))
  have hxy' : e x - e y ∈ IsLocalRing.maximalIdeal T ^ r := by
    rw [← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv]
    exact (mem_maximalIdeal_pow_iff_addVal _ _).mp hxy
  have hp : (Module.finrank E.val F').Prime := hd.symm ▸ (Fact.out : p.Prime)
  let s : ℕ := ⌈apfPhi E.val F' (r : ℝ)⌉₊
  have hc : Algebra.intNorm (NormedField.valuation (K := E.val)).valuationSubring T (e x) -
      Algebra.intNorm (NormedField.valuation (K := E.val)).valuationSubring T (e y) ∈
      IsLocalRing.maximalIdeal (NormedField.valuation (K := E.val)).valuationSubring ^ s :=
    spectralIntegerRing_prime_norm_sub_congruence E.val F' hp he r (e x) (e y) hxy'
  let f : spectralIntegerRing K E.val ≃+*
      (NormedField.valuation (K := E.val)).valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      (spectralIntegerRing_eq_normedUnitBall K E.val))
  have hnorm (z : spectralIntegerRing K F.val) :
      Algebra.intNorm (NormedField.valuation (K := E.val)).valuationSubring T (e z) =
        f (integerNorm E F hEF z) := by
    apply Subtype.ext
    change ((Algebra.intNorm (NormedField.valuation (K := E.val)).valuationSubring T (e z)) : E.val)
        =
      ((integerNorm E F hEF z) : E.val)
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm
      (A := (NormedField.valuation (K := E.val)).valuationSubring)
      (B := T) (K := E.val) (L := F') (e z)
  exact norm_sub_mem_pow_of_commutes f (integerNorm E F hEF)
    (Algebra.intNorm (NormedField.valuation (K := E.val)).valuationSubring T) e hnorm s x y hc

/-- Actual Herbrand moduli compose through the original inclusions of
three finite layers, with all relative scalar structures explicitly fixed. -/
theorem apfPhi_tower (E F G : FiniteLayer K Ω) (hEF : E ≤ F) (hFG : F ≤ G) (r : ℝ) :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
    letI : Algebra E.val G.val := (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K E.val G.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower E.val F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
    letI : FiniteDimensional E.val G.val := Module.Finite.right K E.val G.val
    letI : FiniteDimensional F.val G.val := Module.Finite.right K F.val G.val
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E.val G.val
    letI := Algebra.isSeparable_tower_top_of_isSeparable K F.val G.val
    apfPhi E.val F.val
        (apfPhi F.val G.val r) =
      apfPhi E.val G.val r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
  let : Algebra E.val G.val := (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K E.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E.val F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : FiniteDimensional E.val G.val := Module.Finite.right K E.val G.val
  have : FiniteDimensional F.val G.val := Module.Finite.right K F.val G.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val G.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K F.val G.val
  let : NormedAlgebra E.val F.val := { (inferInstance : Algebra E.val F.val) with
    norm_smul_le a b := by
      change ‖(a : Ω) * (b : Ω)‖ ≤ ‖(a : Ω)‖ * ‖(b : Ω)‖
      exact norm_mul_le _ _ }
  exact apfPhi_finiteBase_comp_of_normedAlgebra E.val F.val G.val r

end FiniteLayer

end FontaineWintenberger
