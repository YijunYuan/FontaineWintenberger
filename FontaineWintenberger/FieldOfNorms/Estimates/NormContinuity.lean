/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Estimates.Wild
public import FontaineWintenberger.APF.Elementary.NormContinuity
public import FontaineWintenberger.APF.BaseChange.Strict

/-!
# Norm continuity at Herbrand precision

## Actual finite-layer norm continuity at Herbrand precision

Prime norm continuity transports to the original finite-layer integer norms.
The actual inverse Herbrand functions compose in the same original towers,
so their proved moduli compose along the actual wild prime chains.

## Herbrand norm continuity on the actual wild finite tower

The actual cyclic prime field chain supplies every step. Composing its
proved norm moduli and actual Herbrand functions gives continuity for the
original finite-layer norm, without a continuity hypothesis in the endpoint.
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

namespace FiniteIntermediateField

variable {K Ω : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [Algebra.IsSeparable K Ω]

local instance (E : FiniteIntermediateField K Ω) : CompleteSpace E.val :=
    FiniteDimensional.complete K E.val
local instance (E : FiniteIntermediateField K Ω) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val
local instance (E : FiniteIntermediateField K Ω) : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := E.val)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K E.val

/-- Prime Herbrand continuity applies to the same original finite-layer
norm maps and integer rings used by the actual inverse system. -/
theorem integerNorm_prime_sub_congruence
    (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) (p : ℕ) [Fact p.Prime] :
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
three finite intermediate fields, with all relative scalar structures explicitly fixed. -/
theorem apfPhi_tower (E F G : FiniteIntermediateField K Ω) (hEF : E ≤ F) (hFG : F ≤ G) (r : ℝ) :
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

end FiniteIntermediateField

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger.FiniteIntermediateField

variable {K Ω : Type*} [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [Algebra.IsSeparable K Ω]

local instance (E : FiniteIntermediateField K Ω) : CompleteSpace E.val :=
    FiniteDimensional.complete K E.val
local instance (E : FiniteIntermediateField K Ω) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val
local instance (E : FiniteIntermediateField K Ω) : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := E.val)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K E.val

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] [IsUltrametricDist Ω] in
/-- The same original integral norms compose arbitrary proved input and
output precisions through an actual triple of finite fields. -/
theorem integerNorm_sub_congruence_tower (E F G : FiniteIntermediateField K Ω)
    (hEF : E ≤ F) (hFG : F ≤ G) (r s t : ℕ)
    (hE : ∀ x y : spectralIntegerRing K F.val,
      x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s →
        integerNorm E F hEF x - integerNorm E F hEF y ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ t)
    (hF : ∀ x y : spectralIntegerRing K G.val,
      x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K G.val) ^ r →
        integerNorm F G hFG x - integerNorm F G hFG y ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s)
    (x y : spectralIntegerRing K G.val)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K G.val) ^ r) :
    integerNorm E G (hEF.trans hFG) x - integerNorm E G (hEF.trans hFG) y ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ t := by
  simpa only [integerNorm_integerNorm] using
    hE (integerNorm F G hFG x) (integerNorm F G hFG y) (hF x y hxy)

private def finitePhi (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) (r : ℝ) : ℝ := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  exact apfPhi E.val F.val r

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem finitePhi_self (E : FiniteIntermediateField K Ω) (r : ℝ) :
    finitePhi E E le_rfl r = r := by
  change apfPhi E.val E.val r = r
  exact apfPhi_eq_self_of_bound_eq_top E.val E.val (apfRamificationBound_self E.val) r

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem finitePhi_eq_extendScalars (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) (r :
    ℝ) :
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    finitePhi E F hEF r = apfPhi E.val F' r := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  let F' := IntermediateField.extendScalars hEF
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  let e : F.val ≃ₐ[E.val] F' :=
    { RingEquiv.refl F.val with commutes' := fun _ => rfl }
  exact apfPhi_algEquiv E.val F.val e r

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem finitePhi_mono (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F) :
    Monotone (finitePhi E F hEF) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  exact (strictMono_apfPhi E.val F.val).monotone

private theorem finitePhi_comp (E F G : FiniteIntermediateField K Ω)
    (hEF : E ≤ F) (hFG : F ≤ G) (r : ℝ) :
    finitePhi E F hEF (finitePhi F G hFG r) = finitePhi E G (hEF.trans hFG) r := by
  exact apfPhi_tower E F G hEF hFG r

variable [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "P" => lowerRamificationGroup (Ω ≃ₐ[K] Ω)
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1

/-- The original norm on every actual finite step above wild inertia has
its intrinsic Herbrand modulus. Each cyclic prime step and its total
ramification are produced by the actual field chain. -/
theorem integerNorm_sub_congruence_of_wild_field (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F)
    (hE : IntermediateField.fixedField P ≤ E.val) :
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    ∀ (r : ℕ) (x y : spectralIntegerRing K F.val),
      x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r →
        integerNorm E F hEF x - integerNorm E F hEF y ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
            ⌈apfPhi E.val F' (r : ℝ)⌉₊ := by
  dsimp only
  intro r x y hxy
  have hfix : E.val.fixingSubgroup ≤ P := by
    simpa only [IntermediateField.fixingSubgroup_fixedField] using
      IntermediateField.fixingSubgroup_le hE
  have hpgroup : IsPGroup p E.val.fixingSubgroup :=
    (lowerRamificationGroup_one_isPGroup (Ω ≃ₐ[K] Ω) p).of_injective
      (Subgroup.inclusion hfix) (Subgroup.inclusion_injective _)
  have hchain := relative_prime_field_chain K Ω p E.val F.val hEF hpgroup
  have hmain : ∀ (A : IntermediateField K Ω),
      Relation.ReflTransGen
        (fun A B : IntermediateField K Ω => ∃ hAB : A ≤ B,
          IsGalois A (IntermediateField.extendScalars hAB) ∧
          Module.finrank A (IntermediateField.extendScalars hAB) = p ∧
          IsCyclic ((IntermediateField.extendScalars hAB) ≃ₐ[A]
            IntermediateField.extendScalars hAB)) A F.val →
      E.val ≤ A → ∃ hAF : A ≤ F.val,
        ∀ (r : ℕ) (x y : spectralIntegerRing K F.val),
          x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r →
            integerNorm ⟨A, inferInstance⟩ F hAF x - integerNorm ⟨A, inferInstance⟩ F hAF y ∈
              IsLocalRing.maximalIdeal (spectralIntegerRing K A) ^
                ⌈finitePhi ⟨A, inferInstance⟩ F hAF (r : ℝ)⌉₊ := by
    intro A hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro _
        refine ⟨le_rfl, fun r x y hxy => ?_⟩
        simpa only [integerNorm_self, finitePhi_self, Nat.ceil_natCast] using hxy
    | @head A B hstep hc ih =>
        intro hEA
        obtain ⟨hAB, hg, hd, _⟩ := hstep
        obtain ⟨hBF, htail⟩ := ih (hEA.trans hAB)
        have he := wildField_step_ramificationIdx_eq_finrank K Ω A B hAB (hE.trans hEA)
        let A' : FiniteIntermediateField K Ω := ⟨A, inferInstance⟩
        let B' : FiniteIntermediateField K Ω := ⟨B, inferInstance⟩
        refine ⟨hAB.trans hBF, fun r x y hxy => ?_⟩
        let q : ℕ := ⌈finitePhi B' F hBF (r : ℝ)⌉₊
        have hprime (u v : spectralIntegerRing K B) (huv :
            u - v ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K B) ^ q) :
            integerNorm A' B' hAB u - integerNorm A' B' hAB v ∈
              IsLocalRing.maximalIdeal (spectralIntegerRing K A) ^
                ⌈finitePhi A' B' hAB (q : ℝ)⌉₊ := by
          rw [finitePhi_eq_extendScalars]
          exact integerNorm_prime_sub_congruence A' B' hAB p hg hd he q u v huv
        have hstepnorm := integerNorm_sub_congruence_tower A' B' F hAB hBF r q
          ⌈finitePhi A' B' hAB (q : ℝ)⌉₊ hprime (htail r) x y hxy
        have hle : ⌈finitePhi A' F (hAB.trans hBF) (r : ℝ)⌉₊ ≤
            ⌈finitePhi A' B' hAB (q : ℝ)⌉₊ := by
          apply Nat.ceil_mono
          rw [← finitePhi_comp A' B' F hAB hBF (r : ℝ)]
          exact finitePhi_mono A' B' hAB (Nat.le_ceil _)
        exact Ideal.pow_le_pow_right hle hstepnorm
  obtain ⟨_, hn⟩ := hmain E.val hchain le_rfl
  have ht := hn r x y hxy
  rw [finitePhi_eq_extendScalars] at ht
  exact ht

end FontaineWintenberger.FiniteIntermediateField
