/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Estimates.Wild
public import FontaineWintenberger.APF.Elementary.TameCompositum
public import FontaineWintenberger.Ramification.Norm.Approximation

/-!
# Descent of the wild-field norm estimate

The tame compositum preserves the nonnormal field norm.
The proved first-bound scaling and normalized valuation restriction cancel
the same ramification index in the precision estimate.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open IsDiscreteValuationRing

/-- Integer ceiling precision descends through a local DVR map,
using its canonical ramification index, including zero elements. -/
theorem mem_maximalIdeal_pow_of_algebraMap_mem_ceil
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    (b : ℝ) (x : R)
    (hx : algebraMap R S x ∈ IsLocalRing.maximalIdeal S ^
      ⌈((IsLocalRing.maximalIdeal S).ramificationIdx R : ℝ) * b⌉₊) :
    x ∈ IsLocalRing.maximalIdeal R ^ ⌈b⌉₊ := by
  rw [mem_maximalIdeal_pow_iff_addVal, addVal_algebraMap R S] at hx
  rw [mem_maximalIdeal_pow_iff_addVal]
  generalize hv : addVal R x = v at hx ⊢
  cases v using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have he : (0 : ℝ) < (IsLocalRing.maximalIdeal S).ramificationIdx R :=
      Nat.cast_pos.mpr (local_ramificationIdx_pos R S)
    have hn : ⌈((IsLocalRing.maximalIdeal S).ramificationIdx R : ℝ) * b⌉₊ ≤
        (IsLocalRing.maximalIdeal S).ramificationIdx R * n := by
      exact_mod_cast hx
    have hb : b ≤ n := by
      apply (mul_le_mul_iff_right₀ he).mp
      calc
        _ ≤ (⌈((IsLocalRing.maximalIdeal S).ramificationIdx R : ℝ) * b⌉₊ : ℝ) :=
          Nat.le_ceil _
        _ ≤ _ := by exact_mod_cast hn
    exact_mod_cast (Nat.ceil_le.mpr hb : ⌈b⌉₊ ≤ n)

section FiniteGaloisOverfield

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "p" => residueChar K

local instance tameNorm_residueField_charP :
    CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p :=
  charP_of_injective_algebraMap
    (algebraMap 𝓀[K]
      (IsLocalRing.ResidueField (spectralIntegerRing K Ω))).injective p

local instance tameNorm_completeSpace (M : IntermediateField K Ω) : CompleteSpace M :=
  FiniteDimensional.complete K M
local instance tameNorm_discreteValuationRing (M : IntermediateField K Ω) :
    IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
local instance tameNorm_perfectField (M : IntermediateField K Ω) : PerfectField
    𝓀[M] :=
  Algebra.IsAlgebraic.perfectField 𝓀[K]

variable (H : Subgroup (Ω ≃ₐ[K] Ω))

local notation "F" => IntermediateField.fixedField H
local notation "S" => spectralIntegerRing K F
local notation "P" => lowerRamificationGroup (Ω ≃ₐ[K] Ω)
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1
local notation "A" => IntermediateField.fixedField P
local notation "T" => spectralIntegerRing K A
local notation "e" => Ideal.ramificationIdx (IsLocalRing.maximalIdeal T) 𝒪[K]

/-- The nonnormal p-power norm satisfies the quantitative addition
estimate. The tame compositum, its scaled first bound and its field
norm base-change identity are all supplied by proved producers. -/
theorem exists_intNorm_add_congruence_of_totallyRamified_fixedField
    (he : (IsLocalRing.maximalIdeal (Valuation.valuationSubring
      (Valuation.comap (algebraMap F Ω) (spectralValuation K Ω)))).ramificationIdx 𝒪[K] =
        Module.finrank K F)
    (n : ℕ) (hd : Module.finrank K F = p ^ n) (hdegree : 1 < Module.finrank K F) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K F = (b : EReal) ∧
      ∀ x y : S, Algebra.intNorm 𝒪[K] S (x + y) - Algebra.intNorm 𝒪[K] S x -
        Algebra.intNorm 𝒪[K] S y ∈ IsLocalRing.maximalIdeal 𝒪[K] ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  obtain ⟨b, hb, hbound, hboundA⟩ :=
    exists_apfRamificationBound_wild_compositum_of_totallyRamified K Ω p H he n hd hdegree
  refine ⟨b, hb, hbound, ?_⟩
  intro x y
  let E : FiniteIntermediateField K Ω := ⟨A, inferInstance⟩
  let N : FiniteIntermediateField K Ω := ⟨A ⊔ F, inferInstance⟩
  have hEN : E ≤ N := (show A ≤ A ⊔ F from le_sup_left)
  let j : F →ₐ[K] (A ⊔ F : IntermediateField K Ω) :=
    IntermediateField.inclusion (show F ≤ A ⊔ F from le_sup_right)
  let J := spectralIntegerInclusion K j
  have hc := FiniteIntermediateField.integerNorm_add_congruence_of_wild_field p E N hEN le_rfl
    ((e : ℝ) * b) (le_of_eq hboundA.symm) (J x) (J y)
  have hnorm (z : S) : FiniteIntermediateField.integerNorm E N hEN (J z) =
      algebraMap 𝒪[K] T (Algebra.intNorm 𝒪[K] S z) := by
    apply Subtype.ext
    rw [FiniteIntermediateField.coe_integerNorm]
    change Algebra.norm A
      (⟨((z : F) : Ω), (show F ≤ A ⊔ F from le_sup_right) (z : F).property⟩ :
        IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)) =
      algebraMap K A (algebraMap 𝒪[K] K (Algebra.intNorm 𝒪[K] S z))
    rw [show algebraMap 𝒪[K] K (Algebra.intNorm 𝒪[K] S z) = Algebra.norm K (z : F) from
      Algebra.algebraMap_intNorm z]
    exact fixedField_wild_norm_baseChange K Ω p H he n hd (z : F)
  have hsum := (congrArg (FiniteIntermediateField.integerNorm E N hEN)
    (map_add J x y).symm).trans (hnorm (x + y))
  have hdefect := congrArg₂ (fun a b : T => a - b)
    (congrArg₂ (fun a b : T => a - b) hsum (hnorm x)) (hnorm y)
  have hm : algebraMap 𝒪[K] T (Algebra.intNorm 𝒪[K] S (x + y) - Algebra.intNorm 𝒪[K] S x -
      Algebra.intNorm 𝒪[K] S y) ∈ IsLocalRing.maximalIdeal T ^
        ⌈((p - 1 : ℕ) : ℝ) / p * ((e : ℝ) * b)⌉₊ := by
    simpa only [map_sub] using hdefect ▸ hc
  apply mem_maximalIdeal_pow_of_algebraMap_mem_ceil 𝒪[K] T
    (((p - 1 : ℕ) : ℝ) / p * b)
  simpa only [mul_left_comm] using hm

end FiniteGaloisOverfield

end FontaineWintenberger
