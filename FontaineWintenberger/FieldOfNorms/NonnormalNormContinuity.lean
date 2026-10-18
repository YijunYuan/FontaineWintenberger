/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormEstimates
public import FontaineWintenberger.FieldOfNorms.WildNormContinuity
public import FontaineWintenberger.APF.WildCompositumHerbrand

/-!
# Herbrand continuity for the original nonnormal norm

Actual tame base change scales both input precision and the Herbrand modulus
by the same ramification index. Descent therefore preserves the intrinsic
modulus on the original integer rings, without a normality assumption.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

private theorem algebraMap_sub_mem_pow_mul
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    (r : ℕ) (x y : R) (h : x - y ∈ IsLocalRing.maximalIdeal R ^ r) :
    algebraMap R S x - algebraMap R S y ∈ IsLocalRing.maximalIdeal S ^
      ((IsLocalRing.maximalIdeal S).ramificationIdx R * r) := by
  rw [← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_algebraMap, Nat.cast_mul]
  gcongr
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mp h

private theorem sub_mem_pow_of_equiv_commutes
    {R S T : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (f : T ≃+* S) (g : R → T) (j : R → S)
    (hcomm : ∀ z, f (g z) = j z) (r : ℕ) (x y : R)
    (hxy : g x - g y ∈ IsLocalRing.maximalIdeal T ^ r) :
    j x - j y ∈ IsLocalRing.maximalIdeal S ^ r := by
  rw [← hcomm x, ← hcomm y, ← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv]
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mp hxy

private theorem spectralIntegerInclusion_sub_mem_pow_of_normedTower
    (K E L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField E] [NormedAlgebra K E] [IsUltrametricDist E] [CompleteSpace E]
    [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
    [NormedAlgebra E L] [IsScalarTower K E L]
    [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic E L]
    [IsDiscreteValuationRing (spectralIntegerRing K E)]
    [IsDiscreteValuationRing (spectralIntegerRing K L)]
    [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
    [IsDiscreteValuationRing (spectralIntegerRing E L)]
    (i : E →ₐ[K] L) (hi : ∀ z, algebraMap E L z = i z)
    (r : ℕ) (x y : spectralIntegerRing K E)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K E) ^ r) :
    spectralIntegerInclusion K i x -
      spectralIntegerInclusion K i y ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K L) ^
        ((IsLocalRing.maximalIdeal (spectralIntegerRing E L)).ramificationIdx
          (NormedField.valuation (K := E)).valuationSubring * r) := by
  let RF := (NormedField.valuation (K := E)).valuationSubring
  let T := spectralIntegerRing E L
  let f : spectralIntegerRing K E ≃+* RF :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      (spectralIntegerRing_eq_normedUnitBall K E))
  let g : T ≃+* spectralIntegerRing K L :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      ((spectralIntegerRing_eq_normedUnitBall E L).trans
        (spectralIntegerRing_eq_normedUnitBall K L).symm))
  have hxy' : f x - f y ∈ IsLocalRing.maximalIdeal RF ^ r := by
    rw [← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv]
    exact (mem_maximalIdeal_pow_iff_addVal _ _).mp hxy
  have ht := algebraMap_sub_mem_pow_mul RF T r (f x) (f y) hxy'
  let J := spectralIntegerInclusion K i
  have hcomm (z : spectralIntegerRing K E) : g (algebraMap RF T (f z)) = J z := by
    apply Subtype.ext
    change ((algebraMap RF T (f z)) : L) = i (z : E)
    exact (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
      (NormedField.valuation (K := E)) (spectralValuation E L) (f z)).trans (hi (z : E))
  exact sub_mem_pow_of_equiv_commutes g (fun z => algebraMap RF T (f z))
    J hcomm ((IsLocalRing.maximalIdeal T).ramificationIdx RF * r) x y ht

section ActualCompositum

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω
local notation "P" => lowerRamificationGroup G
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1
local notation "A" => IntermediateField.fixedField P
local notation "e" => Ideal.ramificationIdx
  (IsLocalRing.maximalIdeal (spectralIntegerRing K A))
  (Valuation.valuationSubring (NormedField.valuation (K := K)))

local instance (E : IntermediateField K Ω) : CompleteSpace E :=
  FiniteDimensional.complete K E
local instance (E : IntermediateField K Ω) :
    IsCompleteDiscreteValuedField E :=
  normedAlgebra_isCompleteDiscreteValuedField K E
local instance (E : IntermediateField K Ω) : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := E)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K E

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Actual finite-layer integer inclusions multiply integral precision by
the ramification index of the same extension on its own integer rings. -/
theorem spectralIntegerInclusion_sub_mem_pow_ramificationIdx
    (F M : IntermediateField K Ω) (hFM : F ≤ M)
    (r : ℕ) (x y : spectralIntegerRing K F)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F) ^ r) :
    let MF := IntermediateField.extendScalars hFM
    spectralIntegerInclusion K (IntermediateField.inclusion hFM) x -
      spectralIntegerInclusion K (IntermediateField.inclusion hFM) y ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K M) ^
        ((IsLocalRing.maximalIdeal (spectralIntegerRing F MF)).ramificationIdx
          (NormedField.valuation (K := F)).valuationSubring * r) := by
  let MF := IntermediateField.extendScalars hFM
  let : NontriviallyNormedField MF := inferInstanceAs (NontriviallyNormedField M)
  let : NormedAlgebra K MF := inferInstanceAs (NormedAlgebra K M)
  let : FiniteDimensional K MF := inferInstanceAs (FiniteDimensional K M)
  let : IsScalarTower K F MF := IsScalarTower.of_algebraMap_eq' rfl
  let : IsDiscreteValuationRing (spectralIntegerRing K MF) :=
    inferInstanceAs (IsDiscreteValuationRing (spectralIntegerRing K M))
  have h := spectralIntegerInclusion_sub_mem_pow_of_normedTower K F MF
    (IntermediateField.inclusion hFM) (fun _ => rfl) r x y hxy
  exact h

/-- The actual inclusion into the tame compositum multiplies integral
precision by the same actual ramification index used in Herbrand scaling. -/
theorem spectralIntegerInclusion_sub_mem_wild_compositum_pow
    (F : IntermediateField K Ω) (hFP : F.fixingSubgroup ⊔ P = ⊤)
    (r : ℕ) (x y : spectralIntegerRing K F)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F) ^ r) :
    spectralIntegerInclusion K (IntermediateField.inclusion
        (show F ≤ A ⊔ F from le_sup_right)) x -
      spectralIntegerInclusion K (IntermediateField.inclusion
        (show F ≤ A ⊔ F from le_sup_right)) y ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K (A ⊔ F : IntermediateField K Ω)) ^
        (e * r) := by
  have h := spectralIntegerInclusion_sub_mem_pow_ramificationIdx K Ω F (A ⊔ F)
    le_sup_right r x y hxy
  dsimp only at h
  rw [wild_compositum_ramificationIdx_eq K Ω F hFP] at h
  exact h

/-- Tame base change and actual ceiling descent give the intrinsic Herbrand
modulus for the original fixed field, including the trivial extension. -/
theorem intNorm_sub_congruence_of_totallyRamified_fixedField
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal ((spectralValuation K Ω).comap
      (algebraMap (IntermediateField.fixedField H) Ω)).valuationSubring).ramificationIdx
        (NormedField.valuation (K := K)).valuationSubring =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n)
    (r : ℕ) (x y : spectralIntegerRing K (IntermediateField.fixedField H))
    (hxy : x - y ∈ IsLocalRing.maximalIdeal
      (spectralIntegerRing K (IntermediateField.fixedField H)) ^ r) :
    Algebra.intNorm (NormedField.valuation (K := K)).valuationSubring
        (spectralIntegerRing K (IntermediateField.fixedField H)) x -
      Algebra.intNorm (NormedField.valuation (K := K)).valuationSubring
        (spectralIntegerRing K (IntermediateField.fixedField H)) y ∈
      IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring ^
        ⌈apfPhi K (IntermediateField.fixedField H) (isAPF_of_finite K _) (r : ℝ)⌉₊ := by
  let R := (NormedField.valuation (K := K)).valuationSubring
  let F := IntermediateField.fixedField H
  let S := spectralIntegerRing K F
  let T := spectralIntegerRing K A
  have hFP : F.fixingSubgroup ⊔ P = ⊤ := by
    simpa only [F, IntermediateField.fixingSubgroup_fixedField] using
      fixedField_sup_wild_eq_top K Ω p H he n hd
  let E : FiniteLayer K Ω := ⟨A, inferInstance⟩
  let N : FiniteLayer K Ω := ⟨A ⊔ F, inferInstance⟩
  have hEN : E ≤ N := (show A ≤ A ⊔ F from le_sup_left)
  let j : F →ₐ[K] (A ⊔ F : IntermediateField K Ω) :=
    IntermediateField.inclusion (show F ≤ A ⊔ F from le_sup_right)
  let J := spectralIntegerInclusion K j
  have hxy' := spectralIntegerInclusion_sub_mem_wild_compositum_pow K Ω F hFP r x y hxy
  have hc := FiniteLayer.integerNorm_sub_congruence_of_wild_field p E N hEN le_rfl
    (e * r) (J x) (J y) hxy'
  rw [Nat.cast_mul, wild_compositum_apfPhi_scaling K Ω F hFP (Nat.cast_nonneg r)] at hc
  have hnorm (z : S) : FiniteLayer.integerNorm E N hEN (J z) =
      algebraMap R T (Algebra.intNorm R S z) := by
    apply Subtype.ext
    rw [FiniteLayer.coe_integerNorm]
    change Algebra.norm A
      (⟨((z : F) : Ω), (show F ≤ A ⊔ F from le_sup_right) (z : F).property⟩ :
        IntermediateField.extendScalars (show A ≤ A ⊔ F from le_sup_left)) =
      algebraMap K A (algebraMap R K (Algebra.intNorm R S z))
    rw [show algebraMap R K (Algebra.intNorm R S z) = Algebra.norm K (z : F) from
      Algebra.algebraMap_intNorm z]
    exact fixedField_wild_norm_baseChange K Ω p H he n hd (z : F)
  have hdefect := congrArg₂ (fun a b : T => a - b) (hnorm x) (hnorm y)
  apply mem_maximalIdeal_pow_of_algebraMap_mem_ceil R T
    (apfPhi K F (isAPF_of_finite K F) (r : ℝ))
  simpa only [map_sub] using hdefect ▸ hc

end ActualCompositum

section OriginalExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The original intermediate field need not be normal: its own total
ramification and prime-power degree give the actual norm continuity modulus. -/
theorem intNorm_sub_congruence_of_totallyRamified_intermediateField
    (Ω : Type*) [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (M : IntermediateField K Ω)
    (he : (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx R =
      Module.finrank K M)
    (n : ℕ) (hd : Module.finrank K M = p ^ n)
    (r : ℕ) (x y : spectralIntegerRing K M)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K M) ^ r) :
    Algebra.intNorm R (spectralIntegerRing K M) x -
      Algebra.intNorm R (spectralIntegerRing K M) y ∈ IsLocalRing.maximalIdeal R ^
        ⌈apfPhi K M (isAPF_of_finite K M) (r : ℝ)⌉₊ := by
  let H := M.fixingSubgroup
  have hM : IntermediateField.fixedField H = M := IsGalois.fixedField_fixingSubgroup M
  clear_value H
  subst M
  let w := (spectralValuation K Ω).comap
    (algebraMap (IntermediateField.fixedField H) Ω)
  have he' :
      letI := extensionValuationSubring_isDiscreteValuationRing K (IntermediateField.fixedField H) w
      (IsLocalRing.maximalIdeal w.valuationSubring).ramificationIdx R =
        Module.finrank K (IntermediateField.fixedField H) := by
    rw [extensionValuationSubring_ramificationIdx_eq_spectral K
      (IntermediateField.fixedField H) w]
    exact he
  exact intNorm_sub_congruence_of_totallyRamified_fixedField K Ω p H he' n hd r x y hxy

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "S" => spectralIntegerRing K L

omit [PerfectField (IsLocalRing.ResidueField R)] in
private theorem intNorm_sub_congruence_of_algEquiv
    (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (e : L ≃ₐ[K] M) (r : ℕ)
    (hM : ∀ u v : spectralIntegerRing K M,
      u - v ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K M) ^ r →
        Algebra.intNorm R (spectralIntegerRing K M) u -
          Algebra.intNorm R (spectralIntegerRing K M) v ∈ IsLocalRing.maximalIdeal R ^
            ⌈apfPhi K M (isAPF_of_finite K M) (r : ℝ)⌉₊)
    (x y : S) (hxy : x - y ∈ IsLocalRing.maximalIdeal S ^ r) :
    Algebra.intNorm R S x - Algebra.intNorm R S y ∈ IsLocalRing.maximalIdeal R ^
      ⌈apfPhi K L (isAPF_of_finite K L) (r : ℝ)⌉₊ := by
  let f := spectralIntegerRingEquiv K e
  have hxy' : f x - f y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K M) ^ r := by
    rw [← map_sub, mem_maximalIdeal_pow_iff_addVal,
      spectralIntegerRingEquiv_addVal K e]
    exact (mem_maximalIdeal_pow_iff_addVal _ _).mp hxy
  have h := hM (f x) (f y) hxy'
  rw [← apfPhi_algEquiv K L e (isAPF_of_finite K L) (isAPF_of_finite K M) (r : ℝ)] at h
  simpa only [Algebra.intNorm_map_algEquiv] using h

/-- Every original finite separable totally ramified prime-power extension
has its intrinsic Herbrand norm modulus, over an arbitrary perfect residue
field. The trivial extension and zero inputs are included. -/
theorem intNorm_sub_congruence_of_totallyRamified
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    (n : ℕ) (hd : Module.finrank K L = p ^ n)
    (r : ℕ) (x y : S) (hxy : x - y ∈ IsLocalRing.maximalIdeal S ^ r) :
    Algebra.intNorm R S x - Algebra.intNorm R S y ∈ IsLocalRing.maximalIdeal R ^
      ⌈apfPhi K L (isAPF_of_finite K L) (r : ℝ)⌉₊ := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let Ω := IntermediateField.normalClosure K L (SeparableClosure K)
  let : NontriviallyNormedField Ω := spectralNorm.nontriviallyNormedField K Ω
  let : NormedAlgebra K Ω := spectralNorm.normedAlgebra K Ω
  let : IsUltrametricDist Ω :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  have : CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p :=
    charP_of_injective_algebraMap' (IsLocalRing.ResidueField R) p
  let i : L →ₐ[K] Ω :=
    j.codRestrict Ω.toSubalgebra (fun x => j.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let M := i.fieldRange
  let e : L ≃ₐ[K] M := i.equivFieldRange
  let : FiniteDimensional K M := Module.Finite.equiv e.toLinearEquiv
  have hn : Module.finrank K M = Module.finrank K L := e.toLinearEquiv.finrank_eq.symm
  have heM : (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx R =
      Module.finrank K M := by
    rw [spectral_ramificationIdx_algEquiv K e, he, hn]
  exact intNorm_sub_congruence_of_algEquiv K L M e r
    (fun u v huv => intNorm_sub_congruence_of_totallyRamified_intermediateField
      K Ω p M heM n (hn.trans hd) r u v huv) x y hxy

end OriginalExtension

end FontaineWintenberger
