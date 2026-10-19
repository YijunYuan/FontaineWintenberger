/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Estimates.Nonnormal

/-!
# Estimates for the finite-layer integral norms

The canonical spectral norms on the two finite fields identify
their integer rings with the integer rings used over the relative base.
The commuting identity on field elements transports the norms,
ramification indices and ideal-power estimates without a norm on the
ambient separable extension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open IsDiscreteValuationRing

private theorem ramificationIdx_of_equiv_commutes
    {R S R' S' : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S'] [IsDomain S'] [IsDiscreteValuationRing S']
    [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    [Algebra R' S'] [FaithfulSMul R' S'] [IsLocalHom (algebraMap R' S')]
    (f : R ≃+* R') (g : S ≃+* S')
    (hcomm : ∀ z, algebraMap R' S' (f z) = g (algebraMap R S z)) :
    (IsLocalRing.maximalIdeal S').ramificationIdx R' =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  apply ENat.natCast_inj.mp
  calc
    _ = addVal S' (algebraMap R' S' (f π)) := by
      rw [addVal_algebraMap, addVal_ringEquiv, addVal_uniformizer hπ, mul_one]
    _ = addVal S' (g (algebraMap R S π)) := congrArg _ (hcomm π)
    _ = addVal S (algebraMap R S π) := addVal_ringEquiv g _
    _ = _ := (ramificationIdx_eq_addVal_uniformizer R S hπ).symm

private theorem sub_mem_pow_of_norm_commutes
    {R R' S S' : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S] [CommRing S']
    (f : R ≃+* R') (g : S ≃+* S') (N : S →* R) (N' : S' →* R')
    (hN : ∀ z, N' (g z) = f (N z)) (r : ℕ) (x y : S)
    (h : N' (g x) - N' (g y) ∈ IsLocalRing.maximalIdeal R' ^ r) :
    N x - N y ∈ IsLocalRing.maximalIdeal R ^ r := by
  rw [hN x, hN y, ← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv] at h
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mpr h

private theorem add_sub_mem_pow_of_norm_commutes
    {R R' S S' : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S] [CommRing S']
    (f : R ≃+* R') (g : S ≃+* S') (N : S →* R) (N' : S' →* R')
    (hN : ∀ z, N' (g z) = f (N z)) (r : ℕ) (x y : S)
    (h : N' (g x + g y) - N' (g x) - N' (g y) ∈
      IsLocalRing.maximalIdeal R' ^ r) :
    N (x + y) - N x - N y ∈ IsLocalRing.maximalIdeal R ^ r := by
  rw [← map_add g, hN (x + y), hN x, hN y, ← map_sub, ← map_sub,
    mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv] at h
  exact (mem_maximalIdeal_pow_iff_addVal _ _).mpr h

namespace FiniteIntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field L] [Algebra K L] [Algebra.IsSeparable K L]

local notation "p" => residueChar K

/-- The finite-layer norm has the intrinsic relative
Herbrand modulus on every totally ramified prime-power step, including
the identity step. No norm on the ambient separable extension is chosen. -/
theorem integerNorm_sub_congruence_of_totallyRamified
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isPerfectResidueLocalField K E.val
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    ∀ (_ : (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
          (spectralIntegerRing K E.val) = Module.finrank E.val F')
      (n : ℕ) (_ : Module.finrank E.val F' = p ^ n)
      (r : ℕ) (x y : spectralIntegerRing K F.val),
      x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ r →
        integerNorm E F hEF x - integerNorm E F hEF y ∈
          IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
            ⌈apfPhi E.val F' (r : ℝ)⌉₊ := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isPerfectResidueLocalField K E.val
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := F.property
  let : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  dsimp only
  intro he n hd r x y hxy
  let : IsScalarTower K E.val F' := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable K F' := inferInstanceAs (Algebra.IsSeparable K F.val)
  let : NontriviallyNormedField F' := spectralNorm.nontriviallyNormedField K F'
  let : NormedAlgebra K F' := spectralNorm.normedAlgebra K F'
  let : NormedAlgebra E.val F' := spectralNorm.normedAlgebra' K E.val F'
  let : IsUltrametricDist F' :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := F'))
  have : Algebra.IsSeparable E.val F' :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F'
  have : CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := E.val)).valuationSubring) p :=
    charP_of_injective_algebraMap'
      (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p
  let R := spectralIntegerRing K E.val
  let S := spectralIntegerRing K F.val
  let R' := (NormedField.valuation (K := E.val)).valuationSubring
  let S' := spectralIntegerRing E.val F'
  let f : R ≃+* R' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    (spectralIntegerRing_eq_normedUnitBall K E.val))
  let g : S ≃+* S' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    ((spectralIntegerRing_eq_normedUnitBall K F').trans
      (spectralIntegerRing_eq_normedUnitBall E.val F').symm))
  have hcomm (z : R) : algebraMap R' S' (f z) = g (algebraMap R S z) := by
    apply Subtype.ext
    exact (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
      (NormedField.valuation (K := E.val)) (spectralValuation E.val F') (f z)).trans
      (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
        (spectralValuation K E.val) (spectralValuation K F.val) z).symm
  have he' : (IsLocalRing.maximalIdeal S').ramificationIdx R' =
      Module.finrank E.val F' := (ramificationIdx_of_equiv_commutes f g hcomm).trans he
  have hxy' : g x - g y ∈ IsLocalRing.maximalIdeal S' ^ r := by
    rw [← map_sub, mem_maximalIdeal_pow_iff_addVal, addVal_ringEquiv]
    exact (mem_maximalIdeal_pow_iff_addVal _ _).mp hxy
  have hc := FontaineWintenberger.intNorm_sub_congruence_of_totallyRamified
    E.val F' p he' n hd r (g x) (g y) hxy'
  have hnorm (z : S) : Algebra.intNorm R' S' (g z) = f (integerNorm E F hEF z) := by
    apply Subtype.ext
    change (Algebra.intNorm R' S' (g z) : E.val) = (integerNorm E F hEF z : E.val)
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm (A := R') (B := S') (K := E.val) (L := F') (g z)
  exact sub_mem_pow_of_norm_commutes f g (integerNorm E F hEF)
    (Algebra.intNorm R' S') hnorm _ x y hc

/-- The additive norm defect has the precision given by
the first bound of a nontrivial totally ramified prime-power step. -/
theorem exists_integerNorm_add_congruence_of_totallyRamified
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isPerfectResidueLocalField K E.val
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    ∀ (_ : (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
          (spectralIntegerRing K E.val) = Module.finrank E.val F')
      (n : ℕ) (_ : Module.finrank E.val F' = p ^ n)
      (_ : 1 < Module.finrank E.val F'),
      ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound E.val F' = (b : EReal) ∧
        ∀ x y : spectralIntegerRing K F.val,
          integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
            IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
              ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isPerfectResidueLocalField K E.val
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := F.property
  let : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  dsimp only
  intro he n hd hdegree
  let : IsScalarTower K E.val F' := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable K F' := inferInstanceAs (Algebra.IsSeparable K F.val)
  let : NontriviallyNormedField F' := spectralNorm.nontriviallyNormedField K F'
  let : NormedAlgebra K F' := spectralNorm.normedAlgebra K F'
  let : NormedAlgebra E.val F' := spectralNorm.normedAlgebra' K E.val F'
  let : IsUltrametricDist F' :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := F'))
  have : Algebra.IsSeparable E.val F' :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F'
  have hp : residueChar E.val = p := normedAlgebra_residueChar_eq K E.val
  let R := spectralIntegerRing K E.val
  let S := spectralIntegerRing K F.val
  let R' := (NormedField.valuation (K := E.val)).valuationSubring
  let S' := spectralIntegerRing E.val F'
  let f : R ≃+* R' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    (spectralIntegerRing_eq_normedUnitBall K E.val))
  let g : S ≃+* S' := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    ((spectralIntegerRing_eq_normedUnitBall K F').trans
      (spectralIntegerRing_eq_normedUnitBall E.val F').symm))
  have hcomm (z : R) : algebraMap R' S' (f z) = g (algebraMap R S z) := by
    apply Subtype.ext
    exact (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
      (NormedField.valuation (K := E.val)) (spectralValuation E.val F') (f z)).trans
      (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
        (spectralValuation K E.val) (spectralValuation K F.val) z).symm
  have he' : (IsLocalRing.maximalIdeal S').ramificationIdx R' =
      Module.finrank E.val F' := (ramificationIdx_of_equiv_commutes f g hcomm).trans he
  obtain ⟨b, hb, hbound, hadd⟩ :=
    FontaineWintenberger.exists_intNorm_add_congruence_of_totallyRamified
      E.val F' he' n (by rw [hp]; exact hd) hdegree
  simp only [hp] at hadd
  refine ⟨b, hb, hbound, fun x y => ?_⟩
  have hnorm (z : S) : Algebra.intNorm R' S' (g z) = f (integerNorm E F hEF z) := by
    apply Subtype.ext
    change (Algebra.intNorm R' S' (g z) : E.val) = (integerNorm E F hEF z : E.val)
    rw [coe_integerNorm]
    exact Algebra.algebraMap_intNorm (A := R') (B := S') (K := E.val) (L := F') (g z)
  exact add_sub_mem_pow_of_norm_commutes f g (integerNorm E F hEF)
    (Algebra.intNorm R' S') hnorm _ x y (hadd (g x) (g y))

/-- A degree-one inclusion is an equality of the finite intermediate fields,
so its norm has exactly zero additive defect. -/
theorem integerNorm_add_sub_eq_zero_of_finrank_eq_one
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (hd : Module.finrank E.val (IntermediateField.extendScalars hEF) = 1)
    (x y : spectralIntegerRing K F.val) :
    integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y = 0 := by
  let F' := IntermediateField.extendScalars hEF
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  have hdim : Module.finrank K E.val = Module.finrank K F.val := by
    change Module.finrank E.val F' = 1 at hd
    have h := Module.finrank_mul_finrank K E.val F'
    rw [hd, mul_one] at h
    exact h
  have hef : E = F := Subtype.ext (IntermediateField.eq_of_le_of_finrank_eq hEF hdim)
  subst F
  simp only [integerNorm_self, add_sub_cancel_left, sub_self]

/-- Every finite real lower bound for the first bound controls the
additive norm defect. The identity step has infinite first bound
and zero defect, so all finite precisions are covered uniformly. -/
theorem integerNorm_add_congruence_of_le_apfRamificationBound
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isPerfectResidueLocalField K E.val
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    ∀ (_ : (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
          (spectralIntegerRing K E.val) = Module.finrank E.val F')
      (n : ℕ) (_ : Module.finrank E.val F' = p ^ n)
      (b : ℝ) (_ : (b : EReal) ≤ apfRamificationBound E.val F')
      (x y : spectralIntegerRing K F.val),
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isPerfectResidueLocalField K E.val
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := F.property
  let : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  dsimp only
  intro he n hd b hb x y
  by_cases hdegree : 1 < Module.finrank E.val F'
  · obtain ⟨c, _, hc, hadd⟩ :=
      exists_integerNorm_add_congruence_of_totallyRamified E F hEF he n hd hdegree
    have hbc : b ≤ c := by exact_mod_cast (hb.trans_eq hc)
    apply Ideal.pow_le_pow_right (Nat.ceil_mono
      (mul_le_mul_of_nonneg_left hbc
        (div_nonneg (Nat.cast_nonneg (p - 1)) (Nat.cast_nonneg p))))
    exact hadd x y
  · have hd1 : Module.finrank E.val F' = 1 := by
      have hpos := Module.finrank_pos (R := E.val) (M := F')
      omega
    rw [integerNorm_add_sub_eq_zero_of_finrank_eq_one E F hEF hd1]
    exact Ideal.zero_mem _

end FiniteIntermediateField

end FontaineWintenberger
