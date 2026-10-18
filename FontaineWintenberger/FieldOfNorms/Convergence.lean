/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Addition

/-!
# Convergence of the original norm-sum nets

Actual deep finite-layer estimates and the intrinsic Herbrand modulus prove
the Cauchy property in each original complete finite field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every requested integral precision is attained by the actual additive
norm defect on an entire original finite-layer tail. -/
theorem IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence
    [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, T ≤ E → ∀ hEF : E ≤ F,
      ∀ x y : spectralIntegerRing K F.val,
        FiniteIntermediateField.integerNorm E F hEF (x + y) - FiniteIntermediateField.integerNorm E
            F hEF x -
          FiniteIntermediateField.integerNorm E F hEF y ∈
            IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s := by
  let c : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ) * s
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  obtain ⟨T₁, hT₁⟩ := IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge K L c
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E F hE hEF x y => ?_⟩
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  obtain ⟨_, ⟨n, hd⟩, he⟩ := hT₀ E F ((FiniteIntermediateField.le_sup_left T₀ T₁).trans hE) hEF
  have hb := hT₁ E F ((FiniteIntermediateField.le_sup_right T₀ T₁).trans hE) hEF
  have h := FiniteIntermediateField.integerNorm_add_congruence_of_le_apfRamificationBound
    E F hEF he n hd c hb x y
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hp₁ : ((p - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := (Fact.out : Nat.Prime p).two_le; omega)
  have hc : ((p - 1 : ℕ) : ℝ) / p * c = (s : ℝ) := by
    dsimp only [c]
    field_simp
  simpa only [hc, Nat.ceil_natCast] using h

/-- The actual norm-sum term differs from the two original integral
coordinates by any requested precision on one entire finite-layer tail. -/
theorem IsAPF.exists_finiteIntermediateField_normSumNet_sub_mem [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      ∀ α β : FieldOfNorms K L,
      FieldOfNorms.valuation K L α ≤ 1 → FieldOfNorms.valuation K L β ≤ 1 →
      ∀ F : Set.Ici E,
        normSumNet K L E α β F - FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence K L s
  refine ⟨T, fun E hE α β hα hβ F => ?_⟩
  let x : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F.val⟩
  refine ⟨FiniteIntermediateField.integerNorm E F.val F.property (x + y) -
    FiniteIntermediateField.integerNorm E F.val F.property x -
    FiniteIntermediateField.integerNorm E F.val F.property y, hT E F.val hE F.property x y, ?_⟩
  change (FiniteIntermediateField.integerNorm E F.val F.property (x + y) : E.val) -
      (FiniteIntermediateField.integerNorm E F.val F.property x : E.val) -
      (FiniteIntermediateField.integerNorm E F.val F.property y : E.val) = _
  rw [FiniteIntermediateField.coe_integerNorm E F.val F.property (x + y),
    FiniteIntermediateField.coe_integerNorm E F.val F.property x,
    FiniteIntermediateField.coe_integerNorm E F.val F.property y]
  change normSumNet K L E α β F -
    FiniteIntermediateField.norm E F.val F.property (FieldOfNorms.coord K L F.val α) -
    FiniteIntermediateField.norm E F.val F.property (FieldOfNorms.coord K L F.val β) = _
  rw [FieldOfNorms.coord_norm K L E F.val F.property α,
    FieldOfNorms.coord_norm K L E F.val F.property β]

/-- On an actual wild tail, every integral-family norm-sum net is Cauchy
in its original fixed finite field. All finite precision estimates are proved. -/
theorem IsAPF.exists_finiteIntermediateField_normSumNet_cauchy [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      ∀ α β : FieldOfNorms K L,
      FieldOfNorms.valuation K L α ≤ 1 → FieldOfNorms.valuation K L β ≤ 1 →
      letI := spectralNorm.nontriviallyNormedField K E.val
      Cauchy (map (normSumNet K L E α β) atTop) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  refine ⟨T, fun E hE α β hα hβ => ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
  let a (F : FiniteIntermediateField K L) : spectralIntegerRing K F.val :=
    ⟨FieldOfNorms.coord K L F α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F⟩
  let b (F : FiniteIntermediateField K L) : spectralIntegerRing K F.val :=
    ⟨FieldOfNorms.coord K L F β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F⟩
  have ha (F G : FiniteIntermediateField K L) (hFG : F ≤ G) :
      FiniteIntermediateField.integerNorm F G hFG (a G) = a F := by
    apply Subtype.ext
    rw [FiniteIntermediateField.coe_integerNorm]
    exact FieldOfNorms.coord_norm K L F G hFG α
  have hb (F G : FiniteIntermediateField K L) (hFG : F ≤ G) :
      FiniteIntermediateField.integerNorm F G hFG (b G) = b F := by
    apply Subtype.ext
    rw [FiniteIntermediateField.coe_integerNorm]
    exact FieldOfNorms.coord_norm K L F G hFG β
  apply cauchy_map_of_eventually_sub_mem_maximalIdeal_pow E.val
  intro N
  let s := ⌈apfPsi E.val L (N : ℝ)⌉₊
  have hs : apfPsi E.val L (N : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  obtain ⟨U, hU⟩ := IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence K L s
  let A : Set.Ici E := ⟨FiniteIntermediateField.sup E U, FiniteIntermediateField.le_sup_left E U⟩
  have hstep (B C : FiniteIntermediateField K L) (hEB : E ≤ B) (hBC : B ≤ C) (hUB : U ≤ B) :
      normSumNet K L E α β ⟨C, hEB.trans hBC⟩ -
        normSumNet K L E α β ⟨B, hEB⟩ ∈
      (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ N :
          Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
    let : Algebra E.val B.val := (IntermediateField.inclusion hEB).toRingHom.toAlgebra
    let : IsScalarTower K E.val B.val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := E.val) (L := B.val)
    let x := FiniteIntermediateField.integerNorm B C hBC (a C + b C)
    let y := a B + b B
    have hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K B.val) ^ s := by
      have h := hU B C hUB hBC (a C) (b C)
      rw [ha B C hBC, hb B C hBC] at h
      simpa only [x, y, sub_sub] using h
    obtain ⟨_, ⟨n, hd⟩, he⟩ := hT E B hE hEB
    have h := FiniteIntermediateField.integerNorm_sub_congruence_of_totallyRamified
      E B hEB he n hd s x y hxy
    have hprecision := FiniteIntermediateField.le_ceil_apfPhi_of_apfPsi_le K L E B hEB N s hs
    have hmem := Ideal.pow_le_pow_right hprecision h
    refine ⟨FiniteIntermediateField.integerNorm E B hEB x - FiniteIntermediateField.integerNorm E B
        hEB y,
      hmem, ?_⟩
    change (FiniteIntermediateField.integerNorm E B hEB x : E.val) -
      (FiniteIntermediateField.integerNorm E B hEB y : E.val) = _
    rw [FiniteIntermediateField.coe_integerNorm E B hEB x, FiniteIntermediateField.coe_integerNorm
        E B hEB y]
    dsimp only [x, y]
    rw [FiniteIntermediateField.coe_integerNorm B C hBC (a C + b C)]
    change FiniteIntermediateField.norm E B hEB
        (FiniteIntermediateField.norm B C hBC (FieldOfNorms.coord K L C α + FieldOfNorms.coord K L
            C β)) -
      FiniteIntermediateField.norm E B hEB (FieldOfNorms.coord K L B α + FieldOfNorms.coord K L B
          β) = _
    rw [FiniteIntermediateField.norm_norm]
    rfl
  refine ⟨A, fun B hB C hC => ?_⟩
  let D := FiniteIntermediateField.sup B.val C.val
  have hUB : U ≤ B.val := (FiniteIntermediateField.le_sup_right E U).trans hB
  have hUC : U ≤ C.val := (FiniteIntermediateField.le_sup_right E U).trans hC
  obtain ⟨zB, hzB, heqB⟩ := hstep B.val D B.property (FiniteIntermediateField.le_sup_left _ _) hUB
  obtain ⟨zC, hzC, heqC⟩ := hstep C.val D C.property (FiniteIntermediateField.le_sup_right _ _) hUC
  refine ⟨zC - zB, Ideal.sub_mem _ hzC hzB, ?_⟩
  change (zC : E.val) - (zB : E.val) = _
  linear_combination heqC - heqB

/-- Actual integral-family norm-sum nets converge at every original finite
base, including bases below or incomparable with the wild tail. -/
theorem exists_tendsto_normSumNet_of_valuation_le_one [IsAPF K L]
    (α β : FieldOfNorms K L) (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_normSumNet_cauchy K L
  apply exists_tendsto_normSumNet_of_upper_tail K L T α β
  intro E hE
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.completeSpace K E.val
  exact cauchy_map_iff_exists_tendsto.mp (hT E hE α β hα hβ)

/-- The same original field of norms contains the unique integral sum family.
Its finite-coordinate approximation is proved by closed actual ideal powers. -/
theorem existsUnique_fieldOfNorms_integral_add [IsAPF K L]
    (α β : FieldOfNorms K L) (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∃! γ : FieldOfNorms K L, FieldOfNorms.valuation K L γ ≤ 1 ∧
      (∀ E : FiniteIntermediateField K L,
        letI := spectralNorm.nontriviallyNormedField K E.val
        Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ))) ∧
      ∀ s : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
        FieldOfNorms.coord K L E γ - FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_fieldOfNorms_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet_of_valuation_le_one K L α β hα hβ)
  refine ⟨γ, ⟨?_, hγ, ?_⟩, fun δ hδ => huniq δ hδ.2.1⟩
  · rw [FieldOfNorms.valuation_le_one_iff K L γ]
    intro E
    exact normSumNet_limit_mem_of_valuation_le_one K L α β hα hβ E _ (hγ E)
  · intro s
    obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_normSumNet_sub_mem K L s
    refine ⟨T, fun E hE => ?_⟩
    let := spectralNorm.nontriviallyNormedField K E.val
    exact (FiniteIntermediateField.isClosed_image_maximalIdeal_pow E s).mem_of_tendsto
      (((hγ E).sub_const (FieldOfNorms.coord K L E α)).sub_const (FieldOfNorms.coord K L E β))
      (Eventually.of_forall (hT E hE α β hα hβ))

end FontaineWintenberger
