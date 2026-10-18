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

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

include p

/-- Every requested integral precision is attained by the actual additive
norm defect on an entire original finite-layer tail. -/
theorem IsAPF.exists_finiteLayer_integerNorm_add_congruence
    [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteLayer K L, ∀ E F : FiniteLayer K L, T ≤ E → ∀ hEF : E ≤ F,
      ∀ x y : spectralIntegerRing K F.val,
        FiniteLayer.integerNorm E F hEF (x + y) - FiniteLayer.integerNorm E F hEF x -
          FiniteLayer.integerNorm E F hEF y ∈
            IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s := by
  let c : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ) * s
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_finiteLayer_wild_tail K L p
  obtain ⟨T₁, hT₁⟩ := IsAPF.exists_finiteLayer_relativeFirstBound_ge K L c
  refine ⟨FiniteLayer.sup T₀ T₁, fun E F hE hEF x y => ?_⟩
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  obtain ⟨_, ⟨n, hd⟩, he⟩ := hT₀ E F ((FiniteLayer.le_sup_left T₀ T₁).trans hE) hEF
  have hb := hT₁ E F ((FiniteLayer.le_sup_right T₀ T₁).trans hE) hEF
  have h := FiniteLayer.integerNorm_add_congruence_of_le_apfRamificationBound
    E F hEF p he n hd c hb x y
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp₁ : ((p - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := (Fact.out : p.Prime).two_le; omega)
  have hc : ((p - 1 : ℕ) : ℝ) / p * c = (s : ℝ) := by
    dsimp only [c]
    field_simp
  simpa only [hc, Nat.ceil_natCast] using h

/-- The actual norm-sum term differs from the two original integral
coordinates by any requested precision on one entire finite-layer tail. -/
theorem IsAPF.exists_finiteLayer_normSumNet_sub_mem [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      ∀ α β : NormLimit K L,
      normLimitValuation K L α ≤ 1 → normLimitValuation K L β ≤ 1 →
      ∀ F : Set.Ici E,
        normSumNet K L E α β F - normLimitEval K L E α - normLimitEval K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_integerNorm_add_congruence K L p s
  refine ⟨T, fun E hE α β hα hβ F => ?_⟩
  let x : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val α, normLimitEval_mem_of_valuation_le_one K L α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val β, normLimitEval_mem_of_valuation_le_one K L β hβ F.val⟩
  refine ⟨FiniteLayer.integerNorm E F.val F.property (x + y) -
    FiniteLayer.integerNorm E F.val F.property x -
    FiniteLayer.integerNorm E F.val F.property y, hT E F.val hE F.property x y, ?_⟩
  change (FiniteLayer.integerNorm E F.val F.property (x + y) : E.val) -
      (FiniteLayer.integerNorm E F.val F.property x : E.val) -
      (FiniteLayer.integerNorm E F.val F.property y : E.val) = _
  rw [FiniteLayer.coe_integerNorm E F.val F.property (x + y),
    FiniteLayer.coe_integerNorm E F.val F.property x,
    FiniteLayer.coe_integerNorm E F.val F.property y]
  change normSumNet K L E α β F -
    FiniteLayer.norm E F.val F.property (normLimitEval K L F.val α) -
    FiniteLayer.norm E F.val F.property (normLimitEval K L F.val β) = _
  rw [normLimitEval_norm K L E F.val F.property α,
    normLimitEval_norm K L E F.val F.property β]

/-- On an actual wild tail, every integral-family norm-sum net is Cauchy
in its original fixed finite field. All finite precision estimates are proved. -/
theorem IsAPF.exists_finiteLayer_normSumNet_cauchy [IsAPF K L] :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      ∀ α β : NormLimit K L,
      normLimitValuation K L α ≤ 1 → normLimitValuation K L β ≤ 1 →
      letI := spectralNorm.nontriviallyNormedField K E.val
      Cauchy (map (normSumNet K L E α β) atTop) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_wild_tail K L p
  refine ⟨T, fun E hE α β hα hβ => ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
  let a (F : FiniteLayer K L) : spectralIntegerRing K F.val :=
    ⟨normLimitEval K L F α, normLimitEval_mem_of_valuation_le_one K L α hα F⟩
  let b (F : FiniteLayer K L) : spectralIntegerRing K F.val :=
    ⟨normLimitEval K L F β, normLimitEval_mem_of_valuation_le_one K L β hβ F⟩
  have ha (F G : FiniteLayer K L) (hFG : F ≤ G) :
      FiniteLayer.integerNorm F G hFG (a G) = a F := by
    apply Subtype.ext
    rw [FiniteLayer.coe_integerNorm]
    exact normLimitEval_norm K L F G hFG α
  have hb (F G : FiniteLayer K L) (hFG : F ≤ G) :
      FiniteLayer.integerNorm F G hFG (b G) = b F := by
    apply Subtype.ext
    rw [FiniteLayer.coe_integerNorm]
    exact normLimitEval_norm K L F G hFG β
  apply cauchy_map_of_eventually_sub_mem_maximalIdeal_pow E.val
  intro N
  let s := ⌈apfPsi E.val L (N : ℝ)⌉₊
  have hs : apfPsi E.val L (N : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  obtain ⟨U, hU⟩ := IsAPF.exists_finiteLayer_integerNorm_add_congruence K L p s
  let A : Set.Ici E := ⟨FiniteLayer.sup E U, FiniteLayer.le_sup_left E U⟩
  have hstep (B C : FiniteLayer K L) (hEB : E ≤ B) (hBC : B ≤ C) (hUB : U ≤ B) :
      normSumNet K L E α β ⟨C, hEB.trans hBC⟩ -
        normSumNet K L E α β ⟨B, hEB⟩ ∈
      (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ N :
          Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
    let : Algebra E.val B.val := (IntermediateField.inclusion hEB).toRingHom.toAlgebra
    let : IsScalarTower K E.val B.val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := E.val) (L := B.val)
    let x := FiniteLayer.integerNorm B C hBC (a C + b C)
    let y := a B + b B
    have hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K B.val) ^ s := by
      have h := hU B C hUB hBC (a C) (b C)
      rw [ha B C hBC, hb B C hBC] at h
      simpa only [x, y, sub_sub] using h
    obtain ⟨_, ⟨n, hd⟩, he⟩ := hT E B hE hEB
    have h := FiniteLayer.integerNorm_sub_congruence_of_totallyRamified
      E B hEB p he n hd s x y hxy
    have hprecision := FiniteLayer.le_ceil_apfPhi_of_apfPsi_le K L E B hEB N s hs
    have hmem := Ideal.pow_le_pow_right hprecision h
    refine ⟨FiniteLayer.integerNorm E B hEB x - FiniteLayer.integerNorm E B hEB y,
      hmem, ?_⟩
    change (FiniteLayer.integerNorm E B hEB x : E.val) -
      (FiniteLayer.integerNorm E B hEB y : E.val) = _
    rw [FiniteLayer.coe_integerNorm E B hEB x, FiniteLayer.coe_integerNorm E B hEB y]
    dsimp only [x, y]
    rw [FiniteLayer.coe_integerNorm B C hBC (a C + b C)]
    change FiniteLayer.norm E B hEB
        (FiniteLayer.norm B C hBC (normLimitEval K L C α + normLimitEval K L C β)) -
      FiniteLayer.norm E B hEB (normLimitEval K L B α + normLimitEval K L B β) = _
    rw [FiniteLayer.norm_norm]
    rfl
  refine ⟨A, fun B hB C hC => ?_⟩
  let D := FiniteLayer.sup B.val C.val
  have hUB : U ≤ B.val := (FiniteLayer.le_sup_right E U).trans hB
  have hUC : U ≤ C.val := (FiniteLayer.le_sup_right E U).trans hC
  obtain ⟨zB, hzB, heqB⟩ := hstep B.val D B.property (FiniteLayer.le_sup_left _ _) hUB
  obtain ⟨zC, hzC, heqC⟩ := hstep C.val D C.property (FiniteLayer.le_sup_right _ _) hUC
  refine ⟨zC - zB, Ideal.sub_mem _ hzC hzB, ?_⟩
  change (zC : E.val) - (zB : E.val) = _
  linear_combination heqC - heqB

/-- Actual integral-family norm-sum nets converge at every original finite
base, including bases below or incomparable with the wild tail. -/
theorem exists_tendsto_normSumNet_of_valuation_le_one [IsAPF K L]
    (α β : NormLimit K L) (hα : normLimitValuation K L α ≤ 1)
    (hβ : normLimitValuation K L β ≤ 1) :
    ∀ E : FiniteLayer K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_normSumNet_cauchy K L p
  apply exists_tendsto_normSumNet_of_upper_tail K L T α β
  intro E hE
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.completeSpace K E.val
  exact cauchy_map_iff_exists_tendsto.mp (hT E hE α β hα hβ)

/-- The same original norm limit contains the unique integral sum family.
Its finite-coordinate approximation is proved by closed actual ideal powers. -/
theorem existsUnique_normLimit_integral_add [IsAPF K L]
    (α β : NormLimit K L) (hα : normLimitValuation K L α ≤ 1)
    (hβ : normLimitValuation K L β ≤ 1) :
    ∃! γ : NormLimit K L, normLimitValuation K L γ ≤ 1 ∧
      (∀ E : FiniteLayer K L,
        letI := spectralNorm.nontriviallyNormedField K E.val
        Tendsto (normSumNet K L E α β) atTop (nhds (normLimitEval K L E γ))) ∧
      ∀ s : ℕ, ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
        normLimitEval K L E γ - normLimitEval K L E α - normLimitEval K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_normLimit_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet_of_valuation_le_one K L p α β hα hβ)
  refine ⟨γ, ⟨?_, hγ, ?_⟩, fun δ hδ => huniq δ hδ.2.1⟩
  · rw [normLimitValuation_le_one_iff K L γ]
    intro E
    exact normSumNet_limit_mem_of_valuation_le_one K L α β hα hβ E _ (hγ E)
  · intro s
    obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_normSumNet_sub_mem K L p s
    refine ⟨T, fun E hE => ?_⟩
    let := spectralNorm.nontriviallyNormedField K E.val
    exact (FiniteLayer.isClosed_image_maximalIdeal_pow E s).mem_of_tendsto
      (((hγ E).sub_const (normLimitEval K L E α)).sub_const (normLimitEval K L E β))
      (Eventually.of_forall (hT E hE α β hα hβ))

end FontaineWintenberger
