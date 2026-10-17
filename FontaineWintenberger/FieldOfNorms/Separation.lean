/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Convergence

/-!
# Separation of the original norm families by deep coordinate precision

Actual Herbrand continuity transports deep coordinate errors to a fixed finite
base before its Hausdorff separation is used.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

include p

/-- Deep ideal-power agreement of integral families gives equality by
transporting every precision to one fixed original finite base. -/
theorem normLimit_ext_of_integral_eventually_sub_mem (hL : IsAPF K L)
    (α β : NormLimit K L) (hα : normLimitValuation K L hL α ≤ 1)
    (hβ : normLimitValuation K L hL β ≤ 1)
    (h : ∀ n : ℕ, ∃ T : FiniteLayer K L, ∀ F : FiniteLayer K L, T ≤ F →
      normLimitEval K L F α - normLimitEval K L F β ∈
        (fun x : spectralIntegerRing K F.val => (x : F.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ n :
            Ideal (spectralIntegerRing K F.val)) : Set (spectralIntegerRing K F.val))) :
    α = β := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_wild_tail K L p hL
  apply NormLimit.ext K L
  intro D
  let B := FiniteLayer.sup D T
  have hTB : T ≤ B := FiniteLayer.le_sup_right D T
  have hDB : D ≤ B := FiniteLayer.le_sup_left D T
  let := spectralNorm.nontriviallyNormedField K B.val
  let := spectralNorm.normedAlgebra K B.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := B.val))
  let := spectralNorm.completeSpace K B.val
  let := normedAlgebra_unitBall_isDiscreteValuationRing K B.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K B.val L
  have hmem (N : ℕ) :
      normLimitEval K L B α - normLimitEval K L B β ∈
        (fun x : spectralIntegerRing K B.val => (x : B.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K B.val) ^ N :
            Ideal (spectralIntegerRing K B.val)) : Set (spectralIntegerRing K B.val)) := by
    let s := ⌈apfPsi B.val L (N : ℝ)⌉₊
    have hs : apfPsi B.val L (N : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
    obtain ⟨U, hU⟩ := h s
    let F := FiniteLayer.sup B U
    have hBF : B ≤ F := FiniteLayer.le_sup_left B U
    let : Algebra B.val F.val := (IntermediateField.inclusion hBF).toRingHom.toAlgebra
    let : IsScalarTower K B.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := B.val) (L := F.val)
    let x : spectralIntegerRing K F.val :=
      ⟨normLimitEval K L F α, normLimitEval_mem_of_valuation_le_one K L hL α hα F⟩
    let y : spectralIntegerRing K F.val :=
      ⟨normLimitEval K L F β, normLimitEval_mem_of_valuation_le_one K L hL β hβ F⟩
    obtain ⟨d, hd, heq⟩ := hU F (FiniteLayer.le_sup_right B U)
    have hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s := by
      have heq' : x - y = d := Subtype.ext heq.symm
      rw [heq']
      exact hd
    obtain ⟨_, ⟨n, hn⟩, he⟩ := hT B F hTB hBF
    have hc := FiniteLayer.integerNorm_sub_congruence_of_totallyRamified
      B F hBF p he n hn s x y hxy
    have hprecision := FiniteLayer.le_ceil_apfPhi_of_apfPsi_le K L hL B F hBF N s hs
    refine ⟨FiniteLayer.integerNorm B F hBF x - FiniteLayer.integerNorm B F hBF y,
      Ideal.pow_le_pow_right hprecision hc, ?_⟩
    change (FiniteLayer.integerNorm B F hBF x : B.val) -
      (FiniteLayer.integerNorm B F hBF y : B.val) = _
    rw [FiniteLayer.coe_integerNorm B F hBF x, FiniteLayer.coe_integerNorm B F hBF y]
    exact congrArg₂ (fun a b : B.val => a - b)
      (normLimitEval_norm K L B F hBF α) (normLimitEval_norm K L B F hBF β)
  have hz : normLimitEval K L B α - normLimitEval K L B β = 0 := by
    have ht : Tendsto (fun _ : ℕ => normLimitEval K L B α - normLimitEval K L B β)
        atTop (nhds 0) :=
      (FiniteLayer.nhds_zero_hasBasis_maximalIdeal_pow B).tendsto_right_iff.mpr
        (fun N _ => Eventually.of_forall fun _ => hmem N)
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hB := sub_eq_zero.mp hz
  have hnorm := congrArg (FiniteLayer.norm D B hDB) hB
  simpa only [normLimitEval_norm] using hnorm

/-- Asymptotic ideal-power agreement separates arbitrary original norm
families. An existing maximal-valued family makes all normalization integral. -/
theorem normLimit_ext_of_eventually_sub_mem (hL : IsAPF K L)
    (α β : NormLimit K L)
    (h : ∀ n : ℕ, ∃ T : FiniteLayer K L, ∀ F : FiniteLayer K L, T ≤ F →
      normLimitEval K L F α - normLimitEval K L F β ∈
        (fun x : spectralIntegerRing K F.val => (x : F.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ n :
            Ideal (spectralIntegerRing K F.val)) : Set (spectralIntegerRing K F.val))) :
    α = β := by
  classical
  let w := normLimitValuation K L hL
  let S : Finset (NormLimit K L) := {1, α, β}
  obtain ⟨δ, _, hmax⟩ := Finset.exists_max_image S w ⟨1, by simp [S]⟩
  have hone : 1 ≤ w δ := by simpa only [map_one] using hmax 1 (by simp [S])
  have hδpos : 0 < w δ := zero_lt_one.trans_le hone
  have hδ : δ ≠ 0 := by
    intro hδ
    rw [hδ, map_zero] at hone
    exact not_le_of_gt zero_lt_one hone
  have ha : w (α / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax α (by simp [S]))
  have hb : w (β / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax β (by simp [S]))
  have hi : w δ⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hone
  have heq := normLimit_ext_of_integral_eventually_sub_mem K L p hL
    (α / δ) (β / δ) ha hb (fun n => ?_)
  · simpa [div_eq_mul_inv, mul_assoc, hδ] using
      congrArg (fun x : NormLimit K L => x * δ) heq
  · obtain ⟨T, hT⟩ := h n
    refine ⟨T, fun F hF => ?_⟩
    obtain ⟨d, hd, hdeq⟩ := hT F hF
    let z : spectralIntegerRing K F.val :=
      ⟨normLimitEval K L F δ⁻¹, normLimitEval_mem_of_valuation_le_one K L hL δ⁻¹ hi F⟩
    refine ⟨z * d, Ideal.mul_mem_left _ z hd, ?_⟩
    change normLimitEval K L F δ⁻¹ * (d : F.val) = _
    change (d : F.val) = normLimitEval K L F α - normLimitEval K L F β at hdeq
    rw [hdeq, map_inv₀, map_div₀, map_div₀]
    simp only [div_eq_mul_inv]
    ring

end FontaineWintenberger
