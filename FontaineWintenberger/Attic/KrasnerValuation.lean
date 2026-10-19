/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.Analysis.Krasner
public import FontaineWintenberger.LocalField.Spectral.CompatibleNorm

/-!
# Krasner descent for the original chosen extension valuation

Uniqueness of the extension valuation on every actual finite simple field
identifies the spectral integer ring on a separable algebraic extension with
the original chosen valuation ring. The compatible norm then transfers the
proved complete-base Krasner theorem without changing either field element.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open IntermediateField

section AlgebraicExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation Ω Γ)
    [(NormedField.valuation (K := K)).HasExtension w]

/-- The spectral ring equals the actual chosen extension valuation ring
also in an infinite separable algebraic extension: each element is checked
in its actual finite simple subextension. -/
theorem spectralIntegerRing_eq_separable_extension_valuationSubring :
    spectralIntegerRing K Ω = w.valuationSubring := by
  let : NontriviallyNormedField Ω := spectralNorm.nontriviallyNormedField K Ω
  let : NormedAlgebra K Ω := spectralNorm.normedAlgebra K Ω
  ext x
  let E := K⟮x⟯
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  let wE : Valuation E Γ := w.comap E.val.toRingHom
  let : (NormedField.valuation (K := K)).HasExtension wE := ⟨by
    intro a b
    change (NormedField.valuation (K := K)) a ≤ (NormedField.valuation (K := K)) b ↔
      w (algebraMap K Ω a) ≤ w (algebraMap K Ω b)
    exact (Valuation.HasExtension.val_map_le_iff (NormedField.valuation (K := K)) w a b).symm⟩
  have hring := spectralIntegerRing_eq_extension_valuationSubring K E wE
  let xE : E := AdjoinSimple.gen K x
  have hmem : xE ∈ spectralIntegerRing K E ↔ xE ∈ wE.valuationSubring := by rw [hring]
  change spectralNorm K Ω x ≤ 1 ↔ w x ≤ 1
  change spectralNorm K E xE ≤ 1 ↔ w x ≤ 1 at hmem
  rw [← NormedAlgebra.norm_eq_spectralNorm K] at hmem
  exact hmem

end AlgebraicExtension

section OriginalValuation

variable (K : Type*) [Field K] (ΓK : Type*) [LinearOrderedCommGroupWithZero ΓK]
    [val : Valued K ΓK] [Valuation.IsRankOneDiscrete val.v] [CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring]
    {ΓΩ : Type*} [LinearOrderedCommGroupWithZero ΓΩ]
    (w : Valuation (SeparableClosure K) ΓΩ) [val.v.HasExtension w]

local notation "Ω" => SeparableClosure K

include ΓK val

/-- Krasner descent in the actual separable closure with its actual chosen
extension valuation. The original simple-field inclusion is the unique
embedding satisfying the same strict comparison with every other conjugate. -/
theorem discreteValued_krasner_mem_adjoin_and_unique {a b : Ω}
    (hclose : ∀ c : Ω, IsConjRoot K a c → a ≠ c → w (a - b) < w (a - c)) :
    a ∈ K⟮b⟯ ∧ ∀ f : K⟮a⟯ →ₐ[K] Ω,
      (∀ c : Ω, IsConjRoot K a c → a ≠ c →
        w (f (AdjoinSimple.gen K a) - b) < w (a - c)) → f = (K⟮a⟯).val := by
  let : Valuation.RankOne val.v :=
    Valuation.IsRankOneDiscrete.rankOne val.v (e := 2) (by norm_num)
  let : NontriviallyNormedField K := discreteValuedNormedField K ΓK
  let : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (Valued.isNonarchimedean_norm K ΓK)
  let : IsCompleteDiscreteValuedField K := discreteValued_isCompleteDiscreteValuedField K ΓK
  let : (NormedField.valuation (K := K)).HasExtension w :=
    discreteValued_norm_hasExtension K ΓK Ω w
  let : NontriviallyNormedField Ω := spectralNorm.nontriviallyNormedField K Ω
  let : NormedAlgebra K Ω := spectralNorm.normedAlgebra K Ω
  let : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra K
  have hring : (NormedField.valuation (K := Ω)).valuationSubring = w.valuationSubring :=
    spectralIntegerRing_eq_separable_extension_valuationSubring K Ω w
  have hval : (NormedField.valuation (K := Ω)).IsEquiv w :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hring
  have hle (x y : Ω) : ‖x‖ ≤ ‖y‖ ↔ w x ≤ w y := by exact_mod_cast hval x y
  have hlt (x y : Ω) : ‖x‖ < ‖y‖ ↔ w x < w y := by
    simp only [lt_iff_not_ge, hle]
  refine ⟨krasner_mem_adjoin (fun c hc hne => (hlt _ _).mpr (hclose c hc hne)), ?_⟩
  intro f hf
  apply IntermediateField.adjoin_algHom_ext K
  intro x hx
  have hx' : x = a := Set.mem_singleton_iff.mp hx
  subst x
  change f (AdjoinSimple.gen K a) = a
  by_contra hne
  have hc := isConjRoot_adjoin_simple_gen_image a f
  have hne' := Ne.symm hne
  have ha := hclose _ hc hne'
  have hf' := hf _ hc hne'
  have hbound : w (a - f (AdjoinSimple.gen K a)) ≤
      max (w (a - b)) (w (f (AdjoinSimple.gen K a) - b)) := by
    calc
      _ = w ((a - b) - (f (AdjoinSimple.gen K a) - b)) := by congr 1; ring
      _ ≤ _ := w.map_sub _ _
  exact (not_lt_of_ge hbound) (max_lt ha hf')

/-- Literal original additive-valuation Krasner statement. Comparing with
every other conjugate expresses the strict maximum bound, including the
empty-conjugate case, without introducing a separation certificate. -/
theorem discreteValued_krasner_mem_adjoin_and_unique_additive {a b : Ω}
    (hclose : ∀ c : Ω, IsConjRoot K a c → a ≠ c →
      (Valuation.toAddValuation w) (a - c) < (Valuation.toAddValuation w) (a - b)) :
    a ∈ K⟮b⟯ ∧ ∀ f : K⟮a⟯ →ₐ[K] Ω,
      (∀ c : Ω, IsConjRoot K a c → a ≠ c →
        (Valuation.toAddValuation w) (a - c) <
          (Valuation.toAddValuation w) (f (AdjoinSimple.gen K a) - b)) →
            f = (K⟮a⟯).val :=
  discreteValued_krasner_mem_adjoin_and_unique K ΓK w hclose

end OriginalValuation

end FontaineWintenberger
