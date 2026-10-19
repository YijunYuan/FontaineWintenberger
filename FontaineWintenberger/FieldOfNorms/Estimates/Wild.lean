/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Estimates.Prime
public import FontaineWintenberger.Ramification.Fields.PrimeTower
public import FontaineWintenberger.Ramification.Fields.Wild
public import FontaineWintenberger.APF.BaseChange.Bounds

/-!
# Norm congruences on fields above wild inertia

The cyclic prime-degree chain, its proved total ramification and
its common intrinsic first bound supply every prime-step congruence.
Composition uses the finite-layer integral norm maps.

## Main results

* `integerNorm_add_congruence_of_wild_field`: The norm congruence above the wild fixed field.

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
    [FiniteDimensional K Ω] [IsGalois K Ω]

local instance wildNorm_completeSpace (E : FiniteIntermediateField K Ω) : CompleteSpace E.val :=
  FiniteDimensional.complete K E.val
local instance wildNorm_discreteValuationRing (E : FiniteIntermediateField K Ω) :
    IsCompleteDiscreteValuedField E.val :=
  normedAlgebra_isCompleteDiscreteValuedField K E.val
local instance wildNorm_perfectField (E : FiniteIntermediateField K Ω) : PerfectField
    𝓀[E.val] :=
  Algebra.IsAlgebraic.perfectField 𝓀[K]

local notation "P" => lowerRamificationGroup (Ω ≃ₐ[K] Ω)
  (IsLocalRing.maximalIdeal (spectralIntegerRing K Ω)) 1

/-- The norm congruence above the wild fixed field. All prime-step
congruences, total ramification and the common first bound are proved. -/
theorem integerNorm_add_congruence_of_wild_field (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (E F : FiniteIntermediateField K Ω) (hEF : E ≤ F)
    (hE : IntermediateField.fixedField P ≤ E.val)
    (b : ℝ) (hb : (b : EReal) ≤
      apfRamificationBound E.val (IntermediateField.extendScalars hEF)) :
    ∀ x y : spectralIntegerRing K F.val,
      integerNorm E F hEF (x + y) - integerNorm E F hEF x - integerNorm E F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
  have hfix : E.val.fixingSubgroup ≤ P := by
    simpa only [IntermediateField.fixingSubgroup_fixedField] using
      IntermediateField.fixingSubgroup_le hE
  have hpgroup : IsPGroup p E.val.fixingSubgroup :=
    (lowerRamificationGroup_one_isPGroup (Ω ≃ₐ[K] Ω) p).of_injective
      (Subgroup.inclusion hfix) (Subgroup.inclusion_injective _)
  have hchain := relative_prime_field_chain K Ω p E.val F.val hEF hpgroup
  let r := ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊
  have hmain : ∀ (A : IntermediateField K Ω),
      Relation.ReflTransGen
        (fun A B : IntermediateField K Ω => ∃ hAB : A ≤ B,
          IsGalois A (IntermediateField.extendScalars hAB) ∧
          Module.finrank A (IntermediateField.extendScalars hAB) = p ∧
          IsCyclic ((IntermediateField.extendScalars hAB) ≃ₐ[A]
            IntermediateField.extendScalars hAB)) A F.val →
      E.val ≤ A → ∃ hAF : A ≤ F.val,
        ∀ x y : spectralIntegerRing K F.val,
          integerNorm ⟨A, inferInstance⟩ F hAF (x + y) -
            integerNorm ⟨A, inferInstance⟩ F hAF x -
            integerNorm ⟨A, inferInstance⟩ F hAF y ∈
              IsLocalRing.maximalIdeal (spectralIntegerRing K A) ^ r := by
    intro A hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro _
        refine ⟨le_rfl, fun x y => ?_⟩
        simp only [integerNorm_self, add_sub_cancel_left, sub_self, Ideal.zero_mem]
    | @head A B hstep hc ih =>
        intro hEA
        obtain ⟨hAB, hg, hd, _⟩ := hstep
        obtain ⟨hBF, htail⟩ := ih (hEA.trans hAB)
        have he := wildField_step_ramificationIdx_eq_finrank K Ω A B hAB (hE.trans hEA)
        have : FiniteDimensional E.val Ω := Module.Finite.right K E.val Ω
        have : IsGalois E.val Ω := IsGalois.tower_top_of_isGalois K E.val Ω
        let A' := IntermediateField.extendScalars hEA
        let B' := IntermediateField.extendScalars (hEA.trans hAB)
        let F' := IntermediateField.extendScalars hEF
        have hAB' : A' ≤ B' := hAB
        have hBF' : B' ≤ F' := hBF
        have hb' := hb.trans
          (apfRamificationBound_le_step_of_finiteGalois E.val Ω A' B' F' hAB' hBF')
        have hnorm := integerNorm_prime_add_congruence_of_bound
          (⟨A, inferInstance⟩ : FiniteIntermediateField K Ω) ⟨B, inferInstance⟩ hAB p hg hd he b hb'
        exact ⟨hAB.trans hBF, integerNorm_add_congruence_tower
          ⟨A, inferInstance⟩ ⟨B, inferInstance⟩ F hAB hBF hnorm htail⟩
  obtain ⟨_, hn⟩ := hmain E.val hchain le_rfl
  exact hn

end FontaineWintenberger.FiniteIntermediateField
