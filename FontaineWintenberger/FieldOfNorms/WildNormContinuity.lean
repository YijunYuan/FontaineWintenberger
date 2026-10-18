/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormContinuity

/-!
# Herbrand norm continuity on the actual wild finite tower

The actual cyclic prime field chain supplies every step. Composing its
proved norm moduli and actual Herbrand functions gives continuity for the
original finite-layer norm, without a continuity hypothesis in the endpoint.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger.FiniteLayer

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

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] [IsUltrametricDist Ω] in
/-- The same original integral norms compose arbitrary proved input and
output precisions through an actual triple of finite fields. -/
theorem integerNorm_sub_congruence_tower (E F G : FiniteLayer K Ω)
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

private def finitePhi (E F : FiniteLayer K Ω) (hEF : E ≤ F) (r : ℝ) : ℝ := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  exact apfPhi E.val F.val r

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem finitePhi_self (E : FiniteLayer K Ω) (r : ℝ) :
    finitePhi E E le_rfl r = r := by
  change apfPhi E.val E.val r = r
  exact apfPhi_eq_self_of_bound_eq_top E.val E.val (apfRamificationBound_self E.val) r

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
private theorem finitePhi_eq_extendScalars (E F : FiniteLayer K Ω) (hEF : E ≤ F) (r : ℝ) :
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
private theorem finitePhi_mono (E F : FiniteLayer K Ω) (hEF : E ≤ F) :
    Monotone (finitePhi E F hEF) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  exact (strictMono_apfPhi E.val F.val).monotone

private theorem finitePhi_comp (E F G : FiniteLayer K Ω)
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
    (E F : FiniteLayer K Ω) (hEF : E ≤ F)
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
        let A' : FiniteLayer K Ω := ⟨A, inferInstance⟩
        let B' : FiniteLayer K Ω := ⟨B, inferInstance⟩
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

end FontaineWintenberger.FiniteLayer
