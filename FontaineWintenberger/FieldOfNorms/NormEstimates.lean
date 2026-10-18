/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.TameNorms
public import FontaineWintenberger.APF.PrimeDegree

/-!
# Norm estimates for the original arbitrary finite separable extension

A genuine finite Galois closure supplies the tame reduction; canonical
integer-ring equivalences transport its proved estimate to the original
field. Finite perfect-residue digits then supply norm approximation.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

attribute [local instance] FractionRing.liftAlgebra

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- The actual intermediate field may be nonnormal; its own integer-ring
total ramification supplies the genuine tame norm estimate. -/
theorem exists_intNorm_add_congruence_of_totallyRamified_intermediateField
    (Ω : Type*) [NontriviallyNormedField Ω] [NormedAlgebra K Ω] [IsUltrametricDist Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (M : IntermediateField K Ω)
    (he : (IsLocalRing.maximalIdeal (spectralIntegerRing K M)).ramificationIdx R =
      Module.finrank K M)
    (n : ℕ) (hd : Module.finrank K M = p ^ n) (hdegree : 1 < Module.finrank K M) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K M = (b : EReal) ∧
      ∀ x y : spectralIntegerRing K M,
        Algebra.intNorm R (spectralIntegerRing K M) (x + y) -
          Algebra.intNorm R (spectralIntegerRing K M) x -
          Algebra.intNorm R (spectralIntegerRing K M) y ∈ IsLocalRing.maximalIdeal R ^
            ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
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
  exact exists_intNorm_add_congruence_of_totallyRamified_fixedField K Ω p H he' n hd hdegree

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]

local notation "S" => spectralIntegerRing K L

/-- The original arbitrary totally ramified p-power extension has the
actual quantitative norm addition estimate. Normality is not required. -/
theorem exists_intNorm_add_congruence_of_totallyRamified
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    (n : ℕ) (hd : Module.finrank K L = p ^ n) (hdegree : 1 < Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K L = (b : EReal) ∧
      ∀ x y : S, Algebra.intNorm R S (x + y) - Algebra.intNorm R S x -
        Algebra.intNorm R S y ∈ IsLocalRing.maximalIdeal R ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ := by
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
  obtain ⟨b, hb, hbound, hadd⟩ :=
    exists_intNorm_add_congruence_of_totallyRamified_intermediateField K Ω p M heM n
      (hn.trans hd) (by simpa only [hn] using hdegree)
  refine ⟨b, hb, ?_, ?_⟩
  · rw [apfRamificationBound_algEquiv K L e]
    exact hbound
  · intro x y
    let f := spectralIntegerRingEquiv K e
    have h := hadd (f x) (f y)
    simpa only [← map_add f, Algebra.intNorm_map_algEquiv] using h

/-- Both actual norm estimates for every nontrivial finite separable totally
ramified p-power extension, with arbitrary perfect residue field. -/
theorem exists_intNorm_estimates_of_totallyRamified
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    (n : ℕ) (hd : Module.finrank K L = p ^ n) (hdegree : 1 < Module.finrank K L) :
    ∃ b : ℝ, 0 ≤ b ∧ apfRamificationBound K L = (b : EReal) ∧
      (∀ x y : S, Algebra.intNorm R S (x + y) - Algebra.intNorm R S x -
        Algebra.intNorm R S y ∈ IsLocalRing.maximalIdeal R ^
          ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) ∧
      (∀ a : R, ∃ α : S, Algebra.intNorm R S α - a ∈
        IsLocalRing.maximalIdeal R ^ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) := by
  obtain ⟨b, hb, hbound, hadd⟩ :=
    exists_intNorm_add_congruence_of_totallyRamified K L p he n hd hdegree
  refine ⟨b, hb, hbound, hadd, ?_⟩
  exact extensionValuationSubring_exists_intNorm_sub_mem_maximalIdeal_pow
    K L (spectralValuation K L) p n ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ he hd hadd

end FontaineWintenberger
