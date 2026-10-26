/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Continuous Laurent maps and ordinary power-series substitution

The topology on Laurent series is its valuation topology.

## Main results

* `continuous_ofPowerSeries_valued`: The usual inclusion is continuous into the Laurent valuation
  topology.
* `continuous_powerSeries_subst`: Ordinary substitution is continuous for the coefficientwise
  topology.
* `map_ofPowerSeries_eq_subst`: A continuous coefficient-fixing Laurent homomorphism acts on every
  power series by ordinary substitution at the image of the parameter.
* `comp_apply_parameter`: Composition of the Laurent maps reverses the order of their parameter
  power series: the parameter of `F.comp G` is the series of `G` substituted at that of `F`.
* `iterate_ofPowerSeries_eq_subst_iterate`: Ordinary function iteration of the Laurent map restricts
  to ordinary function iteration of the usual power-series substitution.
* `iterate_apply_parameter_eq_subst_iterate`: The parameter image of every iterate uses the same
  canonical substitution.
-/

@[expose] public section

noncomputable section

open Filter WithZero
open scoped Topology PowerSeries.WithPiTopology LaurentSeries

namespace FontaineWintenberger

variable {k : Type*} [Field k]

section DiscreteCoefficients

variable [UniformSpace k] [DiscreteUniformity k]

/-- The usual inclusion is continuous into the Laurent valuation topology. -/
theorem continuous_ofPowerSeries_valued :
    Continuous (HahnSeries.ofPowerSeries ℤ k : PowerSeries k → LaurentSeries k) := by
  apply continuous_of_tendsto_nhds_zero (HahnSeries.ofPowerSeries ℤ k).toAddMonoidHom
  rw [(Valued.hasBasis_nhds_zero (LaurentSeries k) ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  have hT : Valued.v ((PowerSeries.X : PowerSeries k) : LaurentSeries k) ≤ exp (-1) := by
    simpa using (LaurentSeries.valuation_X_pow k 1).le
  have ht := Valued.tendsto_zero_pow_of_le_exp_neg_one hT
  have hγ := ht.eventually
    ((Valued.hasBasis_nhds_zero (LaurentSeries k) ℤᵐ⁰).mem_of_mem (i := γ) trivial)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hγ
  have hcoeff : ∀ M : ℕ, ∀ᶠ A : PowerSeries k in 𝓝 0,
      ∀ n < M, A.coeff n = 0 := by
    intro M
    induction M with
    | zero => exact Filter.Eventually.of_forall (by simp)
    | succ M ih =>
      have hc : ∀ᶠ A : PowerSeries k in 𝓝 0, A.coeff M = 0 := by
        have ho : ({0} : Set k) ∈ 𝓝 ((PowerSeries.coeff M) (0 : PowerSeries k)) := by
          simp
        exact (PowerSeries.WithPiTopology.continuous_coeff k M).continuousAt.eventually ho
      filter_upwards [ih, hc] with A hA hM n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · exact hA n hn
      · exact hM
  filter_upwards [hcoeff N] with A hA
  apply lt_of_le_of_lt _ (hN N le_rfl)
  apply (Valuation.restrict_le_iff Valued.v).mpr
  change Valued.v (A : LaurentSeries k) ≤
    Valued.v (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ N)
  rw [LaurentSeries.valuation_X_pow]
  exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero k A).mpr hA

attribute [local instance] DiscreteTopology.instContinuousSMul

/-- Ordinary substitution is continuous for the coefficientwise topology. -/
theorem continuous_powerSeries_subst (g : PowerSeries k) (hg : g.constantCoeff = 0) :
    Continuous (PowerSeries.subst g : PowerSeries k → PowerSeries k) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [← PowerSeries.coe_substAlgHom hs, PowerSeries.substAlgHom_eq_aeval]
  exact PowerSeries.continuous_aeval _

end DiscreteCoefficients

/-- A continuous coefficient-fixing Laurent homomorphism acts on every power series
by ordinary substitution at the image of the parameter. -/
theorem map_ofPowerSeries_eq_subst
    (F : LaurentSeries k →+* LaurentSeries k) (hF : Continuous F)
    (hC : ∀ a, F (HahnSeries.C a) = HahnSeries.C a)
    (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k g)
    (A : PowerSeries k) :
    F (HahnSeries.ofPowerSeries ℤ k A) = HahnSeries.ofPowerSeries ℤ k (A.subst g) := by
  let : UniformSpace k := ⊥
  let j := HahnSeries.ofPowerSeries ℤ k
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  let s := (PowerSeries.substAlgHom hs : PowerSeries k →ₐ[k] PowerSeries k).toRingHom
  have hj : Continuous j := continuous_ofPowerSeries_valued
  have hsc : Continuous s := by
    simpa only [s, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      PowerSeries.coe_substAlgHom] using continuous_powerSeries_subst g hg
  have hp : (F.comp j).comp Polynomial.coeToPowerSeries.ringHom =
      (j.comp s).comp Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, s, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
      change F (j (PowerSeries.C a)) = j (PowerSeries.C a)
      simpa only [j, HahnSeries.ofPowerSeries_C] using hC a
    · simpa [j, s, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs] using hX
  have heq := (PowerSeries.WithPiTopology.denseRange_toPowerSeries k).equalizer
    (g := F.comp j) (h := j.comp s) (hF.comp hj) (hj.comp hsc)
    (congrArg DFunLike.coe hp)
  simpa only [RingHom.comp_apply, j, s, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    PowerSeries.coe_substAlgHom] using congr_fun heq A

/-- Composition of the Laurent maps reverses the order of their parameter
power series: the parameter of `F.comp G` is the series of `G` substituted at that of `F`. -/
theorem comp_apply_parameter
    (F : LaurentSeries k →+* LaurentSeries k) (hF : Continuous F)
    (hC : ∀ a, F (HahnSeries.C a) = HahnSeries.C a)
    (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k g)
    (G : LaurentSeries k →+* LaurentSeries k) (h : PowerSeries k)
    (hG : G (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k h) :
    (F.comp G) (HahnSeries.single (1 : ℤ) (1 : k)) =
      HahnSeries.ofPowerSeries ℤ k (h.subst g) := by
  rw [RingHom.comp_apply, hG]
  exact map_ofPowerSeries_eq_subst F hF hC g hg hX h

/-- Ordinary function iteration of the Laurent map restricts to ordinary
function iteration of the usual power-series substitution. -/
theorem iterate_ofPowerSeries_eq_subst_iterate
    (F : LaurentSeries k →+* LaurentSeries k) (hF : Continuous F)
    (hC : ∀ a, F (HahnSeries.C a) = HahnSeries.C a)
    (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k g)
    (A : PowerSeries k) (n : ℕ) :
    (F : LaurentSeries k → LaurentSeries k)^[n] (HahnSeries.ofPowerSeries ℤ k A) =
      HahnSeries.ofPowerSeries ℤ k
        ((PowerSeries.subst g : PowerSeries k → PowerSeries k)^[n] A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_ofPowerSeries_eq_subst F hF hC g hg hX,
      Function.iterate_succ_apply']

/-- The parameter image of every iterate uses the same canonical substitution. -/
theorem iterate_apply_parameter_eq_subst_iterate
    (F : LaurentSeries k →+* LaurentSeries k) (hF : Continuous F)
    (hC : ∀ a, F (HahnSeries.C a) = HahnSeries.C a)
    (g : PowerSeries k) (hg : g.constantCoeff = 0)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k g)
    (n : ℕ) :
    (F : LaurentSeries k → LaurentSeries k)^[n] (HahnSeries.single (1 : ℤ) (1 : k)) =
      HahnSeries.ofPowerSeries ℤ k
        ((PowerSeries.subst g : PowerSeries k → PowerSeries k)^[n] PowerSeries.X) := by
  simpa only [HahnSeries.ofPowerSeries_X] using
    iterate_ofPowerSeries_eq_subst_iterate F hF hC g hg hX PowerSeries.X n

end FontaineWintenberger
