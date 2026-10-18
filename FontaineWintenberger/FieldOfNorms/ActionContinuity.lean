/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Completeness
public import FontaineWintenberger.FieldOfNorms.Isomorphism
public import Mathlib.FieldTheory.KrullTopology

/-!
# Continuity of the original Krull action on the norm field

Original finite-field fixers give uniform precision on every integral norm
family through the actual truncated-coordinate ring homomorphism. Therefore
all original automorphism orbits are continuous for the same valuation topology.

Reference: the continuity used in Yuan, Lemma 5.3, page 12.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace FontaineWintenberger

section Fields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- An original finite-field fixer fixes that finite coordinate of every
original norm-compatible family, without a normality hypothesis. -/
theorem normLimitEval_normLimitMap_of_mem_fixingSubgroup
    (E : FiniteLayer K L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ E.val.fixingSubgroup)
    (x : NormLimit K L) :
    normLimitEval K L E (normLimitMap σ x) = normLimitEval K L E x := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff E.val σ).mp hσ
  have hinv := (IntermediateField.mem_fixingSubgroup_iff E.val σ⁻¹).mp
    (E.val.fixingSubgroup.inv_mem hσ)
  have hmap : FiniteLayer.map σ.symm.toAlgHom E = E := by
    apply Subtype.ext
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change σ.symm z ∈ E.val
      have he : σ.symm z = z := hinv z hz
      rwa [he]
    · intro hy
      exact ⟨y, hy, hinv y hy⟩
  apply Subtype.val_injective
  rw [coe_normLimitEval_normLimitMap]
  exact (congrArg σ (congrArg
    (fun D : FiniteLayer K L => (normLimitEval K L D x : L)) hmap)).trans
      (hfix _ (normLimitEval K L E x).property)

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Fixing an actual deep finite field gives its prescribed original
valuation precision, uniformly for all integral original norm families. -/
theorem normLimitValuation_sub_le_of_mem_deep_fixingSubgroup (n : ℕ)
    (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (deepFiniteTower K L p (FiniteLayer.bottom) n).val.fixingSubgroup) :
    letI := normLimitField K L p
    ∀ (x : NormLimit K L), normLimitValuation K L x ≤ 1 →
      normLimitValuation K L (normLimitAut K L p σ x - x) ≤
        WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
  let := normLimitField K L p
  intro x hx
  let A := (normLimitFieldValuation K L p).valuationSubring
  let a : A := ⟨x, hx⟩
  let b : A := ⟨normLimitAut K L p σ x,
    (normLimitAut_valuation K p σ x).trans_le hx⟩
  let q := normLimitTruncation K L p (FiniteLayer.bottom) n
  have he : normLimitIntegralCoordinate K L p (FiniteLayer.bottom) b n =
      normLimitIntegralCoordinate K L p (FiniteLayer.bottom) a n := by
    apply Subtype.ext
    change normLimitEval K L _ (normLimitMap σ x) = normLimitEval K L _ x
    exact normLimitEval_normLimitMap_of_mem_fixingSubgroup K L _ σ hσ x
  have hq : q b = q a := congrArg (Ideal.Quotient.mk _) he
  have hz : q (b - a) = 0 := by rw [map_sub, hq, sub_self]
  exact (normLimitTruncation_eq_zero_iff K L p (FiniteLayer.bottom) n
    (b - a)).mp hz

/-- Every integral original family has a continuous orbit under the
original Krull topology, with its inherited original valuation topology. -/
theorem continuous_normLimitAut_apply_of_integral :
    letI := normLimitField K L p
    letI := normLimitValued K L p
    ∀ (x : NormLimit K L), normLimitValuation K L x ≤ 1 →
      Continuous (fun σ : L ≃ₐ[K] L => normLimitAut K L p σ x) := by
  let := normLimitField K L p
  let := normLimitValued K L p
  intro x hx
  apply continuous_iff_continuousAt.mpr
  intro σ₀
  have hz : Tendsto (fun σ : L ≃ₐ[K] L =>
      normLimitAut K L p σ x - normLimitAut K L p σ₀ x)
      (nhds σ₀) (nhds 0) := by
    apply (Valued.nhds_zero_hasBasis_integer_closedBall (NormLimit K L)
      (normLimitUniformizer K L p)
      (normLimitValuation_normLimitUniformizer K L p)).tendsto_right_iff.mpr
    intro n _
    let E := deepFiniteTower K L p (FiniteLayer.bottom) n
    have hH : (E.val.fixingSubgroup : Set (L ≃ₐ[K] L)) ∈ nhds 1 :=
      E.val.fixingSubgroup_isOpen.mem_nhds (Subgroup.one_mem _)
    have ht : Tendsto (fun σ : L ≃ₐ[K] L => σ₀⁻¹ * σ) (nhds σ₀) (nhds 1) := by
      have hcont : Continuous (fun σ : L ≃ₐ[K] L => σ₀⁻¹ * σ) :=
        continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using
        hcont.continuousAt.tendsto (x := σ₀)
    filter_upwards [ht hH] with σ hσ
    have hb := normLimitValuation_sub_le_of_mem_deep_fixingSubgroup K L p
      n (σ₀⁻¹ * σ) hσ x hx
    let e := normLimitAut K L p σ₀
    have hcomp : normLimitAut K L p σ x =
        e (normLimitAut K L p (σ₀⁻¹ * σ) x) := by
      have hm := congrArg (fun a : NormLimit K L ≃+* NormLimit K L => a x)
        ((normLimitAut K L p).map_mul σ₀ (σ₀⁻¹ * σ))
      change normLimitAut K L p (σ₀ * (σ₀⁻¹ * σ)) x =
        normLimitAut K L p σ₀
          (normLimitAut K L p (σ₀⁻¹ * σ) x) at hm
      simpa only [mul_inv_cancel_left] using hm
    have heq : e (normLimitAut K L p (σ₀⁻¹ * σ) x - x) =
        normLimitAut K L p σ x - normLimitAut K L p σ₀ x := by
      rw [map_sub e, ← hcomp]
    have hv := normLimitAut_valuation K p σ₀
      (normLimitAut K L p (σ₀⁻¹ * σ) x - x)
    rw [heq] at hv
    exact hv.trans_le hb
  change Tendsto (fun σ : L ≃ₐ[K] L => normLimitAut K L p σ x)
    (nhds σ₀) (nhds (normLimitAut K L p σ₀ x))
  simpa only [sub_add_cancel, zero_add] using
    hz.add_const (normLimitAut K L p σ₀ x)

/-- Every original norm-field family has a continuous orbit under the
original Krull topology and the same original valuation topology. -/
theorem continuous_normLimitAut_apply :
    letI := normLimitField K L p
    letI := normLimitValued K L p
    ∀ x : NormLimit K L,
      Continuous (fun σ : L ≃ₐ[K] L => normLimitAut K L p σ x) := by
  let := normLimitField K L p
  let := normLimitValued K L p
  intro x
  let A := (normLimitFieldValuation K L p).valuationSubring
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective A x
  have ha := continuous_normLimitAut_apply_of_integral K L p (a : NormLimit K L)
    a.property
  have hc := continuous_normLimitAut_apply_of_integral K L p (b : NormLimit K L)
    b.property
  have hne : (b : NormLimit K L) ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hbσ (σ : L ≃ₐ[K] L) : normLimitAut K L p σ (b : NormLimit K L) ≠ 0 := by
    intro h
    apply hne
    apply (normLimitAut K L p σ).injective
    exact h.trans (map_zero _).symm
  have hd := ha.div hc hbσ
  convert hd using 1
  funext σ
  change normLimitAut K L p σ x =
    normLimitAut K L p σ (a : NormLimit K L) /
      normLimitAut K L p σ (b : NormLimit K L)
  rw [← map_div₀]
  exact congrArg (normLimitAut K L p σ) heq.symm

end FontaineWintenberger
