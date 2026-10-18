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
theorem FieldOfNorms.coord_fieldOfNormsMap_of_mem_fixingSubgroup
    (E : FiniteIntermediateField K L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ E.val.fixingSubgroup)
    (x : FieldOfNorms K L) :
    FieldOfNorms.coord K L E (FieldOfNorms.map σ x) = FieldOfNorms.coord K L E x := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff E.val σ).mp hσ
  have hinv := (IntermediateField.mem_fixingSubgroup_iff E.val σ⁻¹).mp
    (E.val.fixingSubgroup.inv_mem hσ)
  have hmap : FiniteIntermediateField.map σ.symm.toAlgHom E = E := by
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
  rw [coe_fieldOfNormsEval_fieldOfNormsMap]
  exact (congrArg σ (congrArg
    (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L)) hmap)).trans
      (hfix _ (FieldOfNorms.coord K L E x).property)

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Fixing an actual deep finite field gives its prescribed original
valuation precision, uniformly for all integral original norm families. -/
theorem FieldOfNorms.valuation_sub_le_of_mem_deep_fixingSubgroup (n : ℕ)
    (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (deepFiniteTower K L (FiniteIntermediateField.bottom) n).val.fixingSubgroup) :
    ∀ (x : FieldOfNorms K L), FieldOfNorms.valuation K L x ≤ 1 →
      FieldOfNorms.valuation K L (FieldOfNorms.aut K L σ x - x) ≤
        WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
  intro x hx
  let A := (FieldOfNorms.fieldValuation K L).valuationSubring
  let a : A := ⟨x, hx⟩
  let b : A := ⟨FieldOfNorms.aut K L σ x,
    (FieldOfNorms.aut_valuation K σ x).trans_le hx⟩
  let q := FieldOfNorms.truncation K L (FiniteIntermediateField.bottom) n
  have he : FieldOfNorms.integralCoordinate K L (FiniteIntermediateField.bottom) b n =
      FieldOfNorms.integralCoordinate K L (FiniteIntermediateField.bottom) a n := by
    apply Subtype.ext
    change FieldOfNorms.coord K L _ (FieldOfNorms.map σ x) = FieldOfNorms.coord K L _ x
    exact FieldOfNorms.coord_fieldOfNormsMap_of_mem_fixingSubgroup K L _ σ hσ x
  have hq : q b = q a := congrArg (Ideal.Quotient.mk _) he
  have hz : q (b - a) = 0 := by rw [map_sub, hq, sub_self]
  exact (FieldOfNorms.truncation_eq_zero_iff K L (FiniteIntermediateField.bottom) n
    (b - a)).mp hz

/-- Every integral original family has a continuous orbit under the
original Krull topology, with its inherited original valuation topology. -/
theorem continuous_fieldOfNormsAut_apply_of_integral :
    ∀ (x : FieldOfNorms K L), FieldOfNorms.valuation K L x ≤ 1 →
      Continuous (fun σ : L ≃ₐ[K] L => FieldOfNorms.aut K L σ x) := by
  intro x hx
  apply continuous_iff_continuousAt.mpr
  intro σ₀
  have hz : Tendsto (fun σ : L ≃ₐ[K] L =>
      FieldOfNorms.aut K L σ x - FieldOfNorms.aut K L σ₀ x)
      (nhds σ₀) (nhds 0) := by
    apply (Valued.nhds_zero_hasBasis_integer_closedBall (FieldOfNorms K L)
      (FieldOfNorms.uniformizer K L)
      (FieldOfNorms.valuation_fieldOfNormsUniformizer K L)).tendsto_right_iff.mpr
    intro n _
    let E := deepFiniteTower K L (FiniteIntermediateField.bottom) n
    have hH : (E.val.fixingSubgroup : Set (L ≃ₐ[K] L)) ∈ nhds 1 :=
      E.val.fixingSubgroup_isOpen.mem_nhds (Subgroup.one_mem _)
    have ht : Tendsto (fun σ : L ≃ₐ[K] L => σ₀⁻¹ * σ) (nhds σ₀) (nhds 1) := by
      have hcont : Continuous (fun σ : L ≃ₐ[K] L => σ₀⁻¹ * σ) :=
        continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using
        hcont.continuousAt.tendsto (x := σ₀)
    filter_upwards [ht hH] with σ hσ
    have hb := FieldOfNorms.valuation_sub_le_of_mem_deep_fixingSubgroup K L
      n (σ₀⁻¹ * σ) hσ x hx
    let e := FieldOfNorms.aut K L σ₀
    have hcomp : FieldOfNorms.aut K L σ x =
        e (FieldOfNorms.aut K L (σ₀⁻¹ * σ) x) := by
      have hm := congrArg (fun a : FieldOfNorms K L ≃+* FieldOfNorms K L => a x)
        ((FieldOfNorms.aut K L).map_mul σ₀ (σ₀⁻¹ * σ))
      change FieldOfNorms.aut K L (σ₀ * (σ₀⁻¹ * σ)) x =
        FieldOfNorms.aut K L σ₀
          (FieldOfNorms.aut K L (σ₀⁻¹ * σ) x) at hm
      simpa only [mul_inv_cancel_left] using hm
    have heq : e (FieldOfNorms.aut K L (σ₀⁻¹ * σ) x - x) =
        FieldOfNorms.aut K L σ x - FieldOfNorms.aut K L σ₀ x := by
      rw [map_sub e, ← hcomp]
    have hv := FieldOfNorms.aut_valuation K σ₀
      (FieldOfNorms.aut K L (σ₀⁻¹ * σ) x - x)
    rw [heq] at hv
    exact hv.trans_le hb
  change Tendsto (fun σ : L ≃ₐ[K] L => FieldOfNorms.aut K L σ x)
    (nhds σ₀) (nhds (FieldOfNorms.aut K L σ₀ x))
  simpa only [sub_add_cancel, zero_add] using
    hz.add_const (FieldOfNorms.aut K L σ₀ x)

/-- Every original norm-field family has a continuous orbit under the
original Krull topology and the same original valuation topology. -/
theorem continuous_fieldOfNormsAut_apply :
    ∀ x : FieldOfNorms K L,
      Continuous (fun σ : L ≃ₐ[K] L => FieldOfNorms.aut K L σ x) := by
  intro x
  let A := (FieldOfNorms.fieldValuation K L).valuationSubring
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective A x
  have ha := continuous_fieldOfNormsAut_apply_of_integral K L (a : FieldOfNorms K L)
    a.property
  have hc := continuous_fieldOfNormsAut_apply_of_integral K L (b : FieldOfNorms K L)
    b.property
  have hne : (b : FieldOfNorms K L) ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hbσ (σ : L ≃ₐ[K] L) : FieldOfNorms.aut K L σ (b : FieldOfNorms K L) ≠ 0 := by
    intro h
    apply hne
    apply (FieldOfNorms.aut K L σ).injective
    exact h.trans (map_zero _).symm
  have hd := ha.div hc hbσ
  convert hd using 1
  funext σ
  change FieldOfNorms.aut K L σ x =
    FieldOfNorms.aut K L σ (a : FieldOfNorms K L) /
      FieldOfNorms.aut K L σ (b : FieldOfNorms K L)
  rw [← map_div₀]
  exact congrArg (FieldOfNorms.aut K L σ) heq.symm

end FontaineWintenberger
