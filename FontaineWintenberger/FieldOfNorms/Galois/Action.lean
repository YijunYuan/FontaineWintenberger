/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import FontaineWintenberger.FieldOfNorms.Functor.Galois
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The absolute Galois action on the field of norms

## Continuity of the Krull action on the norm field

Finite-field fixers give uniform precision on every integral norm
family through the truncated-coordinate ring homomorphism. Therefore
all automorphism orbits are continuous for the same valuation topology.

Reference: the continuity used in Yuan, Lemma 5.3, page 12.

## The absolute base action on the norm field

For a normal intermediate field of the separable closure, compose
ordinary Galois restriction with the existing norm-field action.
The action preserves the coordinates and valuation, has continuous
orbits, and has exactly the pointwise fixer of the intermediate field as kernel.

This is the restriction to the base norm field in Wintenberger, Remark 3.2.4.

## Main definitions

* `FieldOfNorms.absoluteAut`: The absolute Galois group acts on the norm field through its ordinary
  restriction to the given normal APF extension.

## Main results

* `FieldOfNorms.coord_mapEquiv_of_mem_fixingSubgroup`: A finite-field fixer fixes that finite
  coordinate of every norm-compatible family, without a normality hypothesis.
* `FieldOfNorms.valuation_sub_le_of_mem_deep_fixingSubgroup`: Fixing a deep finite field gives its
  prescribed valuation precision, uniformly for all integral norm families.
* `FieldOfNorms.continuous_aut_apply_of_integral`: Every integral family has a continuous orbit
  under the Krull topology, with its inherited valuation topology.
* `FieldOfNorms.continuous_aut_apply`: Every norm-field family has a continuous orbit under the
  Krull topology and the valuation topology.
* `FieldOfNorms.absoluteAut_apply`: The absolute base action factors through the Galois restriction.
* `FieldOfNorms.coe_coord_absoluteAut`: The coordinate formula, viewed in the same separable
  closure.
* `FieldOfNorms.absoluteAut_valuation`: Absolute Galois transport preserves the normalized
  valuation.
* `FieldOfNorms.continuous_absoluteAut_apply`: Every absolute Galois orbit is continuous for the
  Krull and norm-field valuation topologies.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace FontaineWintenberger

section Fields

variable (K L : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A finite-field fixer fixes that finite coordinate of every
norm-compatible family, without a normality hypothesis. -/
theorem FieldOfNorms.coord_mapEquiv_of_mem_fixingSubgroup
    (E : FiniteIntermediateField K L) (σ : L ≃ₐ[K] L) (hσ : σ ∈ E.val.fixingSubgroup)
    (x : FieldOfNorms K L) :
    FieldOfNorms.coord K L E (FieldOfNorms.mapEquiv σ x) = FieldOfNorms.coord K L E x := by
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
  rw [FieldOfNorms.coe_coord_mapEquiv]
  exact (congrArg σ (congrArg
    (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L)) hmap)).trans
      (hfix _ (FieldOfNorms.coord K L E x).property)

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Fixing a deep finite field gives its prescribed
valuation precision, uniformly for all integral norm families. -/
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
    change FieldOfNorms.coord K L _ (FieldOfNorms.mapEquiv σ x) = FieldOfNorms.coord K L _ x
    exact FieldOfNorms.coord_mapEquiv_of_mem_fixingSubgroup K L _ σ hσ x
  have hq : q b = q a := congrArg (Ideal.Quotient.mk _) he
  have hz : q (b - a) = 0 := by rw [map_sub, hq, sub_self]
  exact (FieldOfNorms.truncation_eq_zero_iff K L (FiniteIntermediateField.bottom) n
    (b - a)).mp hz

/-- Every integral family has a continuous orbit under the
Krull topology, with its inherited valuation topology. -/
theorem FieldOfNorms.continuous_aut_apply_of_integral :
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
      (FieldOfNorms.valuation_uniformizer K L)).tendsto_right_iff.mpr
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

/-- Every norm-field family has a continuous orbit under the
Krull topology and the valuation topology. -/
theorem FieldOfNorms.continuous_aut_apply :
    ∀ x : FieldOfNorms K L,
      Continuous (fun σ : L ≃ₐ[K] L => FieldOfNorms.aut K L σ x) := by
  intro x
  let A := (FieldOfNorms.fieldValuation K L).valuationSubring
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective A x
  have ha := FieldOfNorms.continuous_aut_apply_of_integral K L (a : FieldOfNorms K L)
    a.property
  have hc := FieldOfNorms.continuous_aut_apply_of_integral K L (b : FieldOfNorms K L)
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

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable (L : IntermediateField K Ω) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The absolute Galois group acts on the norm field through
its ordinary restriction to the given normal APF extension. -/
def FieldOfNorms.absoluteAut :
    (Ω ≃ₐ[K] Ω) →*
      (FieldOfNorms K L ≃+* FieldOfNorms K L) := by
  exact (FieldOfNorms.aut K L).comp (AlgEquiv.restrictNormalHom L)

/-- The absolute base action factors through the Galois restriction. -/
@[simp]
theorem FieldOfNorms.absoluteAut_apply (σ : Ω ≃ₐ[K] Ω)
    (x : FieldOfNorms K L) :
    FieldOfNorms.absoluteAut K L σ x =
      FieldOfNorms.aut K L (AlgEquiv.restrictNormalHom L σ) x := rfl

/-- The coordinate formula, viewed in the same separable closure. -/
theorem FieldOfNorms.coe_coord_absoluteAut
    (σ : Ω ≃ₐ[K] Ω)
    (x : FieldOfNorms K L) (E : FiniteIntermediateField K L) :
    ((FieldOfNorms.coord K L E (FieldOfNorms.absoluteAut K L σ x) : L) :
        Ω) =
      σ ((FieldOfNorms.coord K L
        (FiniteIntermediateField.map (AlgEquiv.restrictNormalHom L σ).symm.toAlgHom E) x : L) :
          Ω) := by
  let τ := AlgEquiv.restrictNormalHom L σ
  change ((FieldOfNorms.coord K L E (FieldOfNorms.mapEquiv τ x) : L) : Ω) = _
  calc
    _ = ((τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.symm.toAlgHom E) x) : L) :
        Ω) :=
      congrArg (fun y : L => (y : Ω))
        (FieldOfNorms.coe_coord_mapEquiv τ x E)
    _ = _ := AlgEquiv.restrictNormalHom_apply L σ _

/-- Absolute Galois transport preserves the normalized valuation. -/
theorem FieldOfNorms.absoluteAut_valuation
    (σ : Ω ≃ₐ[K] Ω) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.absoluteAut K L σ x) =
      FieldOfNorms.valuation K L x :=
  FieldOfNorms.aut_valuation K (AlgEquiv.restrictNormalHom L σ) x

/-- Every absolute Galois orbit is continuous for the Krull and
norm-field valuation topologies. -/
theorem FieldOfNorms.continuous_absoluteAut_apply :
    ∀ x : FieldOfNorms K L,
      Continuous (fun σ : Ω ≃ₐ[K] Ω =>
        FieldOfNorms.absoluteAut K L σ x) := by
  intro x
  exact (FieldOfNorms.continuous_aut_apply K L x).comp
    (InfiniteGalois.restrictNormalHom_continuous L)

/-- The kernel is exactly the pointwise fixer of the field `L`. -/
theorem FieldOfNorms.absoluteAut_ker :
    (FieldOfNorms.absoluteAut K L).ker = L.fixingSubgroup := by
  rw [← L.restrictNormalHom_ker]
  ext σ
  change FieldOfNorms.aut K L (AlgEquiv.restrictNormalHom L σ) = 1 ↔
    AlgEquiv.restrictNormalHom L σ = 1
  constructor
  · intro h
    apply FieldOfNorms.aut_injective K L
    simpa only [_root_.map_one] using h
  · intro h
    rw [h, _root_.map_one]

/-- Extension of normal-field automorphisms to the same separable
closure shows that restricting the absolute action does not change its image. -/
theorem FieldOfNorms.absoluteAut_range :
    (FieldOfNorms.absoluteAut K L).range =
      (FieldOfNorms.aut K L).range := by
  ext e
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨AlgEquiv.restrictNormalHom L σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := L) (Ω) τ
    exact ⟨σ, congrArg (FieldOfNorms.aut K L) hσ⟩

end FontaineWintenberger
