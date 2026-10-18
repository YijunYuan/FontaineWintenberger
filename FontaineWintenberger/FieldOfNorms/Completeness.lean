/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Truncation
public import FontaineWintenberger.FieldOfNorms.Uniformizer
public import FontaineWintenberger.FieldOfNorms.ValuationCompleteness

/-!
# Completeness in the original norm-limit valuation uniformity

The exact original valuation kernels identify the inherited integral-ring uniformity
with the canonical complete discrete-product inverse limit.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Valued

variable (F : Type*) [Field F] [hv : Valued F (WithZero (Multiplicative ℤ))]

/-- A value-one element gives the integer closed-ball basis for the original
canonical valuation topology; the radii are represented in its actual value group. -/
theorem nhds_zero_hasBasis_integer_closedBall (π : F)
    (hπ : hv.v π = WithZero.exp (-1 : ℤ)) :
    (nhds (0 : F)).HasBasis (fun _ : ℕ => True)
      (fun n => {x : F | hv.v x ≤ WithZero.exp (-((n + 2 : ℕ) : ℤ))}) := by
  rw [Filter.hasBasis_iff]
  intro S
  constructor
  · intro hS
    obtain ⟨γ, _, hγ⟩ := (hasBasis_nhds_zero F (WithZero (Multiplicative ℤ))).mem_iff.mp hS
    let r := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
    have hr : r ≠ 0 := (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr
      (Units.ne_zero γ)
    let k := WithZero.log r
    let n := (-k).toNat
    refine ⟨n, trivial, fun x hx => hγ ?_⟩
    apply (Valuation.restrict_lt_iff_lt_embedding (v := hv.v)).mpr
    apply hx.trans_lt
    change WithZero.exp (-((n + 2 : ℕ) : ℤ)) < r
    rw [← WithZero.exp_log hr, WithZero.exp_lt_exp]
    have hn := Int.self_le_toNat (-k)
    dsimp [n, k] at *
    omega
  · rintro ⟨n, _, hn⟩
    let y := π ^ (n + 2)
    have hy : hv.v y = WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
      simp only [y, map_pow, hπ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hyr : hv.v.restrict y ≠ 0 := by
      intro hz
      have hzv := (Valuation.restrict_eq_zero_iff (v := hv.v) (x := y)).mp hz
      rw [hy] at hzv
      exact WithZero.exp_ne_zero hzv
    have ho := isOpen_closedBall F hyr
    have heq : {x : F | hv.v.restrict x ≤ hv.v.restrict y} =
        {x : F | hv.v x ≤ WithZero.exp (-((n + 2 : ℕ) : ℤ))} := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Valuation.restrict_le_iff (v := hv.v), hy]
    rw [heq] at ho
    apply mem_of_superset (ho.mem_nhds (by simp)) hn

end Valued

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteLayer K L)

local notation "𝔅" => deepFiniteTowerQuotient K L D
local notation "𝒜" => deepNormInverseLimit K L D

/-- The inherited topology on the original valuation ring has exactly
the integer closed-ball basis of the existing stable valuation. -/
theorem normLimitIntegral_nhds_zero_hasBasis :
    (nhds (0 : Valuation.valuationSubring (normLimitFieldValuation K L))).HasBasis
      (fun _ : ℕ => True)
      (fun n => {α | normLimitValuation K L α.val ≤
        WithZero.exp (-((n + 2 : ℕ) : ℤ))}) := by
  have h := Valued.nhds_zero_hasBasis_integer_closedBall (NormLimit K L)
    (normLimitUniformizer K L)
    (normLimitValuation_normLimitUniformizer K L)
  rw [nhds_subtype]
  exact h.comap Subtype.val

/-- The actual truncation isomorphism pulls back precisely the original
valuation-ring neighborhoods, with the canonical discrete-product uniformity. -/
theorem normLimitTruncationHom_comap_nhds_zero :
    letI : ∀ n, UniformSpace (𝔅 n) := fun _ => ⊥
    letI : ∀ n, DiscreteUniformity (𝔅 n) := fun _ => inferInstance
    Filter.comap (normLimitTruncationHom K L D) (nhds (0 : 𝒜)) =
      nhds (0 : Valuation.valuationSubring (normLimitFieldValuation K L)) := by
  let : ∀ n, UniformSpace (𝔅 n) := fun _ => ⊥
  let : ∀ n, DiscreteUniformity (𝔅 n) := fun _ => inferInstance
  let q := fun n => deepFiniteTowerTransition K L D
    n (n + 1) (Nat.le_succ n)
  let f := normLimitTruncationHom K L D
  have h := (SequentialInverseLimit.nhds_zero_hasBasis_ker_projection (fun n => 𝔅 n) q).comap f
  have heq (n : ℕ) :
      f ⁻¹' (RingHom.ker (SequentialInverseLimit.projection (fun n => 𝔅 n) q n) : Set 𝒜) =
      {α | normLimitValuation K L α.val ≤ WithZero.exp (-((n + 2 : ℕ) : ℤ))} := by
    ext α
    exact normLimitTruncation_eq_zero_iff K L D n α
  simp only [heq] at h
  exact h.eq_of_same_basis (normLimitIntegral_nhds_zero_hasBasis K L)

/-- The exact original truncation map induces the original valuation-ring
uniformity from the same canonical discrete-product inverse limit. -/
theorem normLimitTruncationHom_isUniformInducing :
    letI : ∀ n, UniformSpace (𝔅 n) := fun _ => ⊥
    letI : ∀ n, DiscreteUniformity (𝔅 n) := fun _ => inferInstance
    IsUniformInducing (normLimitTruncationHom K L D) := by
  let : ∀ n, UniformSpace (𝔅 n) := fun _ => ⊥
  let : ∀ n, DiscreteUniformity (𝔅 n) := fun _ => inferInstance
  let O := Valuation.valuationSubring (normLimitFieldValuation K L)
  let : IsUniformAddGroup O := IsUniformAddGroup.comap O.subtype.toAddMonoidHom
  let : IsUniformAddGroup 𝒜 := IsUniformAddGroup.comap (𝒜).subtype.toAddMonoidHom
  let f := normLimitTruncationHom K L D
  rw [isUniformInducing_iff, uniformity_eq_comap_nhds_zero O,
    uniformity_eq_comap_nhds_zero 𝒜, Filter.comap_comap]
  have heq : (fun z : 𝒜 × 𝒜 => z.2 - z.1) ∘ Prod.map f f =
      f ∘ (fun z : O × O => z.2 - z.1) := by
    funext z
    exact (map_sub f z.2 z.1).symm
  change Filter.comap ((fun z : 𝒜 × 𝒜 => z.2 - z.1) ∘ Prod.map f f) (nhds (0 : 𝒜)) =
    Filter.comap (fun z : O × O => z.2 - z.1) (nhds (0 : O))
  rw [heq, ← Filter.comap_comap, normLimitTruncationHom_comap_nhds_zero]

include D in
/-- The inherited original valuation ring is complete; its uniformity
is identified with the actual complete truncated inverse limit. -/
theorem normLimitIntegral_completeSpace :
    CompleteSpace (Valuation.valuationSubring (normLimitFieldValuation K L)) := by
  let : ∀ n, UniformSpace (𝔅 n) := fun _ => ⊥
  let : ∀ n, DiscreteUniformity (𝔅 n) := fun _ => inferInstance
  let : CompleteSpace 𝒜 := SequentialInverseLimit.completeSpace (fun n => 𝔅 n)
    (fun n => deepFiniteTowerTransition K L D n (n + 1) (Nat.le_succ n))
  have h := normLimitTruncationHom_isUniformInducing K L D
  exact (h.completeSpace_congr (normLimitTruncationEquiv K L D).surjective).mpr
    inferInstance

/-- The original norm-limit field is complete for precisely the already
constructed canonical stable-valuation uniformity. -/
instance normLimit_completeSpace :
    CompleteSpace (NormLimit K L) := by
  let := normLimitIntegral_completeSpace K L (FiniteLayer.bottom (K := K) (L := L))
  exact Valued.completeSpace_of_completeSpace_valuationSubring (NormLimit K L)

/-- The same original field has a Hausdorff valuation uniformity. -/
theorem normLimit_t2Space :
    T2Space (NormLimit K L) := by
  infer_instance

/-- Its original valuation ring carries the inherited Hausdorff topology. -/
theorem normLimitIntegral_t2Space :
    T2Space (Valuation.valuationSubring (normLimitFieldValuation K L)) := by
  infer_instance

end FontaineWintenberger
