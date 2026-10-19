/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Reconstruction
public import FontaineWintenberger.FieldOfNorms.Basic.Ring

/-!
# The integral field of norms and its truncated coordinates

The valuation ring is identified with the deep truncated inverse limit.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter
open scoped Topology

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteIntermediateField K L)

local notation "𝔈" => deepFiniteTower K L D
local notation "𝔅" => deepFiniteTowerQuotient K L D
local notation "𝒜" => deepNormInverseLimit K L D

/-- The sum is additive at each selected deep stage's own precision. -/
theorem FieldOfNorms.add_deep_sub_mem (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1) (n : ℕ) :
    FieldOfNorms.coord K L (𝔈 n) (FieldOfNorms.add K L α β) -
      FieldOfNorms.coord K L (𝔈 n) α - FieldOfNorms.coord K L (𝔈 n) β ∈
      (fun z : spectralIntegerRing K (𝔈 n).val => (z : (𝔈 n).val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) :
          Ideal (spectralIntegerRing K (𝔈 n).val)) : Set (spectralIntegerRing K (𝔈 n).val)) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 n).val
  apply (FiniteIntermediateField.isClosed_image_maximalIdeal_pow (𝔈 n) (n + 2)).mem_of_tendsto
    (((FieldOfNorms.tendsto_normSumNet_add K L α β (𝔈 n)).sub_const
      (FieldOfNorms.coord K L (𝔈 n) α)).sub_const (FieldOfNorms.coord K L (𝔈 n) β))
  filter_upwards [] with F
  have hEF : 𝔈 n ≤ F.val := F.property
  let x : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F.val⟩
  refine ⟨FiniteIntermediateField.integerNorm (𝔈 n) F.val hEF (x + y) -
    FiniteIntermediateField.integerNorm (𝔈 n) F.val hEF x -
      FiniteIntermediateField.integerNorm (𝔈 n) F.val hEF y,
    deepFiniteTower_integerNorm_add_congruence K L D n F.val hEF x y, ?_⟩
  push_cast
  simp only [FiniteIntermediateField.coe_integerNorm]
  change FiniteIntermediateField.norm (𝔈 n) F.val hEF
      (FieldOfNorms.coord K L F.val α + FieldOfNorms.coord K L F.val β) -
    FiniteIntermediateField.norm (𝔈 n) F.val hEF (FieldOfNorms.coord K L F.val α) -
      FiniteIntermediateField.norm (𝔈 n) F.val hEF (FieldOfNorms.coord K L F.val β) = _
  rw [FieldOfNorms.coord_norm, FieldOfNorms.coord_norm]
  rfl

/-- Integral evaluation uses each finite intermediate field's integer ring. -/
def FieldOfNorms.integralCoordinate :
    Valuation.valuationSubring (FieldOfNorms.fieldValuation K L) →
      (n : ℕ) → spectralIntegerRing K (𝔈 n).val := by
  intro α n
  exact ⟨FieldOfNorms.coord K L (𝔈 n) α.val,
    FieldOfNorms.coord_mem_of_valuation_le_one K L α.val α.property (𝔈 n)⟩

/-- The integral family has a ring-valued coordinate
at the deep stage's specified precision. -/
def FieldOfNorms.truncation (n : ℕ) :
    Valuation.valuationSubring (FieldOfNorms.fieldValuation K L) →+* 𝔅 n := by
  let c := FieldOfNorms.integralCoordinate K L D
  let q := Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2))
  exact {
    toFun := fun α => q (c α n)
    map_one' := by
      have h : c 1 n = 1 := Subtype.ext (_root_.map_one (FieldOfNorms.coord K L (𝔈 n)))
      rw [h, _root_.map_one]
    map_zero' := by
      have h : c 0 n = 0 := Subtype.ext (_root_.map_zero (FieldOfNorms.coord K L (𝔈 n)))
      rw [h, _root_.map_zero]
    map_mul' := fun α β => by
      rw [← _root_.map_mul]
      apply congrArg q
      exact Subtype.ext (_root_.map_mul (FieldOfNorms.coord K L (𝔈 n)) α.val β.val)
    map_add' := fun α β => by
      rw [← _root_.map_add]
      apply Ideal.Quotient.eq.mpr
      obtain ⟨d, hd, he⟩ := FieldOfNorms.add_deep_sub_mem K L D
        α.val β.val α.property β.property n
      have heq : c (α + β) n - c α n - c β n = d := Subtype.ext he.symm
      rw [sub_add_eq_sub_sub, heq]
      exact hd }

/-- The ring coordinate is exactly the finite-field quotient class. -/
@[simp]
theorem FieldOfNorms.truncation_apply (n : ℕ) :
    ∀ α : Valuation.valuationSubring (FieldOfNorms.fieldValuation K L),
    FieldOfNorms.truncation K L D n α =
      Ideal.Quotient.mk _ (FieldOfNorms.integralCoordinate K L D α n) := by
  intro α
  rfl

/-- The quotient coordinates obey the norm transitions. -/
theorem FieldOfNorms.truncation_compatible (n m : ℕ) (hnm : n ≤ m) :
    ∀ α : Valuation.valuationSubring (FieldOfNorms.fieldValuation K L),
    deepFiniteTowerTransition K L D n m hnm
      (FieldOfNorms.truncation K L D m α) =
        FieldOfNorms.truncation K L D n α := by
  intro α
  rw [FieldOfNorms.truncation_apply, deepFiniteTowerTransition_mk, FieldOfNorms.truncation_apply]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  rw [FiniteIntermediateField.coe_integerNorm]
  exact FieldOfNorms.coord_norm K L (𝔈 n) (𝔈 m)
    (deepFiniteTower_monotone K L D hnm) α.val

/-- Quotient coordinates define the ring map on the
valuation ring into the compatible truncated-family subring. -/
def FieldOfNorms.truncationHom :
    Valuation.valuationSubring (FieldOfNorms.fieldValuation K L) →+* 𝒜 := by
  exact {
    toFun := fun α => ⟨fun n => FieldOfNorms.truncation K L D n α,
      (SequentialInverseLimit.mem_subring _ _ _).mpr
        (fun n => FieldOfNorms.truncation_compatible K L D
          n (n + 1) (Nat.le_succ n) α)⟩
    map_zero' := Subtype.ext (funext fun n => _root_.map_zero
      (FieldOfNorms.truncation K L D n))
    map_one' := Subtype.ext (funext fun n => _root_.map_one
      (FieldOfNorms.truncation K L D n))
    map_add' := fun α β => Subtype.ext (funext fun n => _root_.map_add
      (FieldOfNorms.truncation K L D n) α β)
    map_mul' := fun α β => Subtype.ext (funext fun n => _root_.map_mul
      (FieldOfNorms.truncation K L D n) α β) }

/-- The reconstruction, with its proved integrality,
is an element of the canonical valuation ring. -/
def deepIntegralReconstruction :
    𝒜 → Valuation.valuationSubring (FieldOfNorms.fieldValuation K L) := by
  exact fun a => ⟨deepNormReconstruction K L D a,
    deepNormReconstruction_valuation_le_one K L D a⟩

/-- Truncating the reconstructed family retains all
the originally prescribed quotient coordinates. -/
theorem FieldOfNorms.truncationHom_deepIntegralReconstruction (a : 𝒜) :
    FieldOfNorms.truncationHom K L D
      (deepIntegralReconstruction K L D a) = a := by
  apply Subtype.ext
  funext n
  change Ideal.Quotient.mk _
    (FieldOfNorms.integralCoordinate K L D
      (deepIntegralReconstruction K L D a) n) = a.val n
  rw [← deepNormRepresentative_mk K L D a n]
  apply Ideal.Quotient.eq.mpr
  obtain ⟨d, hd, he⟩ := deepNormReconstruction_sub_mem K L D a n
  have heq : FieldOfNorms.integralCoordinate K L D
      (deepIntegralReconstruction K L D a) n -
      deepNormRepresentative K L D a n = d :=
    Subtype.ext he.symm
  rw [heq]
  exact hd

/-- Reconstructing the quotient coordinates returns the same
integral family, rather than a new model of its field. -/
theorem deepIntegralReconstruction_truncationHom :
    ∀ α : Valuation.valuationSubring (FieldOfNorms.fieldValuation K L),
    deepIntegralReconstruction K L D
      (FieldOfNorms.truncationHom K L D α) = α := by
  intro α
  apply Subtype.ext
  apply FieldOfNorms.ext
  intro F
  obtain ⟨j, hFj⟩ := deepFiniteTower_cofinal K L D F
  have hj : FieldOfNorms.coord K L (𝔈 j)
      (deepIntegralReconstruction K L D
        (FieldOfNorms.truncationHom K L D α)).val =
      FieldOfNorms.coord K L (𝔈 j) α.val := by
    let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    let x := FieldOfNorms.integralCoordinate K L D α
    have hx : ∀ n, Ideal.Quotient.mk _ (x n) =
        (FieldOfNorms.truncationHom K L D α).val n := fun _ => rfl
    have ht := deepNormReconstruction_tendsto K L D
      (FieldOfNorms.truncationHom K L D α) x hx j
    have hc : deepNormSequence K L D x j =
        fun _ => FieldOfNorms.coord K L (𝔈 j) α.val := by
      funext n
      by_cases hjn : j ≤ n
      · rw [deepNormSequence_of_le K L D x j n hjn]
        exact FieldOfNorms.coord_norm K L (𝔈 j) (𝔈 n)
          (deepFiniteTower_monotone K L D hjn) α.val
      · rw [deepNormSequence, dite_eq_right hjn]
        rfl
    exact tendsto_nhds_unique ht (by rw [hc]; exact tendsto_const_nhds)
  rw [← FieldOfNorms.coord_norm K L F (𝔈 j) hFj
    (deepIntegralReconstruction K L D
      (FieldOfNorms.truncationHom K L D α)).val,
    ← FieldOfNorms.coord_norm K L F (𝔈 j) hFj α.val, hj]

/-- The integral field of norms is the complete truncated
inverse-limit ring, with the norm reconstruction as inverse. -/
def FieldOfNorms.truncationEquiv :
    Valuation.valuationSubring (FieldOfNorms.fieldValuation K L) ≃+* 𝒜 := by
  exact { FieldOfNorms.truncationHom K L D with
    invFun := deepIntegralReconstruction K L D
    left_inv := deepIntegralReconstruction_truncationHom K L D
    right_inv := FieldOfNorms.truncationHom_deepIntegralReconstruction K L D }

/-- The exact quotient kernel is the valuation ball. -/
theorem FieldOfNorms.truncation_eq_zero_iff (n : ℕ) :
    ∀ α : Valuation.valuationSubring (FieldOfNorms.fieldValuation K L),
    FieldOfNorms.truncation K L D n α = 0 ↔
      FieldOfNorms.valuation K L α.val ≤ WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
  intro α
  rw [FieldOfNorms.truncation_apply, Ideal.Quotient.eq_zero_iff_mem,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation]
  rw [FieldOfNorms.valuation_eq_deepFiniteTower K L D n]
  rfl

end FontaineWintenberger
