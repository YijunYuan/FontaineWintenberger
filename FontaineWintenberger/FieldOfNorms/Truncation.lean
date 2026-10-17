/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Reconstruction
public import FontaineWintenberger.FieldOfNorms.Valued

/-!
# The actual integral norm limit and its truncated coordinates

The original valuation ring is identified with the actual deep truncated inverse limit.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter
open scoped Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) (D : FiniteLayer K L)

local notation "𝔈" => deepFiniteTower K L p hL hInfinite D
local notation "𝔅" => deepFiniteTowerQuotient K L p hL hInfinite D
local notation "𝒜" => deepNormInverseLimit K L p hL hInfinite D

/-- The actual sum is additive at each selected deep stage's own precision. -/
theorem normLimitAdd_deep_sub_mem (α β : NormLimit K L)
    (hα : normLimitValuation K L hL α ≤ 1)
    (hβ : normLimitValuation K L hL β ≤ 1) (n : ℕ) :
    normLimitEval K L (𝔈 n) (normLimitAdd K L p hL α β) -
      normLimitEval K L (𝔈 n) α - normLimitEval K L (𝔈 n) β ∈
      (fun z : spectralIntegerRing K (𝔈 n).val => (z : (𝔈 n).val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) :
          Ideal (spectralIntegerRing K (𝔈 n).val)) : Set (spectralIntegerRing K (𝔈 n).val)) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 n).val
  apply (FiniteLayer.isClosed_image_maximalIdeal_pow (𝔈 n) (n + 2)).mem_of_tendsto
    (((tendsto_normSumNet_normLimitAdd K L p hL α β (𝔈 n)).sub_const
      (normLimitEval K L (𝔈 n) α)).sub_const (normLimitEval K L (𝔈 n) β))
  filter_upwards [] with F
  have hEF : 𝔈 n ≤ F.val := F.property
  let x : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val α, normLimitEval_mem_of_valuation_le_one K L hL α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val β, normLimitEval_mem_of_valuation_le_one K L hL β hβ F.val⟩
  refine ⟨FiniteLayer.integerNorm (𝔈 n) F.val hEF (x + y) -
    FiniteLayer.integerNorm (𝔈 n) F.val hEF x -
      FiniteLayer.integerNorm (𝔈 n) F.val hEF y,
    deepFiniteTower_integerNorm_add_congruence K L p hL hInfinite D n F.val hEF x y, ?_⟩
  push_cast
  simp only [FiniteLayer.coe_integerNorm]
  change FiniteLayer.norm (𝔈 n) F.val hEF
      (normLimitEval K L F.val α + normLimitEval K L F.val β) -
    FiniteLayer.norm (𝔈 n) F.val hEF (normLimitEval K L F.val α) -
      FiniteLayer.norm (𝔈 n) F.val hEF (normLimitEval K L F.val β) = _
  rw [normLimitEval_norm, normLimitEval_norm]
  rfl

/-- Integral evaluation uses each original finite layer's original integer ring. -/
def normLimitIntegralCoordinate :
    letI := normLimitField K L p hL hInfinite
    Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite) →
      (n : ℕ) → spectralIntegerRing K (𝔈 n).val := by
  letI := normLimitField K L p hL hInfinite
  intro α n
  exact ⟨normLimitEval K L (𝔈 n) α.val,
    normLimitEval_mem_of_valuation_le_one K L hL α.val α.property (𝔈 n)⟩

/-- The actual original integral family has a ring-valued coordinate
at the deep stage's specified precision. -/
def normLimitTruncation (n : ℕ) :
    letI := normLimitField K L p hL hInfinite
    Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite) →+* 𝔅 n := by
  letI := normLimitField K L p hL hInfinite
  let c := normLimitIntegralCoordinate K L p hL hInfinite D
  let q := Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2))
  exact {
    toFun := fun α => q (c α n)
    map_one' := by
      have h : c 1 n = 1 := Subtype.ext (map_one (normLimitEval K L (𝔈 n)))
      rw [h, map_one]
    map_zero' := by
      have h : c 0 n = 0 := Subtype.ext (map_zero (normLimitEval K L (𝔈 n)))
      rw [h, map_zero]
    map_mul' := fun α β => by
      rw [← map_mul]
      apply congrArg q
      exact Subtype.ext (map_mul (normLimitEval K L (𝔈 n)) α.val β.val)
    map_add' := fun α β => by
      rw [← map_add]
      apply Ideal.Quotient.eq.mpr
      obtain ⟨d, hd, he⟩ := normLimitAdd_deep_sub_mem K L p hL hInfinite D
        α.val β.val α.property β.property n
      have heq : c (α + β) n - c α n - c β n = d := Subtype.ext he.symm
      rw [sub_add_eq_sub_sub, heq]
      exact hd }

/-- The ring coordinate is exactly the original finite-field quotient class. -/
@[simp]
theorem normLimitTruncation_apply (n : ℕ) :
    letI := normLimitField K L p hL hInfinite
    ∀ α : Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite),
    normLimitTruncation K L p hL hInfinite D n α =
      Ideal.Quotient.mk _ (normLimitIntegralCoordinate K L p hL hInfinite D α n) := by
  let := normLimitField K L p hL hInfinite
  intro α
  rfl

/-- The quotient coordinates obey the actual original norm transitions. -/
theorem normLimitTruncation_compatible (n m : ℕ) (hnm : n ≤ m) :
    letI := normLimitField K L p hL hInfinite
    ∀ α : Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite),
    deepFiniteTowerTransition K L p hL hInfinite D n m hnm
      (normLimitTruncation K L p hL hInfinite D m α) =
        normLimitTruncation K L p hL hInfinite D n α := by
  let := normLimitField K L p hL hInfinite
  intro α
  rw [normLimitTruncation_apply, deepFiniteTowerTransition_mk, normLimitTruncation_apply]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  rw [FiniteLayer.coe_integerNorm]
  exact normLimitEval_norm K L (𝔈 n) (𝔈 m)
    (deepFiniteTower_monotone K L p hL hInfinite D hnm) α.val

/-- Actual quotient coordinates define the ring map on the original
valuation ring into the actual compatible truncated-family subring. -/
def normLimitTruncationHom :
    letI := normLimitField K L p hL hInfinite
    Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite) →+* 𝒜 := by
  letI := normLimitField K L p hL hInfinite
  exact {
    toFun := fun α => ⟨fun n => normLimitTruncation K L p hL hInfinite D n α,
      (SequentialInverseLimit.mem_subring _ _ _).mpr
        (fun n => normLimitTruncation_compatible K L p hL hInfinite D
          n (n + 1) (Nat.le_succ n) α)⟩
    map_zero' := Subtype.ext (funext fun n => map_zero
      (normLimitTruncation K L p hL hInfinite D n))
    map_one' := Subtype.ext (funext fun n => map_one
      (normLimitTruncation K L p hL hInfinite D n))
    map_add' := fun α β => Subtype.ext (funext fun n => map_add
      (normLimitTruncation K L p hL hInfinite D n) α β)
    map_mul' := fun α β => Subtype.ext (funext fun n => map_mul
      (normLimitTruncation K L p hL hInfinite D n) α β) }

/-- The actual original reconstruction, with its proved integrality,
is an element of the original canonical valuation ring. -/
def deepIntegralReconstruction :
    letI := normLimitField K L p hL hInfinite
    𝒜 → Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite) := by
  letI := normLimitField K L p hL hInfinite
  exact fun a => ⟨deepNormReconstruction K L p hL hInfinite D a,
    deepNormReconstruction_valuation_le_one K L p hL hInfinite D a⟩

/-- Truncating the actual reconstructed original family retains all
the originally prescribed quotient coordinates. -/
theorem normLimitTruncationHom_deepIntegralReconstruction (a : 𝒜) :
    normLimitTruncationHom K L p hL hInfinite D
      (deepIntegralReconstruction K L p hL hInfinite D a) = a := by
  let := normLimitField K L p hL hInfinite
  apply Subtype.ext
  funext n
  change Ideal.Quotient.mk _
    (normLimitIntegralCoordinate K L p hL hInfinite D
      (deepIntegralReconstruction K L p hL hInfinite D a) n) = a.val n
  rw [← deepNormRepresentative_mk K L p hL hInfinite D a n]
  apply Ideal.Quotient.eq.mpr
  obtain ⟨d, hd, he⟩ := deepNormReconstruction_sub_mem K L p hL hInfinite D a n
  have heq : normLimitIntegralCoordinate K L p hL hInfinite D
      (deepIntegralReconstruction K L p hL hInfinite D a) n -
      deepNormRepresentative K L p hL hInfinite D a n = d :=
    Subtype.ext he.symm
  rw [heq]
  exact hd

/-- Reconstructing the actual quotient coordinates returns the same original
integral family, rather than a new model of its field. -/
theorem deepIntegralReconstruction_normLimitTruncationHom :
    letI := normLimitField K L p hL hInfinite
    ∀ α : Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite),
    deepIntegralReconstruction K L p hL hInfinite D
      (normLimitTruncationHom K L p hL hInfinite D α) = α := by
  let := normLimitField K L p hL hInfinite
  intro α
  apply Subtype.ext
  apply NormLimit.ext
  intro F
  obtain ⟨j, hFj⟩ := deepFiniteTower_cofinal K L p hL hInfinite D F
  have hj : normLimitEval K L (𝔈 j)
      (deepIntegralReconstruction K L p hL hInfinite D
        (normLimitTruncationHom K L p hL hInfinite D α)).val =
      normLimitEval K L (𝔈 j) α.val := by
    let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    let x := normLimitIntegralCoordinate K L p hL hInfinite D α
    have hx : ∀ n, Ideal.Quotient.mk _ (x n) =
        (normLimitTruncationHom K L p hL hInfinite D α).val n := fun _ => rfl
    have ht := deepNormReconstruction_tendsto K L p hL hInfinite D
      (normLimitTruncationHom K L p hL hInfinite D α) x hx j
    have hc : deepNormSequence K L p hL hInfinite D x j =
        fun _ => normLimitEval K L (𝔈 j) α.val := by
      funext n
      by_cases hjn : j ≤ n
      · rw [deepNormSequence_of_le K L p hL hInfinite D x j n hjn]
        exact normLimitEval_norm K L (𝔈 j) (𝔈 n)
          (deepFiniteTower_monotone K L p hL hInfinite D hjn) α.val
      · rw [deepNormSequence, dite_eq_right hjn]
        rfl
    exact tendsto_nhds_unique ht (by rw [hc]; exact tendsto_const_nhds)
  rw [← normLimitEval_norm K L F (𝔈 j) hFj
    (deepIntegralReconstruction K L p hL hInfinite D
      (normLimitTruncationHom K L p hL hInfinite D α)).val,
    ← normLimitEval_norm K L F (𝔈 j) hFj α.val, hj]

/-- The actual integral norm limit is the actual complete truncated
inverse-limit ring, with the original norm reconstruction as inverse. -/
def normLimitTruncationEquiv :
    letI := normLimitField K L p hL hInfinite
    Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite) ≃+* 𝒜 := by
  letI := normLimitField K L p hL hInfinite
  exact { normLimitTruncationHom K L p hL hInfinite D with
    invFun := deepIntegralReconstruction K L p hL hInfinite D
    left_inv := deepIntegralReconstruction_normLimitTruncationHom K L p hL hInfinite D
    right_inv := normLimitTruncationHom_deepIntegralReconstruction K L p hL hInfinite D }

/-- The exact quotient kernel is the same original valuation ball. -/
theorem normLimitTruncation_eq_zero_iff (n : ℕ) :
    letI := normLimitField K L p hL hInfinite
    ∀ α : Valuation.valuationSubring (normLimitFieldValuation K L p hL hInfinite),
    normLimitTruncation K L p hL hInfinite D n α = 0 ↔
      normLimitValuation K L hL α.val ≤ WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
  let := normLimitField K L p hL hInfinite
  intro α
  rw [normLimitTruncation_apply, Ideal.Quotient.eq_zero_iff_mem,
    ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation]
  rw [normLimitValuation_eq_deepFiniteTower K L p hL hInfinite D n]
  rfl

end FontaineWintenberger
