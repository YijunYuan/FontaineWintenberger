/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Valued

/-!
# Valuations of differences from original finite coordinates

Actual subtraction has arbitrarily precise finite-coordinate approximations.
Consequently cofinally many exact finite displacement valuations determine
the valuation on the same original norm-field carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Actual norm-field subtraction agrees with ordinary coordinate subtraction
to every ideal-power precision on an original finite tail. -/
theorem normLimitEval_sub_sub_mem [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∀ (α β : NormLimit K L) (n : ℕ),
      ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
        normLimitEval K L E (α - β) - normLimitEval K L E α +
          normLimitEval K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  intro α β n
  obtain ⟨T, hT⟩ := normLimitAdd_sub_mem K L (α - β) β n
  have hs : normLimitAdd K L (α - β) β = α := sub_add_cancel α β
  refine ⟨T, fun E hE => ?_⟩
  obtain ⟨z, hz, heq⟩ := hT E hE
  rw [hs] at heq
  refine ⟨-z, neg_mem hz, ?_⟩
  change -(z : E.val) = _
  linear_combination -heq

/-- Cofinal exact valuations of actual finite-coordinate differences compute
the same original norm-field valuation, for every signed displacement order. -/
theorem normLimitValuation_sub_eq_of_cofinal_coordinate [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∀ (α β : NormLimit K L) (n : ℤ),
      (∀ T : FiniteLayer K L, ∃ E : FiniteLayer K L, T ≤ E ∧
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          (normLimitEval K L E α - normLimitEval K L E β) = WithZero.exp (-n)) →
      normLimitValuation K L (α - β) = WithZero.exp (-n) := by
  intro α β n hcofinal
  let s : ℕ := n.toNat + 1
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L
  obtain ⟨T₁, hT₁⟩ := normLimitEval_sub_sub_mem K L α β s
  obtain ⟨E, hE, hval⟩ := hcofinal (FiniteLayer.sup T₀ T₁)
  have hE₀ := (FiniteLayer.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteLayer.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hbound : v (normLimitEval K L E (α - β) - normLimitEval K L E α +
      normLimitEval K L E β) ≤ WithZero.exp (-(s : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ s).mp (hT₁ E hE₁)
  have hlt : WithZero.exp (-(s : ℤ)) < WithZero.exp (-n) := by
    apply WithZero.exp_lt_exp.mpr
    dsimp [s]
    omega
  have hclose : v (normLimitEval K L E (α - β) -
      (normLimitEval K L E α - normLimitEval K L E β)) <
        v (normLimitEval K L E α - normLimitEval K L E β) := by
    rw [hval]
    have heq : normLimitEval K L E (α - β) -
        (normLimitEval K L E α - normLimitEval K L E β) =
        normLimitEval K L E (α - β) - normLimitEval K L E α +
          normLimitEval K L E β := by ring
    rw [heq]
    exact hbound.trans_lt hlt
  rw [hT₀ E hE₀]
  change v (normLimitEval K L E (α - β)) = _
  exact (v.map_eq_of_sub_lt hclose).trans hval

end FontaineWintenberger
