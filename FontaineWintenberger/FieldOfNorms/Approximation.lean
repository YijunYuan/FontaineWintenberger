module

public import FontaineWintenberger.FieldOfNorms.Operations

/-!
# Asymptotic coordinate approximation of the original norm-limit addition

The existing normalized valuations control multiplicative scaling of integral
coordinate errors on the original fields.
-/

@[expose] public section

noncomputable section

namespace ValuationSubring

variable {E : Type*} [Field E] (A : ValuationSubring E) [IsDiscreteValuationRing A]

/-- An ambient-field ideal-power bound is exactly the bound for the existing
canonical normalized valuation, including its integrality consequence. -/
theorem mem_image_maximalIdeal_pow_iff_normalizedValuation (x : E) (n : ℕ) :
    x ∈ (fun a : A => (a : E)) ''
        ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation E x ≤ WithZero.exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_maximalIdeal_pow_iff_normalizedValuation A a n).mp ha
  · intro hx
    have hbound : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hmem : x ∈ A := by
      rw [← normalizedValuation_valuationSubring A]
      exact hx.trans hbound
    exact ⟨⟨x, hmem⟩,
      (mem_maximalIdeal_pow_iff_normalizedValuation A ⟨x, hmem⟩ n).mpr hx, rfl⟩

end ValuationSubring

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The actual sum of arbitrary original norm families agrees with coordinate
addition to every eventual ideal-power precision. -/
theorem normLimitAdd_sub_mem (hL : IsAPF K L) (α β : NormLimit K L) :
    ∀ n : ℕ, ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      normLimitEval K L E (normLimitAdd K L p hL α β) -
        normLimitEval K L E α - normLimitEval K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  let w := normLimitValuation K L hL
  let S : Finset (NormLimit K L) := {1, α, β}
  obtain ⟨δ, _, hmax⟩ := Finset.exists_max_image S w ⟨1, by simp [S]⟩
  have hone : 1 ≤ w δ := by simpa only [map_one] using hmax 1 (by simp [S])
  have hδpos : 0 < w δ := zero_lt_one.trans_le hone
  have hδ : δ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hone
    exact not_le_of_gt zero_lt_one hone
  have ha : w (α / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax α (by simp [S]))
  have hb : w (β / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax β (by simp [S]))
  have hδα : δ * (α / δ) = α := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  let q := (WithZero.log (w δ)).toNat
  have hδbound : w δ ≤ WithZero.exp (q : ℤ) :=
    WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat _))
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L hL
  intro n
  obtain ⟨T₁, hT₁⟩ := normLimitAdd_sub_mem_of_valuation_le_one
    K L p hL (α / δ) (β / δ) ha hb (n + q)
  refine ⟨FiniteLayer.sup T₀ T₁, fun E hE => ?_⟩
  have hE₀ := (FiniteLayer.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteLayer.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hvδ : v (normLimitEval K L E δ) ≤ WithZero.exp (q : ℤ) := by
    change normLimitCoordinateValuation K L E δ ≤ _
    rw [← hT₀ E hE₀ δ]
    exact hδbound
  have hvε : v (normLimitEval K L E (normLimitAdd K L p hL (α / δ) (β / δ)) -
      normLimitEval K L E (α / δ) - normLimitEval K L E (β / δ)) ≤
        WithZero.exp (-((n + q : ℕ) : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ (n + q)).mp (hT₁ E hE₁)
  apply (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) _ n).mpr
  have hs := congrArg (normLimitEval K L E)
    (mul_normLimitAdd K L p hL δ (α / δ) (β / δ))
  rw [map_mul, hδα, hδβ] at hs
  have hαE : normLimitEval K L E δ * normLimitEval K L E (α / δ) =
      normLimitEval K L E α := by rw [← map_mul, hδα]
  have hβE : normLimitEval K L E δ * normLimitEval K L E (β / δ) =
      normLimitEval K L E β := by rw [← map_mul, hδβ]
  have heq : normLimitEval K L E (normLimitAdd K L p hL α β) -
      normLimitEval K L E α - normLimitEval K L E β =
      normLimitEval K L E δ *
        (normLimitEval K L E (normLimitAdd K L p hL (α / δ) (β / δ)) -
          normLimitEval K L E (α / δ) - normLimitEval K L E (β / δ)) := by
    rw [← hs, ← hαE, ← hβE]
    ring
  change v _ ≤ _
  rw [heq, map_mul]
  calc
    _ ≤ WithZero.exp (q : ℤ) * WithZero.exp (-((n + q : ℕ) : ℤ)) :=
      mul_le_mul' hvδ hvε
    _ = WithZero.exp (-(n : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega

end FontaineWintenberger
