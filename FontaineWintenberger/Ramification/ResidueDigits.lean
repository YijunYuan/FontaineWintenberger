module

public import FontaineWintenberger.Ramification.Valuation
public import Mathlib.FieldTheory.Perfect

/-!
# Finite perfect-residue digits

Iterated Frobenius in the actual perfect residue field and ordinary
uniformizer division give finite power-digit expansions. No infinite
choice of representatives, residue finiteness, or completeness is used.
-/

@[expose] public section

namespace FontaineWintenberger

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    [PerfectField (IsLocalRing.ResidueField R)]

/-- A residue Frobenius root lifts to one actual uniformizer digit. -/
theorem exists_pow_digit_uniformizer {π : R} (hπ : Irreducible π) (n : ℕ) (a : R) :
    ∃ b c : R, a = b ^ (p ^ n) + π * c := by
  obtain ⟨x, hx⟩ := (iterateFrobeniusEquiv (IsLocalRing.ResidueField R) p n).surjective
    (IsLocalRing.residue R a)
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  have hb : IsLocalRing.residue R (b ^ (p ^ n)) = IsLocalRing.residue R a := by
    simpa only [map_pow, iterateFrobeniusEquiv_def] using hx
  have hm : a - b ^ (p ^ n) ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue R (a - b ^ (p ^ n)) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨c, hc⟩ : π ∣ a - b ^ (p ^ n) := by
    simpa only [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] using hm
  exact ⟨b, c, by linear_combination hc⟩

/-- Every finite precision has an actual finite power-digit expansion with
an explicit uniformizer-power remainder. -/
theorem exists_pow_digits_uniformizer {π : R} (hπ : Irreducible π) (n r : ℕ) (a : R) :
    ∃ b : ℕ → R, ∃ c : R,
      a = (∑ j ∈ Finset.range r, b j ^ (p ^ n) * π ^ j) + π ^ r * c := by
  induction r generalizing a with
  | zero => exact ⟨fun _ => 0, a, by simp⟩
  | succ r ih =>
    obtain ⟨b₀, a₁, ha⟩ := exists_pow_digit_uniformizer p hπ n a
    obtain ⟨b, c, hc⟩ := ih a₁
    let d : ℕ → R := Nat.rec b₀ (fun j _ => b j)
    refine ⟨d, c, ?_⟩
    have hsum : (∑ j ∈ Finset.range (r + 1), d j ^ (p ^ n) * π ^ j) =
        b₀ ^ (p ^ n) + π * ∑ j ∈ Finset.range r, b j ^ (p ^ n) * π ^ j := by
      rw [Finset.sum_range_succ']
      simp only [d, Nat.rec_zero, pow_zero, mul_one]
      rw [Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [hsum, ha, hc, pow_succ]
    ring

/-- The finite power-digit sum approximates the actual input to the stated
maximal-ideal power, over an arbitrary perfect residue field. -/
theorem exists_pow_digits_sub_mem_maximalIdeal_pow {π : R} (hπ : Irreducible π)
    (n r : ℕ) (a : R) : ∃ b : ℕ → R,
    a - (∑ j ∈ Finset.range r, b j ^ (p ^ n) * π ^ j) ∈
      IsLocalRing.maximalIdeal R ^ r := by
  obtain ⟨b, c, hc⟩ := exists_pow_digits_uniformizer p hπ n r a
  refine ⟨b, ?_⟩
  rw [hc, add_sub_cancel_left, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, rfl⟩

end FontaineWintenberger
