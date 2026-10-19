/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# The uniformizer criterion over an arbitrary perfect residue field

Perfect-residue Frobenius lifts reduce every element to a prime power plus
an uniformizer multiple. The polynomial Taylor identity then upgrades one
lower congruence depth from the corresponding uniformizer congruence.
-/

@[expose] public section

namespace FontaineWintenberger

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField B)]

include p in
/-- Over a perfect residue field, the next uniformizer congruence raises
the lower depth of the whole ring action. -/
theorem mem_lowerRamificationGroup_succ_of_uniformizer {π : B} (hπ : Irreducible π)
    {n : ℕ} {g : G}
    (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n)
    (hgp : g • π - π ∈ IsLocalRing.maximalIdeal B ^ (n + 2)) :
    g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n + 1 : ℕ) := by
  rw [lowerRamificationGroup_nat, Ideal.mem_inertia] at hg ⊢
  intro x
  obtain ⟨b₀, hb₀⟩ := (PerfectRing.bijective_frobenius
    (R := IsLocalRing.ResidueField B) (p := p)).surjective (IsLocalRing.residue B x)
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b₀
  change IsLocalRing.residue B b ^ p = IsLocalRing.residue B x at hb₀
  have hxb : x - b ^ p ∈ IsLocalRing.maximalIdeal B := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue B (x - b ^ p) = 0
    rw [map_sub, map_pow, hb₀, sub_self]
  obtain ⟨c, hc⟩ : π ∣ x - b ^ p := by
    simpa only [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] using hxb
  have hx : x = b ^ p + π * c := by linear_combination hc
  let φ := MulSemiringAction.toRingHom G B g
  let d := φ b - b
  have hd : d ∈ IsLocalRing.maximalIdeal B ^ (n + 1) := hg b
  have hp : (p : B) ∈ IsLocalRing.maximalIdeal B := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue B (p : B) = 0
    simp
  have hd2 : d ^ 2 ∈ IsLocalRing.maximalIdeal B ^ (n + 2) := by
    have h := Ideal.mul_mem_mul hd hd
    rw [← pow_add] at h
    exact (Ideal.pow_le_pow_right (show n + 2 ≤ n + 1 + (n + 1) by omega))
      (by simpa only [pow_two] using h)
  have hpd : (p : B) * d ∈ IsLocalRing.maximalIdeal B ^ (n + 2) := by
    have h := Ideal.mul_mem_mul
      (show (p : B) ∈ IsLocalRing.maximalIdeal B ^ 1 by simpa only [pow_one] using hp) hd
    simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  obtain ⟨z, hz⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
    (Polynomial.X ^ p : Polynomial B) b d
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hz
  have hb : φ (b ^ p) - b ^ p ∈ IsLocalRing.maximalIdeal B ^ (n + 2) := by
    have heq : φ (b ^ p) - b ^ p = z * d ^ 2 + b ^ (p - 1) * ((p : B) * d) := by
      rw [map_pow]
      have hbd : b + d = φ b := by dsimp [d]; ring
      rw [hbd] at hz
      linear_combination -hz
    rw [heq]
    exact (IsLocalRing.maximalIdeal B ^ (n + 2)).add_mem
      ((IsLocalRing.maximalIdeal B ^ (n + 2)).mul_mem_left z hd2)
      ((IsLocalRing.maximalIdeal B ^ (n + 2)).mul_mem_left _ hpd)
  have hπmem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hpc : π * (φ c - c) ∈ IsLocalRing.maximalIdeal B ^ (n + 2) := by
    have h := Ideal.mul_mem_mul
      (show π ∈ IsLocalRing.maximalIdeal B ^ 1 by simpa only [pow_one] using hπmem) (hg c)
    rw [← pow_add] at h
    simpa [φ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hprod : φ (π * c) - π * c ∈ IsLocalRing.maximalIdeal B ^ (n + 2) := by
    have heq : φ (π * c) - π * c = (φ π - π) * φ c + π * (φ c - c) := by
      rw [map_mul]
      ring
    rw [heq]
    exact (IsLocalRing.maximalIdeal B ^ (n + 2)).add_mem
      ((IsLocalRing.maximalIdeal B ^ (n + 2)).mul_mem_right _ hgp) hpc
  change φ x - x ∈ _
  rw [hx, map_add]
  have heq : φ (b ^ p) + φ (π * c) - (b ^ p + π * c) =
      (φ (b ^ p) - b ^ p) + (φ (π * c) - π * c) := by ring
  rw [heq]
  simpa only [Nat.add_assoc] using (IsLocalRing.maximalIdeal B ^ (n + 2)).add_mem hb hprod

include p in
/-- Inertia membership at every nonnegative depth is detected on any uniformizer. -/
theorem mem_lowerRamificationGroup_iff_uniformizer {π : B} (hπ : Irreducible π)
    {g : G} (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0) (m : ℕ) :
    g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) m ↔
      g • π - π ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by
  induction m with
  | zero =>
    constructor
    · intro h
      rw [lowerRamificationGroup_nat, Ideal.mem_inertia] at h
      exact h π
    · intro _
      simpa only [Nat.cast_zero] using hg
  | succ m ih =>
    constructor
    · intro h
      rw [lowerRamificationGroup_nat, Ideal.mem_inertia] at h
      exact h π
    · intro h
      have hprev := (Ideal.pow_le_pow_right (show m + 1 ≤ (m + 1) + 1 by omega)) h
      exact mem_lowerRamificationGroup_succ_of_uniformizer G p hπ (ih.mpr hprev) h

end FontaineWintenberger
