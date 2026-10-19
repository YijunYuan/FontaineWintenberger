/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Basic
public import FontaineWintenberger.Mathlib.GroupTheory.PrimeChain
public import Mathlib.GroupTheory.PGroup

/-!
# Wild inertia

## Depth raising in the lower groups

An element of the `n`-th congruence group moves the `k`-th maximal-ideal
power by order at least `n + k`. In positive residue characteristic,
taking the residue-characteristic power raises every positive depth.

## Relative prime-step chains in finite p-groups

Each proper subgroup is contained in a maximal subgroup, which is normal
of index `p`. Recursion in the finite subgroup lattice gives a finite chain
of inclusions, represented by the canonical reflexive transitive closure.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise

private theorem pow_sub_pow_mem_pow {B : Type*} [CommRing B] (I : Ideal B)
    {a b : B} (ha : a ∈ I) (hb : b ∈ I) {n : ℕ} (hd : a - b ∈ I ^ (n + 1))
    (k : ℕ) : a ^ (k + 1) - b ^ (k + 1) ∈ I ^ (n + k + 1) := by
  induction k with
  | zero => simpa only [zero_add, Nat.add_zero, pow_one] using hd
  | succ k ih =>
    have hfirst : a * (a ^ (k + 1) - b ^ (k + 1)) ∈ I ^ (n + (k + 1) + 1) := by
      have h := Ideal.mul_mem_mul (show a ∈ I ^ 1 by simpa only [pow_one] using ha) ih
      simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hsecond : (a - b) * b ^ (k + 1) ∈ I ^ (n + (k + 1) + 1) := by
      have h := Ideal.mul_mem_mul hd (Ideal.pow_mem_pow hb (k + 1))
      simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have heq : a ^ ((k + 1) + 1) - b ^ ((k + 1) + 1) =
        a * (a ^ (k + 1) - b ^ (k + 1)) + (a - b) * b ^ (k + 1) := by
      rw [pow_succ a (k + 1), pow_succ b (k + 1)]
      ring
    rw [heq]
    exact (I ^ (n + (k + 1) + 1)).add_mem hfirst hsecond

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type*) [Group G] [MulSemiringAction G B]

/-- The lower congruence action gains the input's ideal-power order. -/
theorem smul_sub_mem_maximalIdeal_pow_add {n k : ℕ} {g : G}
    (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n)
    {x : B} (hx : x ∈ IsLocalRing.maximalIdeal B ^ k) :
    g • x - x ∈ IsLocalRing.maximalIdeal B ^ (n + k) := by
  rw [lowerRamificationGroup_nat, Ideal.mem_inertia] at hg
  cases k with
  | zero =>
    exact (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega)) (hg x)
  | succ k =>
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hπmem : π ∈ IsLocalRing.maximalIdeal B := by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    have hsp : g • π ∈ IsLocalRing.maximalIdeal B := by
      have h : g • π ∈ g • IsLocalRing.maximalIdeal B :=
        Ideal.smul_mem_pointwise_smul_iff.mpr hπmem
      simpa only [smul_maximalIdeal G g] using h
    obtain ⟨b, rfl⟩ : π ^ (k + 1) ∣ x := by
      simpa only [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx
    have hpow := pow_sub_pow_mem_pow (IsLocalRing.maximalIdeal B) hsp hπmem (hg π) k
    have hfirst := (IsLocalRing.maximalIdeal B ^ (n + k + 1)).mul_mem_right (g • b) hpow
    have hsecond : π ^ (k + 1) * (g • b - b) ∈ IsLocalRing.maximalIdeal B ^ (n + (k + 1)) := by
      have hdn := (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega)) (hg b)
      have h := Ideal.mul_mem_mul (Ideal.pow_mem_pow hπmem (k + 1)) hdn
      simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have heq : g • (π ^ (k + 1) * b) - π ^ (k + 1) * b =
        ((g • π) ^ (k + 1) - π ^ (k + 1)) * (g • b) + π ^ (k + 1) * (g • b - b) := by
      change (MulSemiringAction.toRingHom G B g) (π ^ (k + 1) * b) - π ^ (k + 1) * b = _
      rw [map_mul, map_pow]
      change (g • π) ^ (k + 1) * (g • b) - π ^ (k + 1) * b = _
      ring
    rw [heq]
    exact (IsLocalRing.maximalIdeal B ^ (n + (k + 1))).add_mem
      (by simpa only [Nat.add_assoc] using hfirst) hsecond

/-- Taking the residue-characteristic power raises every positive lower depth. -/
theorem pow_mem_lowerRamificationGroup_succ (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] {n : ℕ} (hn : 1 ≤ n) {g : G}
    (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n) :
    g ^ p ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (n + 1 : ℕ) := by
  rw [lowerRamificationGroup_nat, Ideal.mem_inertia]
  intro x
  let I := IsLocalRing.maximalIdeal B ^ (n + 2)
  let q : B →+* B ⧸ I := Ideal.Quotient.mk I
  let d := g • x - x
  have hd : d ∈ IsLocalRing.maximalIdeal B ^ (n + 1) := by
    have hg' := hg
    rw [lowerRamificationGroup_nat, Ideal.mem_inertia] at hg'
    exact hg' x
  have hq (j : ℕ) : q (g ^ j • d) = q d := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (Ideal.pow_le_pow_right (show n + 2 ≤ n + (n + 1) by omega))
      (smul_sub_mem_maximalIdeal_pow_add G
        ((lowerRamificationGroup G (IsLocalRing.maximalIdeal B) n).pow_mem hg j) hd)
  have hiter (j : ℕ) : q (g ^ j • x - x) = (j : B ⧸ I) * q d := by
    induction j with
    | zero => simp
    | succ j ih =>
      have heq : g ^ (j + 1) • x - x = g ^ j • d + (g ^ j • x - x) := by
        dsimp [d]
        rw [pow_succ, mul_smul, smul_sub]
        abel
      rw [heq, map_add, hq, ih]
      push_cast
      ring
  have hp : (p : B) ∈ IsLocalRing.maximalIdeal B := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue B (p : B) = 0
    simp
  have hpd : (p : B) * d ∈ I := by
    have h := Ideal.mul_mem_mul
      (show (p : B) ∈ IsLocalRing.maximalIdeal B ^ 1 by simpa only [pow_one] using hp) hd
    simpa only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hz : q (g ^ p • x - x) = 0 := by
    rw [hiter]
    rw [← map_natCast q p, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpd
  simpa only [Nat.add_assoc] using (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Iterated residue-characteristic powers reach arbitrarily deep lower groups. -/
theorem pow_pow_mem_lowerRamificationGroup (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] {g : G}
    (hg : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1) (j : ℕ) :
    g ^ (p ^ j) ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal B) (j + 1 : ℕ) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, zero_add, Nat.cast_one] using hg
  | succ j ih =>
    simpa only [pow_succ p j, pow_mul, Nat.succ_eq_add_one] using
      pow_mem_lowerRamificationGroup_succ G p (show 1 ≤ j + 1 by omega) ih

/-- The first wild ramification group is a finite `p`-group.
No finiteness or perfection of the residue field is needed. -/
theorem lowerRamificationGroup_one_isPGroup [Finite G] [FaithfulSMul G B]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField B) p] :
    IsPGroup p (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1) := by
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := B) G
  apply isPGroup_iff_exists_pow_pow_eq_one.mpr
  refine ⟨N, fun g => ?_⟩
  apply Subtype.ext
  change (g : G) ^ (p ^ N) = 1
  have h := pow_pow_mem_lowerRamificationGroup G p g.property N
  rw [hN (N + 1) (by omega)] at h
  exact Subgroup.mem_bot.mp h

end FontaineWintenberger

namespace FontaineWintenberger

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [MulSemiringAction G B] [FaithfulSMul G B] [CharP (IsLocalRing.ResidueField B) p]

/-- Every relative subgroup inclusion inside wild inertia has a
finite refinement by normal steps of index the residue characteristic. -/
theorem wild_subgroup_prime_chain
    (K H : Subgroup (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1)) (hHK : H ≤ K) :
    Relation.ReflTransGen
      (fun M N : Subgroup (lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1) =>
        N ≤ M ∧ (N.subgroupOf M).Normal ∧ (N.subgroupOf M).index = p) K H :=
  subgroup_prime_chain (lowerRamificationGroup_one_isPGroup G p) K H hHK

end FontaineWintenberger
