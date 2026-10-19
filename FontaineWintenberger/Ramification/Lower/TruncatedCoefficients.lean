/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Teichmuller

/-!
# Canonical coefficients in perfect truncated local rings

In characteristic `p`, nilpotence of the maximal ideal makes the
canonical Teichmüller section an unital ring homomorphism.

## Main definitions

* `truncatedResidueCoefficients`: The canonical unital coefficient section in the truncated local
  ring.

## Main results

* `isAdicComplete_of_isNilpotent_ideal`: A nilpotent ideal gives the discrete, hence complete, adic
  filtration.
* `residueTeichmuller_eq_pow_of_nilpotent`: In the nilpotent range, every lift of the inverse
  Frobenius coordinate has exactly the canonical Teichmüller power, with no limiting error.
* `residueTeichmuller_add_of_isNilpotent`: Nilpotence removes the mixed-characteristic error in
  additivity of Teichmüller representatives.
* `truncatedResidueCoefficients_eq_residueTeichmuller`: Compatibility with the existing canonical
  representatives, for any already installed proof of completeness.
* `residue_truncatedResidueCoefficients`: The coefficient section is a section of the residue map.
* `residue_comp_truncatedResidueCoefficients`: Equality of maps, rather than only equality of
  values, for the splitting of the quotient.
* `truncatedResidueCoefficients_unique`: There is only one unital residue-field section into the
  truncated ring.
* `truncatedResidueCoefficients_eq_pow`: The finite inverse-Frobenius formula, with arbitrary
  nilpotence cutoff, exponent and lift.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- A nilpotent ideal gives the discrete, hence complete, adic filtration.
This uses the ring and does not introduce a completion carrier. -/
theorem isAdicComplete_of_isNilpotent_ideal {R : Type*} [CommRing R]
    (I : Ideal R) (hI : IsNilpotent I) : IsAdicComplete I R := by
  obtain ⟨h, hh⟩ := hI
  change I ^ h = ⊥ at hh
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simpa only [hh, smul_eq_mul, Ideal.mul_top, SModEq.bot] using hx h
  · intro f hf
    refine ⟨f h, fun n => ?_⟩
    by_cases hn : n ≤ h
    · exact hf hn
    · have heq : f h = f n := by
        simpa only [hh, smul_eq_mul, Ideal.mul_top, SModEq.bot] using
          hf (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      rw [heq]

section Truncated

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p]
    [CharP (IsLocalRing.ResidueField R) p]
    [PerfectField (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- In the nilpotent range, every lift of the inverse Frobenius coordinate
has exactly the canonical Teichmüller power, with no limiting error. -/
theorem residueTeichmuller_eq_pow_of_nilpotent
    (h n : ℕ) (hh : IsLocalRing.maximalIdeal R ^ h = ⊥) (hn : h ≤ p ^ n)
    (x : IsLocalRing.ResidueField R) (b : R)
    (hb : IsLocalRing.residue R b = Perfection.coeff (IsLocalRing.ResidueField R) p n
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)) :
    residueTeichmuller R p x = b ^ p ^ n := by
  let y := Perfection.coeff (IsLocalRing.ResidueField R) p n
    ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)
  have hy : y ^ p ^ n = x :=
    Perfection.coeffMonoidHom_pow_p_pow_self
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x) n
  have hmem : residueTeichmuller R p y - b ∈ IsLocalRing.maximalIdeal R := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact (residue_residueTeichmuller R p y).trans hb.symm
  have hz : (residueTeichmuller R p y - b) ^ p ^ n = 0 := by
    apply Ideal.mem_bot.mp
    rw [← hh]
    exact Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hmem (p ^ n))
  rw [sub_pow_char_pow] at hz
  rw [← hy, map_pow]
  exact sub_eq_zero.mp hz

/-- Nilpotence removes the mixed-characteristic error in additivity of
Teichmüller representatives. -/
theorem residueTeichmuller_add_of_isNilpotent
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R)) (x y : IsLocalRing.ResidueField R) :
    residueTeichmuller R p (x + y) = residueTeichmuller R p x + residueTeichmuller R p y := by
  obtain ⟨h, hh⟩ := hI
  change IsLocalRing.maximalIdeal R ^ h = ⊥ at hh
  have hn : h ≤ p ^ h := (Nat.le_of_lt (Nat.lt_two_pow_self (n := h))).trans
    (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le h)
  let r : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField R :=
    (Perfection.coeff (IsLocalRing.ResidueField R) p h).comp
      (PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv.toRingHom
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := R) (r x)
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (R := R) (r y)
  have hab : IsLocalRing.residue R (a + b) = r (x + y) := by
    rw [map_add, ha, hb, map_add]
  rw [residueTeichmuller_eq_pow_of_nilpotent R p h h hh hn (x + y) (a + b) hab,
    residueTeichmuller_eq_pow_of_nilpotent R p h h hh hn x a ha,
    residueTeichmuller_eq_pow_of_nilpotent R p h h hh hn y b hb,
    add_pow_char_pow]

end Truncated

section CanonicalSection

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (p : ℕ) [Fact p.Prime] [CharP R p]
    [CharP (IsLocalRing.ResidueField R) p]
    [PerfectField (IsLocalRing.ResidueField R)]

/-- The canonical unital coefficient section in the truncated
local ring. Its underlying multiplicative map is the existing Teichmüller
section; nilpotence supplies completeness and characteristic `p` supplies
additivity. -/
def truncatedResidueCoefficients (hI : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    IsLocalRing.ResidueField R →+* R := by
  letI := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal R) hI
  exact { residueTeichmuller R p with
    map_add' := residueTeichmuller_add_of_isNilpotent R p hI }

/-- Compatibility with the existing canonical representatives, for any
already installed proof of completeness. -/
theorem truncatedResidueCoefficients_eq_residueTeichmuller
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    (truncatedResidueCoefficients R p hI).toMonoidWithZeroHom = residueTeichmuller R p := rfl

/-- The coefficient section is a section of the residue map. -/
@[simp]
theorem residue_truncatedResidueCoefficients
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R)) (x : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (truncatedResidueCoefficients R p hI x) = x := by
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal R) hI
  exact residue_residueTeichmuller R p x

/-- Equality of maps, rather than only equality of values, for the splitting
of the quotient. -/
theorem residue_comp_truncatedResidueCoefficients
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    (IsLocalRing.residue R).comp (truncatedResidueCoefficients R p hI) = RingHom.id _ :=
  RingHom.ext (residue_truncatedResidueCoefficients R p hI)

/-- There is only one unital residue-field section into the truncated ring. -/
theorem truncatedResidueCoefficients_unique
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R))
    (s : IsLocalRing.ResidueField R →+* R)
    (hs : ∀ x, IsLocalRing.residue R (s x) = x) :
    s = truncatedResidueCoefficients R p hI := by
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal R) hI
  have h := residueTeichmuller_unique R p s.toMonoidWithZeroHom hs
  exact RingHom.ext (fun x => DFunLike.congr_fun h x)

/-- The finite inverse-Frobenius formula, with arbitrary nilpotence cutoff,
exponent and lift. -/
theorem truncatedResidueCoefficients_eq_pow
    (hI : IsNilpotent (IsLocalRing.maximalIdeal R))
    (h n : ℕ) (hh : IsLocalRing.maximalIdeal R ^ h = ⊥) (hn : h ≤ p ^ n)
    (x : IsLocalRing.ResidueField R) (b : R)
    (hb : IsLocalRing.residue R b = Perfection.coeff (IsLocalRing.ResidueField R) p n
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)) :
    truncatedResidueCoefficients R p hI x = b ^ p ^ n := by
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal R) hI
  exact residueTeichmuller_eq_pow_of_nilpotent R p h n hh hn x b hb

/-- Both the exponent and the arbitrary lift disappear from the finite
formula, even when the two exponents are different. -/
theorem truncated_residue_pow_independent
    (h n m : ℕ) (hh : IsLocalRing.maximalIdeal R ^ h = ⊥)
    (hn : h ≤ p ^ n) (hm : h ≤ p ^ m)
    (x : IsLocalRing.ResidueField R) (a b : R)
    (ha : IsLocalRing.residue R a = Perfection.coeff (IsLocalRing.ResidueField R) p n
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x))
    (hb : IsLocalRing.residue R b = Perfection.coeff (IsLocalRing.ResidueField R) p m
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)) :
    a ^ p ^ n = b ^ p ^ m := by
  have hI : IsNilpotent (IsLocalRing.maximalIdeal R) := ⟨h, hh⟩
  exact (truncatedResidueCoefficients_eq_pow R p hI h n hh hn x a ha).symm.trans
    (truncatedResidueCoefficients_eq_pow R p hI h m hh hm x b hb)

variable (S : Type*) [CommRing S] [IsLocalRing S] [CharP S p]
    [CharP (IsLocalRing.ResidueField S) p] [PerfectField (IsLocalRing.ResidueField S)]

/-- Canonical coefficients commute with the local unital ring map
and its residue-field map. No compatibility of chosen lifts is assumed. -/
theorem truncatedResidueCoefficients_naturality
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hS : IsNilpotent (IsLocalRing.maximalIdeal S)) (f : R →+* S) [IsLocalHom f]
    (x : IsLocalRing.ResidueField R) :
    f (truncatedResidueCoefficients R p hR x) =
      truncatedResidueCoefficients S p hS (IsLocalRing.ResidueField.map f x) := by
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal R) hR
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal S) hS
  exact residueTeichmuller_naturality R p S f x

/-- The naturality square as an equality of ring homomorphisms. -/
theorem truncatedResidueCoefficients_naturality_comp
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hS : IsNilpotent (IsLocalRing.maximalIdeal S)) (f : R →+* S) [IsLocalHom f] :
    f.comp (truncatedResidueCoefficients R p hR) =
      (truncatedResidueCoefficients S p hS).comp (IsLocalRing.ResidueField.map f) :=
  RingHom.ext (truncatedResidueCoefficients_naturality R p S hR hS f)

end CanonicalSection

end FontaineWintenberger
