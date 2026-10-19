/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.Basic
public import FontaineWintenberger.LocalField.Spectral.IntegralGenerator
public import FontaineWintenberger.Ramification.Lower.GaloisGroup

/-!
# Computing ramification on an integral generator

The intrinsic ideal-inertia groups and order function can be evaluated on a
single algebra generator. Monogenicity is supplied by the integral-generator
producer, rather than assumed for the finite-extension specialization.
-/

@[expose] public section

namespace FontaineWintenberger

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- Congruences on a generator detect ideal inertia. -/
theorem mem_inertia_iff_generator {x : S} (hx : Algebra.adjoin R {x} = ⊤)
    (I : Ideal S) (g : G) : g ∈ I.inertia G ↔ g • x - x ∈ I := by
  rw [Ideal.mem_inertia]
  constructor
  · intro hg
    exact hg x
  · intro hg y
    have hy : y ∈ Algebra.adjoin R {x} := hx ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem z hz => simpa only [Set.mem_singleton_iff.mp hz] using hg
    | algebraMap r => simp only [smul_algebraMap, sub_self, I.zero_mem]
    | add y z hy hz ihy ihz =>
      simpa only [smul_add, add_sub_add_comm] using I.add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      simpa only [smul_mul'] using I.mul_sub_mul_mem ihy ihz

end Algebra

section DiscreteValuation

open IsDiscreteValuationRing IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Algebra R S]
variable (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- The infimum over all integers is attained at any integral algebra generator. -/
theorem ramificationOrder_eq_generator {x : S} (hx : Algebra.adjoin R {x} = ⊤) (g : G) :
    ramificationOrder (R := S) G g = addVal S (g • x - x) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [ramificationOrder, le_iInf_iff]
  simp only [← mem_maximalIdeal_pow_iff_addVal]
  rw [← Ideal.mem_inertia]
  exact mem_inertia_iff_generator G hx (IsLocalRing.maximalIdeal S ^ n) g

/-- Integer lower membership is a single normalized integral valuation inequality. -/
theorem mem_lowerRamificationGroup_iff_generator {x : S}
    (hx : Algebra.adjoin R {x} = ⊤) (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal S) n ↔
      ((n + 1).toNat : ℕ∞) ≤ addVal S (g • x - x) := by
  rw [mem_lowerRamificationGroup_iff_le_order, ramificationOrder_eq_generator G hx]

end DiscreteValuation

section Spectral

open IsLocalRing IsDiscreteValuationRing

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField (ResidueField (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "D" => ValuationSubring.decompositionSubgroup K (spectralIntegerRing K L)

instance spectralIntegerRing_decompositionSubgroup_smulCommClass : SMulCommClass D OK OL where
  smul_comm g r x := by
    apply Subtype.ext
    change (g : L ≃ₐ[K] L) ((r : K) • (x : L)) =
      (r : K) • (g : L ≃ₐ[K] L) (x : L)
    exact map_smul (g : L ≃ₐ[K] L) (r : K) (x : L)

/-- Monogenicity supplies a generator on which every intrinsic order is attained. -/
theorem spectralIntegerRing_exists_order_generator :
    ∃ x : OL, ∀ g : D,
      (OL).ramificationOrder K g = addVal OL (g • x - x) := by
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K L
  exact ⟨x, fun g => ramificationOrder_eq_generator D hx g⟩

/-- The same proved generator computes ramification for the full field automorphism group. -/
theorem spectralIntegerRing_exists_galois_order_generator :
    ∃ x : OL, ∀ g : L ≃ₐ[K] L,
      ramificationOrder (R := OL) (L ≃ₐ[K] L) g = addVal OL (g • x - x) := by
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K L
  exact ⟨x, fun g => ramificationOrder_eq_generator (L ≃ₐ[K] L) hx g⟩

end Spectral

end FontaineWintenberger
