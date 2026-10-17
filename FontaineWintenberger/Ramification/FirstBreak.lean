/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.HerbrandSubgroup

/-!
# The first upper break of an actual finite fixing subgroup

The least integer lower failure and the actual Herbrand inverse supply a
finite, attained, nonnegative upper break, without prime degree or normality.
-/

@[expose] public section

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G] [FaithfulSMul G R]
variable (H : Subgroup G)

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0
local notation "U" => upperRamificationGroup (R := R) G

/-- The actual first fixing-product failure has a finite nonnegative upper
endpoint, included by the canonical lower ceiling convention. -/
theorem exists_first_upper_break_of_fixingSubgroup
    (hH : H ≠ ⊤) (hzero : H ⊔ I₀ = ⊤) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, 0 ≤ u → (H ⊔ U u = ⊤ ↔ u ≤ b) := by
  classical
  have hex : ∃ n : ℕ,
      H ⊔ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n ≠ ⊤ := by
    obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := R) G
    refine ⟨N, ?_⟩
    simpa only [hN N le_rfl, sup_bot_eq] using hH
  let n : ℕ := Nat.find hex
  have hn : H ⊔ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n ≠ ⊤ :=
    Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    exact hn (by simpa only [hn0, Nat.cast_zero] using hzero)
  let m : ℕ := n - 1
  have hnm : n = m + 1 := by omega
  have hj (j : ℕ) :
      H ⊔ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) j = ⊤ ↔ j < n := by
    constructor
    · intro htop
      by_contra hlt
      have hnj : n ≤ j := by omega
      have hle := sup_le_sup_left
        (lowerRamificationGroup_antitone G (IsLocalRing.maximalIdeal R)
          (show (n : ℤ) ≤ (j : ℤ) by exact_mod_cast hnj)) H
      rw [htop] at hle
      exact hn (top_unique hle)
    · intro hjn
      exact not_ne_iff.mp (Nat.find_min hex hjn)
  have hreal {t : ℝ} (ht : 0 ≤ t) :
      H ⊔ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t = ⊤ ↔ t ≤ (m : ℝ) := by
    have hc : 0 ≤ ⌈t⌉ := by simpa only [Int.ceil_zero] using Int.ceil_mono ht
    have hcn : ((⌈t⌉.toNat : ℕ) : ℤ) = ⌈t⌉ := Int.toNat_of_nonneg hc
    rw [lowerRamificationGroupReal, ← hcn, hj, hnm, Nat.lt_succ_iff]
    constructor
    · intro h
      have hh : ⌈t⌉ ≤ (m : ℤ) := by omega
      exact_mod_cast Int.ceil_le.mp hh
    · intro h
      have hh : ⌈t⌉ ≤ (m : ℤ) := Int.ceil_le.mpr (by exact_mod_cast h)
      omega
  have hm : (-1 : ℝ) ≤ (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : 0 ≤ herbrandFunction (R := R) G m := by
    have h := (strictMonoOn_herbrandFunction (R := R) G).monotoneOn
      (by norm_num : (0 : ℝ) ∈ Set.Ici (-1)) hm (Nat.cast_nonneg m)
    simpa only [herbrandFunction_of_nonpos G le_rfl] using h
  refine ⟨herbrandFunction (R := R) G m, hb, fun u hu => ?_⟩
  have hu' : (-1 : ℝ) ≤ u := by linarith
  have ht : 0 ≤ inverseHerbrandFunction (R := R) G u := by
    have h := (strictMonoOn_inverseHerbrandFunction (R := R) G).monotoneOn
      (by norm_num : (0 : ℝ) ∈ Set.Ici (-1)) hu' hu
    simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl] using h
  have hiff : inverseHerbrandFunction (R := R) G u ≤ (m : ℝ) ↔
      u ≤ herbrandFunction (R := R) G m := by
    constructor
    · intro h
      have hh := (strictMonoOn_herbrandFunction (R := R) G).monotoneOn
        (inverseHerbrandFunction_mem_Ici G u) hm h
      simpa only [herbrandFunction_inverseHerbrandFunction G hu'] using hh
    · intro h
      have hh := (strictMonoOn_inverseHerbrandFunction (R := R) G).monotoneOn
        hu' (herbrandFunction_mem_Ici G hm) h
      simpa only [inverseHerbrandFunction_herbrandFunction G hm] using hh
  have htop : H ⊔ U u = ⊤ ↔ u ≤ herbrandFunction (R := R) G m := by
    exact (hreal ht).trans hiff
  exact htop

end FontaineWintenberger
