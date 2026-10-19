/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Herbrand.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Herbrand change of parameter for subgroups

## Herbrand change of parameter for arbitrary subgroups

The subgroup is allowed to be nonnormal. Its lower groups determine
its Herbrand function on the same valuation ring as the ambient action.

## The first upper break of a finite fixing subgroup

The least integer lower failure and the Herbrand inverse supply a
finite, attained, nonnegative upper break, without prime degree or normality.
-/

@[expose] public section

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R]
variable (H : Subgroup G)

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0
local notation "A₀" => (H ⊓ I₀ : Subgroup G)
local notation "U₀" => upperRamificationGroup (R := R) G

/-- The subgroup lower group has the cardinality of the ambient intersection. -/
theorem card_lowerRamificationGroupReal_subgroup (t : ℝ) :
    Nat.card (lowerRamificationGroupReal H (IsLocalRing.maximalIdeal R) t) =
      Nat.card ↥(H ⊓ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
  let e : lowerRamificationGroupReal H (IsLocalRing.maximalIdeal R) t ≃
      ↥(H ⊓ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) :=
    { toFun := fun g => ⟨g.1.1, ⟨g.1.2, g.2⟩⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- The inertia group of the restricted action is the intersection. -/
theorem card_lowerRamificationGroup_zero_subgroup :
    Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal R) 0) = Nat.card A₀ := by
  simpa only [lowerRamificationGroupReal_intCast] using
    card_lowerRamificationGroupReal_subgroup (R := R) G H (0 : ℤ)

variable [Finite G]

/-- The cardinality identity underlying the nonnormal subgroup change of parameter. -/
theorem subgroup_upperRelIndex_mul_card {u : ℝ} (hu : 0 ≤ u) :
    (A₀ ⊔ U₀ u).relIndex I₀ * Nat.card A₀ * Nat.card (U₀ u) =
      Nat.card I₀ * Nat.card
        (lowerRamificationGroupReal H (IsLocalRing.maximalIdeal R)
          (inverseHerbrandFunction (R := R) G u)) := by
  have hU : U₀ u ≤ I₀ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      upperRamificationGroup_antitoneOn (R := R) G
        (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
  have hsup : A₀ ⊔ U₀ u ≤ I₀ := sup_le inf_le_right hU
  have hm := Subgroup.relIndex_mul_relIndex (U₀ u) (A₀ ⊔ U₀ u) I₀ le_sup_right hsup
  rw [Subgroup.relIndex_sup_right] at hm
  have hcard := (U₀ u).relIndex_mul_card A₀
  have hinf : U₀ u ⊓ A₀ = H ⊓ U₀ u := by
    rw [inf_comm (U₀ u) A₀, inf_assoc, inf_eq_right.mpr hU]
  rw [hinf] at hcard
  have hcard' := (U₀ u).relIndex_mul_card I₀
  rw [inf_eq_left.mpr hU] at hcard'
  rw [card_lowerRamificationGroupReal_subgroup]
  change _ = Nat.card I₀ * Nat.card ↥(H ⊓ U₀ u)
  calc
    _ = (A₀ ⊔ U₀ u).relIndex I₀ *
        ((U₀ u).relIndex A₀ * Nat.card ↥(H ⊓ U₀ u)) * Nat.card (U₀ u) := by
          rw [hcard]
    _ = ((U₀ u).relIndex A₀ * (A₀ ⊔ U₀ u).relIndex I₀ * Nat.card (U₀ u)) *
        Nat.card ↥(H ⊓ U₀ u) := by ring
    _ = _ := by rw [hm, hcard']

/-- The subgroup cardinalities give the chain-rule slope. -/
theorem subgroup_herbrand_slope_mul {u : ℝ} (hu : 0 ≤ u) :
    ((Nat.card (lowerRamificationGroupReal H (IsLocalRing.maximalIdeal R)
        (inverseHerbrandFunction (R := R) G u)) : ℝ) /
      Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal R) 0)) *
      ((Nat.card I₀ : ℝ) / Nat.card (U₀ u)) =
        ((A₀ ⊔ U₀ u).relIndex I₀ : ℝ) := by
  rw [card_lowerRamificationGroup_zero_subgroup]
  have h := congrArg (fun n : ℕ => (n : ℝ))
    (subgroup_upperRelIndex_mul_card (R := R) G H hu)
  push_cast at h
  have hA : (Nat.card A₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hU : (Nat.card (U₀ u) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  nlinarith

/-- Indices of these subgroups are positive because the ambient group is finite. -/
theorem subgroup_upperRelIndex_pos (u : ℝ) : 0 < (A₀ ⊔ U₀ u).relIndex I₀ := by
  exact Nat.card_pos

/-- The finite subgroup index increases with the upper parameter. -/
theorem subgroup_upperRelIndex_monotoneOn :
    MonotoneOn (fun u : ℝ => (A₀ ⊔ U₀ u).relIndex I₀) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hU : U₀ u ≤ I₀ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      upperRamificationGroup_antitoneOn (R := R) G
        (by norm_num : -1 ≤ (0 : ℝ)) (by linarith [hu] : -1 ≤ u) hu
  have hmul := Subgroup.relIndex_mul_relIndex (A₀ ⊔ U₀ v) (A₀ ⊔ U₀ u) I₀
    (sup_le_sup_left (upperRamificationGroup_antitoneOn (R := R) G
      (by linarith [hu] : -1 ≤ u) (by linarith [hv] : -1 ≤ v) huv) _)
    (sup_le inf_le_right hU)
  exact Nat.le_of_dvd (subgroup_upperRelIndex_pos (R := R) G H v)
    (dvd_of_mul_left_eq _ hmul)

/-- The subgroup index is integrable on every nonnegative compact interval. -/
theorem intervalIntegrable_subgroup_upperRelIndex {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun v : ℝ => ((A₀ ⊔ U₀ v).relIndex I₀ : ℝ))
      MeasureTheory.volume 0 u := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hu]
  intro v hv w hw hvw
  exact Nat.cast_le.mpr (subgroup_upperRelIndex_monotoneOn (R := R) G H hv.1 hw.1 hvw)

variable [FaithfulSMul G R]

/-- The nonnormal subgroup composite has the finite-index slope off finitely many points. -/
theorem exists_subgroup_herbrand_comp_derivative_breaks :
    ∃ S : Finset ℝ, ∀ u : ℝ, 0 < u → u ∉ S →
      HasDerivAt
        ((herbrandFunction (R := R) H) ∘ (inverseHerbrandFunction (R := R) G))
        ((A₀ ⊔ U₀ u).relIndex I₀ : ℝ) u := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_inverseHerbrandFunction_finite_derivative_breaks (R := R) G
  obtain ⟨S₂, hS₂⟩ := exists_herbrandFunction_finite_derivative_breaks (R := R) H
  refine ⟨S₁ ∪ S₂.image (herbrandFunction (R := R) G), ?_⟩
  intro u hu hS
  have hnot₁ : u ∉ S₁ := fun h => hS (Finset.mem_union_left _ h)
  have hnot₂ : inverseHerbrandFunction (R := R) G u ∉ S₂ := by
    intro h
    apply hS
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, h,
      herbrandFunction_inverseHerbrandFunction G (by linarith)⟩)
  have hpos : 0 < inverseHerbrandFunction (R := R) G u := by
    have h := strictMonoOn_inverseHerbrandFunction (R := R) G
      (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
    simpa only [inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl] using h
  have hd := (hS₂ _ hpos hnot₂).comp u (hS₁ _ hu hnot₁)
  rw [subgroup_herbrand_slope_mul G H hu.le] at hd
  exact hd

/-- The finite Herbrand subgroup composite is the integral of coset indices. -/
theorem subgroup_herbrandFunction_comp_inverse_eq_integral {u : ℝ} (hu : 0 ≤ u) :
    herbrandFunction (R := R) H (inverseHerbrandFunction (R := R) G u) =
      ∫ v in (0 : ℝ)..u, ((A₀ ⊔ U₀ v).relIndex I₀ : ℝ) := by
  obtain ⟨S, hS⟩ := exists_subgroup_herbrand_comp_derivative_breaks (R := R) G H
  have hcont : ContinuousOn
      ((herbrandFunction (R := R) H) ∘ (inverseHerbrandFunction (R := R) G))
      (Set.Icc 0 u) := by
    apply (continuousOn_herbrandFunction (R := R) H).comp
      (continuous_inverseHerbrandFunction (R := R) G).continuousOn
    intro v hv
    exact inverseHerbrandFunction_mem_Ici G v
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    ((herbrandFunction (R := R) H) ∘ (inverseHerbrandFunction (R := R) G)) _
    hu S.countable_toSet hcont (fun v hv => hS v hv.1.1 hv.2)
    (intervalIntegrable_subgroup_upperRelIndex (R := R) G H hu)
  simpa only [Function.comp_apply,
    inverseHerbrandFunction_of_nonpos G (by norm_num) le_rfl,
    herbrandFunction_of_nonpos H le_rfl, sub_zero] using h.symm

omit [FaithfulSMul G R] in
/-- The same change of parameter is the identity on the initial half interval. -/
theorem subgroup_herbrandFunction_comp_inverse_of_nonpos {u : ℝ}
    (hu : -1 ≤ u) (hu' : u ≤ 0) :
    herbrandFunction (R := R) H (inverseHerbrandFunction (R := R) G u) = u := by
  rw [inverseHerbrandFunction_of_nonpos G hu hu', herbrandFunction_of_nonpos H hu']

end FontaineWintenberger

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G] [FaithfulSMul G R]
variable (H : Subgroup G)

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0
local notation "U" => upperRamificationGroup (R := R) G

/-- The first fixing-product failure has a finite nonnegative upper
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
