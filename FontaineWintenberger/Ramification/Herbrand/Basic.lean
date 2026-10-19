/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Herbrand function

## Herbrand functions and finite truncations of intrinsic ramification order

Extended orders are capped before conversion to real numbers. In particular
the identity contributes the full finite cap. The Herbrand function is
defined by its integral of the real lower-group cardinalities.

## The Herbrand order isomorphism and its inverse

The integral-defined function is strictly increasing and onto its
half-line. Its inverse is obtained from this proved order isomorphism.

## Main definitions

* `truncatedRamificationOrder`: The intrinsic extended order capped at the nonnegative part of `t +
  1`.
* `herbrandFunction`: The Herbrand function, integrating real lower-group cardinalities.
* `herbrandSum`: The finite-sum expression, to be compared with the defining integral.
* `herbrandOrderIso`: The Herbrand integral induces an order isomorphism of the half-line.
* `inverseHerbrandFunction`: Inverse Herbrand function; outside the domain the argument is clamped
  to `-1`.

## Main results

* `hasDerivAt_truncatedRamificationOrder`: Away from the integer breaks, a capped order has
  derivative its lower-group indicator.
* `hasDerivAt_herbrandSum`: The finite sum has the lower-cardinality ratio as derivative away from
  breaks.
* `integral_card_lower_eq_herbrandSum`: Equality with the defining integral on nonnegative indices.
* `herbrandFunction_eq_sum`: The finite sum is proved equal to the integral on its entire domain.
* `hasDerivAt_herbrandFunction`: The integral-defined Herbrand function has the cardinality-ratio
  derivative.
* `herbrandFunction_lower_bound`: The identity summand gives a linear lower bound with a positive
  finite denominator.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal
open MeasureTheory

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R]

/-- The intrinsic extended order capped at the nonnegative part of `t + 1`. -/
noncomputable def truncatedRamificationOrder (g : G) (t : ℝ) : ℝ :=
  (min (ramificationOrder (R := R) G g : ℝ≥0∞) (ENNReal.ofReal (t + 1))).toReal

theorem truncatedRamificationOrder_of_order_top {g : G}
    (hg : ramificationOrder (R := R) G g = ⊤) (t : ℝ) :
    truncatedRamificationOrder (R := R) G g t = max (t + 1) 0 := by
  simp [truncatedRamificationOrder, hg, ENNReal.toReal_ofReal']

theorem truncatedRamificationOrder_of_order_nat {g : G} {n : ℕ}
    (hg : ramificationOrder (R := R) G g = n) (t : ℝ) :
    truncatedRamificationOrder (R := R) G g t = min (n : ℝ) (max (t + 1) 0) := by
  rw [truncatedRamificationOrder, hg, ENat.toENNReal_coe,
    ENNReal.toReal_min (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top]
  simp [ENNReal.toReal_ofReal']

theorem truncatedRamificationOrder_nonneg (g : G) (t : ℝ) :
    0 ≤ truncatedRamificationOrder (R := R) G g t := ENNReal.toReal_nonneg

theorem truncatedRamificationOrder_le (g : G) (t : ℝ) :
    truncatedRamificationOrder (R := R) G g t ≤ max (t + 1) 0 := by
  simpa only [truncatedRamificationOrder, ENNReal.toReal_ofReal'] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right
      (ramificationOrder (R := R) G g : ℝ≥0∞) (ENNReal.ofReal (t + 1)))

theorem continuous_truncatedRamificationOrder (g : G) :
    Continuous (truncatedRamificationOrder (R := R) G g) := by
  rcases eq_or_ne (ramificationOrder (R := R) G g) ⊤ with hg | hg
  · have hfun : truncatedRamificationOrder (R := R) G g = fun t => max (t + 1) 0 :=
      funext (truncatedRamificationOrder_of_order_top G hg)
    rw [hfun]
    exact (continuous_id.add_const 1).max continuous_const
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    have hfun : truncatedRamificationOrder (R := R) G g =
        fun t => min (n : ℝ) (max (t + 1) 0) :=
      funext (truncatedRamificationOrder_of_order_nat G hn.symm)
    rw [hfun]
    exact continuous_const.min ((continuous_id.add_const 1).max continuous_const)

theorem monotone_truncatedRamificationOrder (g : G) :
    Monotone (truncatedRamificationOrder (R := R) G g) := by
  intro s t hst
  apply ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))
  exact min_le_min_left _ (ENNReal.ofReal_le_ofReal (by linarith))

@[simp]
theorem truncatedRamificationOrder_one (t : ℝ) (ht : -1 ≤ t) :
    truncatedRamificationOrder (R := R) G 1 t = t + 1 := by
  rw [truncatedRamificationOrder_of_order_top G (ramificationOrder_one G)]
  exact max_eq_left (by linarith)

open scoped Classical in
theorem truncatedRamificationOrder_zero (g : G) :
    truncatedRamificationOrder (R := R) G g 0 =
      if g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0 then 1 else 0 := by
  classical
  rw [mem_lowerRamificationGroup_iff_le_order]
  simp only [Int.reduceAdd, Int.toNat_one, Nat.cast_one]
  generalize hj : ramificationOrder (R := R) G g = j
  cases j using ENat.recTopCoe with
  | top => simp [truncatedRamificationOrder, hj]
  | coe n =>
    rw [truncatedRamificationOrder_of_order_nat G hj]
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hr : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      simp [min_eq_right hr, show (1 : ℕ∞) ≤ n by exact_mod_cast hn']

open scoped Classical in
/-- Away from the integer breaks, a capped order has derivative its lower-group indicator. -/
theorem hasDerivAt_truncatedRamificationOrder (g : G) {t : ℝ} (ht : -1 < t)
    (hbreak : ∀ n : ℕ, t + 1 ≠ n) :
    HasDerivAt (truncatedRamificationOrder (R := R) G g)
      (if g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t then 1 else 0) t := by
  have hp : 0 < t + 1 := by linarith
  rcases eq_or_ne (ramificationOrder (R := R) G g) ⊤ with hg | hg
  · have hm : g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t := by
      rw [mem_lowerRamificationGroupReal_iff_le_order, hg]
      simp
    rw [ite_eq_left hm]
    apply ((hasDerivAt_id t).add_const 1).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const (continuous_id.add_const 1)).mem_nhds hp]
      with s hs
    change 0 < s + 1 at hs
    rw [truncatedRamificationOrder_of_order_top G hg, max_eq_left hs.le]
    rfl
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    have hm : g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t ↔
        t + 1 ≤ (n : ℝ) := by
      rw [mem_lowerRamificationGroupReal_iff_le_order, ← hn, ENat.toENNReal_coe,
        ENNReal.ofReal_le_natCast]
    rcases lt_or_gt_of_ne (hbreak n) with hlt | hgt
    · rw [ite_eq_left (hm.mpr hlt.le)]
      apply ((hasDerivAt_id t).add_const 1).congr_of_eventuallyEq
      filter_upwards
        [(isOpen_lt continuous_const (continuous_id.add_const 1)).mem_nhds hp,
          (isOpen_lt (continuous_id.add_const 1) continuous_const).mem_nhds hlt] with s hs hn'
      change 0 < s + 1 at hs
      change s + 1 < (n : ℝ) at hn'
      rw [truncatedRamificationOrder_of_order_nat G hn.symm,
        max_eq_left hs.le, min_eq_right hn'.le]
      rfl
    · rw [ite_eq_right (by simpa only [hm, not_le] using hgt)]
      apply (hasDerivAt_const t (n : ℝ)).congr_of_eventuallyEq
      filter_upwards
        [(isOpen_lt continuous_const (continuous_id.add_const 1)).mem_nhds hgt] with s hs
      change (n : ℝ) < s + 1 at hs
      rw [truncatedRamificationOrder_of_order_nat G hn.symm,
        max_eq_left ((Nat.cast_nonneg n).trans hs.le), min_eq_left hs.le]

variable [Finite G]

theorem antitone_card_lowerRamificationGroupReal :
    Antitone (fun t : ℝ =>
      (Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) : ℝ)) := by
  intro s t hst
  have hle := lowerRamificationGroupReal_antitone G (IsLocalRing.maximalIdeal R) hst
  exact Nat.cast_le.mpr
    (Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle))

theorem intervalIntegrable_card_lowerRamificationGroupReal (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) : ℝ)) volume a b :=
  (antitone_card_lowerRamificationGroupReal (R := R) G).intervalIntegrable

/-- The Herbrand function, integrating real lower-group cardinalities. -/
noncomputable def herbrandFunction (t : ℝ) : ℝ :=
  if t ≤ 0 then t else
    ∫ s in (0 : ℝ)..t,
      (Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) s) : ℝ) /
        Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)

/-- The finite-sum expression, to be compared with the defining integral. -/
noncomputable def herbrandSum (t : ℝ) : ℝ :=
  letI := Fintype.ofFinite G
  (∑ g : G, truncatedRamificationOrder (R := R) G g t) /
    Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) - 1

open scoped Classical in
theorem sum_truncatedRamificationOrder_zero :
    letI := Fintype.ofFinite G
    (∑ g : G, truncatedRamificationOrder (R := R) G g 0) =
      (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)
  simp [truncatedRamificationOrder_zero, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem herbrandSum_zero : herbrandSum (R := R) G 0 = 0 := by
  rw [herbrandSum, sum_truncatedRamificationOrder_zero,
    div_self (show (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) ≠ 0
      by exact_mod_cast Nat.card_pos.ne'), sub_self]

theorem continuous_herbrandSum : Continuous (herbrandSum (R := R) G) := by
  let := Fintype.ofFinite G
  exact ((continuous_finsetSum Finset.univ
    (fun g _ => continuous_truncatedRamificationOrder (R := R) G g)).div_const _).sub
        continuous_const

open scoped Classical in
/-- The finite sum has the lower-cardinality ratio as derivative away from breaks. -/
theorem hasDerivAt_herbrandSum {t : ℝ} (ht : -1 < t)
    (hbreak : ∀ n : ℕ, t + 1 ≠ n) :
    HasDerivAt (herbrandSum (R := R) G)
      ((Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) : ℝ) /
        Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) t := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t)
  have hs : HasDerivAt (fun x => ∑ g : G, truncatedRamificationOrder (R := R) G g x)
      (∑ g : G, if g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t
        then (1 : ℝ) else 0) t :=
    HasDerivAt.fun_sum (fun g _ => hasDerivAt_truncatedRamificationOrder G g ht hbreak)
  have hc : (∑ g : G, if g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t
      then (1 : ℝ) else 0) =
      Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc] at hs
  exact (hs.div_const _).sub_const 1

/-- Equality with the defining integral on nonnegative indices. -/
theorem integral_card_lower_eq_herbrandSum {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
      (Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) s) : ℝ) /
        Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) =
      herbrandSum (R := R) G t := by
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (herbrandSum (R := R) G) _ ht (Set.countable_range (fun n : ℕ => (n : ℝ) - 1))
    (continuous_herbrandSum (R := R) G).continuousOn
    (fun x hx => hasDerivAt_herbrandSum G (by linarith [hx.1.1]) (fun n hn =>
      hx.2 ⟨n, by linarith⟩))
    ((intervalIntegrable_card_lowerRamificationGroupReal (R := R) G 0 t).div_const _)
  simpa only [herbrandSum_zero, sub_zero] using h

omit [Finite G] in
theorem truncatedRamificationOrder_of_nonpos (g : G) {t : ℝ} (ht : -1 ≤ t)
    (ht' : t ≤ 0) :
    truncatedRamificationOrder (R := R) G g t =
      (t + 1) * truncatedRamificationOrder (R := R) G g 0 := by
  rcases eq_or_ne (ramificationOrder (R := R) G g) ⊤ with hg | hg
  · rw [truncatedRamificationOrder_of_order_top G hg,
      truncatedRamificationOrder_of_order_top G hg]
    rw [max_eq_left (by linarith : 0 ≤ t + 1)]
    norm_num
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    simp only [truncatedRamificationOrder_of_order_nat G hn.symm]
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      rw [max_eq_left (by linarith : 0 ≤ t + 1), min_eq_right (by linarith : t + 1 ≤ n)]
      norm_num [min_eq_right hn1]

theorem herbrandSum_of_nonpos {t : ℝ} (ht : -1 ≤ t) (ht' : t ≤ 0) :
    herbrandSum (R := R) G t = t := by
  let := Fintype.ofFinite G
  have hs : (∑ g : G, truncatedRamificationOrder (R := R) G g t) =
      (t + 1) * ∑ g : G, truncatedRamificationOrder (R := R) G g 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g _ => truncatedRamificationOrder_of_nonpos G g ht ht')
  rw [herbrandSum, hs, sum_truncatedRamificationOrder_zero]
  have he : (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

/-- The finite sum is proved equal to the integral on its entire domain. -/
theorem herbrandFunction_eq_sum {t : ℝ} (ht : -1 ≤ t) :
    herbrandFunction (R := R) G t = herbrandSum (R := R) G t := by
  by_cases ht0 : t ≤ 0
  · rw [herbrandFunction, ite_eq_left ht0, herbrandSum_of_nonpos G ht ht0]
  · rw [herbrandFunction, ite_eq_right ht0]
    exact integral_card_lower_eq_herbrandSum G (by linarith)

theorem continuousOn_herbrandFunction :
    ContinuousOn (herbrandFunction (R := R) G) (Set.Ici (-1)) :=
  (continuous_herbrandSum (R := R) G).continuousOn.congr
    (fun _ ht => herbrandFunction_eq_sum G ht)

/-- The integral-defined Herbrand function has the cardinality-ratio derivative. -/
theorem hasDerivAt_herbrandFunction {t : ℝ} (ht : -1 < t)
    (hbreak : ∀ n : ℕ, t + 1 ≠ n) :
    HasDerivAt (herbrandFunction (R := R) G)
      ((Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) : ℝ) /
        Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) t := by
  apply (hasDerivAt_herbrandSum G ht hbreak).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact herbrandFunction_eq_sum G hs.le

end FontaineWintenberger

namespace FontaineWintenberger

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

theorem strictMonoOn_herbrandSum :
    StrictMonoOn (herbrandSum (R := R) G) (Set.Ici (-1)) := by
  let := Fintype.ofFinite G
  intro s hs t ht hst
  have hsum : (∑ g : G, truncatedRamificationOrder (R := R) G g s) <
      ∑ g : G, truncatedRamificationOrder (R := R) G g t := by
    apply Finset.sum_lt_sum
    · exact fun g _ => monotone_truncatedRamificationOrder G g hst.le
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      rw [truncatedRamificationOrder_one G s hs, truncatedRamificationOrder_one G t ht]
      linarith
  have he : (0 : ℝ) < Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) :=
    Nat.cast_pos.mpr Nat.card_pos
  exact sub_lt_sub_right ((div_lt_div_iff_of_pos_right he).mpr hsum) 1

theorem strictMonoOn_herbrandFunction :
    StrictMonoOn (herbrandFunction (R := R) G) (Set.Ici (-1)) := by
  intro s hs t ht hst
  rw [herbrandFunction_eq_sum G hs, herbrandFunction_eq_sum G ht]
  exact strictMonoOn_herbrandSum G hs ht hst

omit [Finite G] in
@[simp]
theorem herbrandFunction_neg_one : herbrandFunction (R := R) G (-1) = -1 := by
  norm_num [herbrandFunction]

theorem herbrandFunction_mem_Ici {t : ℝ} (ht : -1 ≤ t) :
    -1 ≤ herbrandFunction (R := R) G t := by
  have h := (strictMonoOn_herbrandFunction (R := R) G).monotoneOn (by simp) ht ht
  simpa only [herbrandFunction_neg_one] using h

/-- The identity summand gives a linear lower bound with a positive finite denominator. -/
theorem herbrandFunction_lower_bound {t : ℝ} (ht : -1 ≤ t) :
    (t + 1) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) - 1 ≤
      herbrandFunction (R := R) G t := by
  let := Fintype.ofFinite G
  rw [herbrandFunction_eq_sum G ht]
  have hsum : t + 1 ≤ ∑ g : G, truncatedRamificationOrder (R := R) G g t := by
    simpa only [truncatedRamificationOrder_one G t ht] using
      (Finset.single_le_sum
        (fun g _ => truncatedRamificationOrder_nonneg (R := R) G g t)
        (Finset.mem_univ (1 : G)))
  have he : (0 : ℝ) < Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) :=
    Nat.cast_pos.mpr Nat.card_pos
  exact sub_le_sub_right ((div_le_div_iff_of_pos_right he).mpr hsum) 1

theorem surjOn_herbrandFunction :
    Set.SurjOn (herbrandFunction (R := R) G) (Set.Ici (-1)) (Set.Ici (-1)) := by
  intro u hu
  change -1 ≤ u at hu
  let e : ℝ := Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)
  have he : 0 < e := Nat.cast_pos.mpr Nat.card_pos
  let T := e * (u + 1) - 1
  have hT : -1 ≤ T := by dsimp [T]; nlinarith
  have hbound : u ≤ herbrandFunction (R := R) G T := by
    have h := herbrandFunction_lower_bound (R := R) G hT
    have hid : (T + 1) / e - 1 = u := by dsimp [T]; field_simp; ring
    exact hid ▸ h
  have hc := (continuousOn_herbrandFunction (R := R) G).mono
    (show Set.Icc (-1) T ⊆ Set.Ici (-1) from fun _ hx => hx.1)
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc hT hc
    ⟨by simpa only [herbrandFunction_neg_one] using hu, hbound⟩
  exact ⟨t, ht.1, htu⟩

/-- The Herbrand integral induces an order isomorphism of the half-line. -/
noncomputable def herbrandOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) where
  toEquiv := Equiv.ofBijective
    (fun t => ⟨herbrandFunction (R := R) G t, herbrandFunction_mem_Ici G t.property⟩)
    ⟨fun s t h => Subtype.ext
      ((strictMonoOn_herbrandFunction (R := R) G).injOn s.property t.property
        (congrArg Subtype.val h)), fun u => by
      obtain ⟨t, ht, htu⟩ := surjOn_herbrandFunction (R := R) G u.property
      exact ⟨⟨t, ht⟩, Subtype.ext htu⟩⟩
  map_rel_iff' := by
    intro s t
    exact (strictMonoOn_herbrandFunction (R := R) G).le_iff_le s.property t.property

@[simp]
theorem herbrandOrderIso_apply (t : Set.Ici (-1 : ℝ)) :
    (herbrandOrderIso (R := R) G t : ℝ) = herbrandFunction (R := R) G t := rfl

/-- Inverse Herbrand function; outside the domain the argument is clamped to `-1`. -/
noncomputable def inverseHerbrandFunction (u : ℝ) : ℝ :=
  ((herbrandOrderIso (R := R) G).symm ⟨max u (-1), le_max_right _ _⟩ : ℝ)

theorem herbrandFunction_inverseHerbrandFunction {u : ℝ} (hu : -1 ≤ u) :
    herbrandFunction (R := R) G (inverseHerbrandFunction (R := R) G u) = u := by
  have h := congrArg Subtype.val ((herbrandOrderIso (R := R) G).apply_symm_apply ⟨u, hu⟩)
  simpa only [inverseHerbrandFunction, max_eq_left hu, herbrandOrderIso_apply] using h

theorem inverseHerbrandFunction_herbrandFunction {t : ℝ} (ht : -1 ≤ t) :
    inverseHerbrandFunction (R := R) G (herbrandFunction (R := R) G t) = t := by
  have h := congrArg Subtype.val ((herbrandOrderIso (R := R) G).symm_apply_apply ⟨t, ht⟩)
  change ((herbrandOrderIso (R := R) G).symm
    ⟨herbrandFunction (R := R) G t, herbrandFunction_mem_Ici G ht⟩ : ℝ) = t at h
  simpa only [inverseHerbrandFunction, max_eq_left (herbrandFunction_mem_Ici G ht),
    herbrandOrderIso_apply] using h

theorem continuous_inverseHerbrandFunction :
    Continuous (inverseHerbrandFunction (R := R) G) :=
  continuous_subtype_val.comp ((herbrandOrderIso (R := R) G).symm.toHomeomorph.continuous.comp
    ((continuous_id.max continuous_const).subtype_mk (fun _ => le_max_right _ _)))

theorem strictMonoOn_inverseHerbrandFunction :
    StrictMonoOn (inverseHerbrandFunction (R := R) G) (Set.Ici (-1)) := by
  intro s hs t ht hst
  have h := (herbrandOrderIso (R := R) G).symm.strictMono
    (show (⟨s, hs⟩ : Set.Ici (-1 : ℝ)) < ⟨t, ht⟩ from hst)
  change ((herbrandOrderIso (R := R) G).symm ⟨s, hs⟩ : ℝ) <
    ((herbrandOrderIso (R := R) G).symm ⟨t, ht⟩ : ℝ) at h
  simpa only [inverseHerbrandFunction, max_eq_left hs, max_eq_left ht] using h

theorem inverseHerbrandFunction_mem_Ici (u : ℝ) :
    -1 ≤ inverseHerbrandFunction (R := R) G u :=
  ((herbrandOrderIso (R := R) G).symm ⟨max u (-1), le_max_right _ _⟩).property

omit [Finite G] in
theorem herbrandFunction_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    herbrandFunction (R := R) G t = t := by rw [herbrandFunction, ite_eq_left ht]

theorem inverseHerbrandFunction_of_nonpos {u : ℝ} (hu : -1 ≤ u) (hu' : u ≤ 0) :
    inverseHerbrandFunction (R := R) G u = u := by
  have h := inverseHerbrandFunction_herbrandFunction (R := R) G hu
  simpa only [herbrandFunction_of_nonpos G hu'] using h

end FontaineWintenberger
