/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Herbrand.Basic

/-!
# Explicit affine pieces of the Herbrand function

The slopes on integer intervals count the next lower group. Eventual
triviality gives a final affine ray, hence a finite partition for a finite
faithful action.

## Main results

* `truncatedRamificationOrder_affine`: Each capped order is affine on an integer interval, with the
  next lower-group indicator slope.
* `herbrandFunction_affine`: Explicit affine formula on every nonnegative integer interval.
* `herbrandFunction_affine_of_lower_eq_bot`: An interval of trivial lower groups has the final
  affine slope.
* `exists_herbrandFunction_affine_tail`: A finite faithful action has a final affine ray with an
  integer starting point.
* `inverseHerbrandFunction_affine`: The inverse has the reciprocal positive slope on each image
  interval.
* `exists_herbrand_affine_tails`: The same finite cutoff works for both the function and its
  inverse.
* `herbrandFunction_finite_affine_partition`: A finite family of explicit affine pieces covers the
  whole half-line.
* `inverseHerbrandFunction_finite_affine_partition`: The corresponding finitely many image intervals
  give explicit inverse affine pieces.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

open scoped ENNReal
open MeasureTheory

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R]

open scoped Classical in
/-- Each capped order is affine on an integer interval, with the next lower-group indicator
slope. -/
theorem truncatedRamificationOrder_affine (g : G) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    truncatedRamificationOrder (R := R) G g t =
      truncatedRamificationOrder (R := R) G g n + (t - n) *
        (if g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1) then 1 else 0) := by
  have hp : 0 ≤ t + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnp : 0 ≤ (n : ℝ) + 1 := by positivity
  rcases eq_or_ne (ramificationOrder (R := R) G g) ⊤ with hg | hg
  · have hm : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1) := by
      rw [mem_lowerRamificationGroup_iff_le_order, hg]
      exact le_top
    rw [truncatedRamificationOrder_of_order_top G hg,
      truncatedRamificationOrder_of_order_top G hg, max_eq_left hp, max_eq_left hnp,
      ite_eq_left hm]
    ring
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hg
    have hm : g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1) ↔
        n + 2 ≤ k := by
      rw [mem_lowerRamificationGroup_iff_le_order, ← hk]
      simp
      omega
    rw [truncatedRamificationOrder_of_order_nat G hk.symm,
      truncatedRamificationOrder_of_order_nat G hk.symm, max_eq_left hp, max_eq_left hnp]
    by_cases hnk : n + 2 ≤ k
    · have hr : (n : ℝ) + 2 ≤ k := by exact_mod_cast hnk
      rw [ite_eq_left (hm.mpr hnk), min_eq_right (by linarith : t + 1 ≤ k),
        min_eq_right (by linarith : (n : ℝ) + 1 ≤ k)]
      ring
    · have hr : (k : ℝ) ≤ n + 1 := by exact_mod_cast (show k ≤ n + 1 by omega)
      rw [ite_eq_right (fun h => hnk (hm.mp h)), min_eq_left (by linarith : (k : ℝ) ≤ t + 1),
        min_eq_left hr]
      ring

variable [Finite G]

open scoped Classical in
/-- Explicit affine formula on every nonnegative integer interval. -/
theorem herbrandFunction_affine (n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t)
    (ht' : t ≤ n + 1) :
    herbrandFunction (R := R) G t = herbrandFunction (R := R) G n +
      (t - n) * Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)) /
        Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1))
  have hc : (∑ g : G, if g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)
      then (1 : ℝ) else 0) =
      Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hs : (∑ g : G, truncatedRamificationOrder (R := R) G g t) =
      (∑ g : G, truncatedRamificationOrder (R := R) G g n) +
      (t - n) * Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)) := by
    calc
      _ = ∑ g : G, (truncatedRamificationOrder (R := R) G g n + (t - n) *
          (if g ∈ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)
            then 1 else 0)) :=
        Finset.sum_congr rfl (fun g _ => truncatedRamificationOrder_affine G g n ht ht')
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc]
  rw [herbrandFunction_eq_sum G
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)] : -1 ≤ t),
    herbrandFunction_eq_sum G
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)] : -1 ≤ (n : ℝ)),
    herbrandSum, herbrandSum, hs]
  ring

/-- An interval of trivial lower groups has the final affine slope. -/
theorem herbrandFunction_affine_of_lower_eq_bot {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b)
    (hgroups : ∀ s ∈ Set.Ioo a b,
      lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) s = ⊥) :
    herbrandFunction (R := R) G b = herbrandFunction (R := R) G a +
      (b - a) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (herbrandFunction (R := R) G)
    (fun _ => (1 : ℝ) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0))
    hab (Set.countable_range (fun n : ℕ => (n : ℝ) - 1))
    ((continuousOn_herbrandFunction (R := R) G).mono
      (show Set.Icc a b ⊆ Set.Ici (-1) from fun _ hx => ha.trans hx.1))
    (fun x hx => by
      have hd := hasDerivAt_herbrandFunction (R := R) G (t := x) (by linarith [hx.1.1])
        (fun n hn => hx.2 ⟨n, by linarith⟩)
      simpa only [hgroups x hx.1, Nat.card_unique, Nat.cast_one] using hd)
    intervalIntegrable_const
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- A finite faithful action has a final affine ray with an integer starting point. -/
theorem exists_herbrandFunction_affine_tail [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ t : ℝ, (N : ℝ) ≤ t →
      herbrandFunction (R := R) G t = herbrandFunction (R := R) G N +
        (t - N) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
  obtain ⟨T, hT⟩ := lowerRamificationGroupReal_eventually_eq_bot (R := R) G
  obtain ⟨N, hN⟩ := exists_nat_gt T
  refine ⟨N, fun t ht => herbrandFunction_affine_of_lower_eq_bot G
    (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) ht
    (fun s hs => hT s (hN.le.trans hs.1.le))⟩

/-- The inverse has the reciprocal positive slope on each image interval. -/
theorem inverseHerbrandFunction_affine (n : ℕ) {u : ℝ}
    (hu : herbrandFunction (R := R) G n ≤ u)
    (hu' : u ≤ herbrandFunction (R := R) G ((n : ℝ) + 1)) :
    inverseHerbrandFunction (R := R) G u = n +
      (u - herbrandFunction (R := R) G n) /
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)) : ℝ) /
          Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) := by
  have hn : -1 ≤ (n : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn' : -1 ≤ (n : ℝ) + 1 := by linarith
  have hu0 := (herbrandFunction_mem_Ici (R := R) G hn).trans hu
  have hψ := inverseHerbrandFunction_mem_Ici (R := R) G u
  have hinv := herbrandFunction_inverseHerbrandFunction (R := R) G hu0
  have ht : (n : ℝ) ≤ inverseHerbrandFunction (R := R) G u :=
    ((strictMonoOn_herbrandFunction (R := R) G).le_iff_le hn hψ).mp (by rwa [hinv])
  have ht' : inverseHerbrandFunction (R := R) G u ≤ (n : ℝ) + 1 :=
    ((strictMonoOn_herbrandFunction (R := R) G).le_iff_le hψ hn').mp (by rwa [hinv])
  have h := herbrandFunction_affine (R := R) G n ht ht'
  rw [hinv] at h
  have he : (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hg : (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (n + 1)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp at h ⊢
  nlinarith

/-- The same finite cutoff works for both the function and its inverse. -/
theorem exists_herbrand_affine_tails [FaithfulSMul G R] :
    ∃ N : ℕ,
      (∀ t : ℝ, (N : ℝ) ≤ t →
        herbrandFunction (R := R) G t = herbrandFunction (R := R) G N +
          (t - N) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) ∧
      (∀ u : ℝ, herbrandFunction (R := R) G N ≤ u →
        inverseHerbrandFunction (R := R) G u = N +
          (u - herbrandFunction (R := R) G N) *
            Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) := by
  obtain ⟨N, hN⟩ := exists_herbrandFunction_affine_tail (R := R) G
  refine ⟨N, hN, fun u hu => ?_⟩
  have hn : -1 ≤ (N : ℝ) := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hu0 := (herbrandFunction_mem_Ici (R := R) G hn).trans hu
  have hψ := inverseHerbrandFunction_mem_Ici (R := R) G u
  have hinv := herbrandFunction_inverseHerbrandFunction (R := R) G hu0
  have ht : (N : ℝ) ≤ inverseHerbrandFunction (R := R) G u :=
    ((strictMonoOn_herbrandFunction (R := R) G).le_iff_le hn hψ).mp (by rwa [hinv])
  have h := hN _ ht
  rw [hinv] at h
  have he : (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp at h
  nlinarith

/-- A finite family of explicit affine pieces covers the whole half-line. -/
theorem herbrandFunction_finite_affine_partition [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ t : ℝ, -1 ≤ t →
      (t ≤ 0 ∧ herbrandFunction (R := R) G t = t) ∨
      (∃ n : Fin N, (n.val : ℝ) ≤ t ∧ t ≤ (n.val : ℝ) + 1 ∧
        herbrandFunction (R := R) G t = herbrandFunction (R := R) G n.val +
          (t - n.val) * Nat.card (lowerRamificationGroup G
            (IsLocalRing.maximalIdeal R) (n.val + 1)) /
              Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) ∨
      ((N : ℝ) ≤ t ∧ herbrandFunction (R := R) G t = herbrandFunction (R := R) G N +
        (t - N) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) := by
  obtain ⟨N, hN⟩ := exists_herbrandFunction_affine_tail (R := R) G
  refine ⟨N, fun t _ => ?_⟩
  by_cases ht0 : t ≤ 0
  · exact Or.inl ⟨ht0, herbrandFunction_of_nonpos G ht0⟩
  · apply Or.inr
    by_cases htN : (N : ℝ) ≤ t
    · exact Or.inr ⟨htN, hN t htN⟩
    · have hpos : 0 ≤ t := by linarith
      have hn : ⌊t⌋₊ < N := (Nat.floor_lt hpos).mpr (lt_of_not_ge htN)
      exact Or.inl ⟨⟨⌊t⌋₊, hn⟩, Nat.floor_le hpos, (Nat.lt_floor_add_one t).le,
        herbrandFunction_affine G ⌊t⌋₊ (Nat.floor_le hpos) (Nat.lt_floor_add_one t).le⟩

/-- The corresponding finitely many image intervals give explicit inverse affine pieces. -/
theorem inverseHerbrandFunction_finite_affine_partition [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ u : ℝ, -1 ≤ u →
      (u ≤ 0 ∧ inverseHerbrandFunction (R := R) G u = u) ∨
      (∃ n : Fin N, herbrandFunction (R := R) G n.val ≤ u ∧
        u ≤ herbrandFunction (R := R) G ((n.val : ℝ) + 1) ∧
        inverseHerbrandFunction (R := R) G u = n.val +
          (u - herbrandFunction (R := R) G n.val) /
            ((Nat.card (lowerRamificationGroup G
              (IsLocalRing.maximalIdeal R) (n.val + 1)) : ℝ) /
                Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0))) ∨
      (herbrandFunction (R := R) G N ≤ u ∧
        inverseHerbrandFunction (R := R) G u = N +
          (u - herbrandFunction (R := R) G N) *
            Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) := by
  obtain ⟨N, _, hN⟩ := exists_herbrand_affine_tails (R := R) G
  refine ⟨N, fun u hu => ?_⟩
  by_cases hu0 : u ≤ 0
  · exact Or.inl ⟨hu0, inverseHerbrandFunction_of_nonpos G hu hu0⟩
  · apply Or.inr
    by_cases huN : herbrandFunction (R := R) G N ≤ u
    · exact Or.inr ⟨huN, hN u huN⟩
    · have hn : -1 ≤ (N : ℝ) := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hψ := inverseHerbrandFunction_mem_Ici (R := R) G u
      have hinv := herbrandFunction_inverseHerbrandFunction (R := R) G hu
      have ht0 : 0 < inverseHerbrandFunction (R := R) G u :=
        ((strictMonoOn_herbrandFunction (R := R) G).lt_iff_lt (by norm_num) hψ).mp
          (by rw [hinv, herbrandFunction_of_nonpos G (le_refl 0)]; exact lt_of_not_ge hu0)
      have htN : inverseHerbrandFunction (R := R) G u < N :=
        ((strictMonoOn_herbrandFunction (R := R) G).lt_iff_lt hψ hn).mp
          (by rw [hinv]; exact lt_of_not_ge huN)
      let n := ⌊inverseHerbrandFunction (R := R) G u⌋₊
      have hnN : n < N := (Nat.floor_lt ht0.le).mpr htN
      have hnle : (n : ℝ) ≤ inverseHerbrandFunction (R := R) G u := Nat.floor_le ht0.le
      have hle : inverseHerbrandFunction (R := R) G u ≤ (n : ℝ) + 1 :=
        (Nat.lt_floor_add_one _).le
      have hn0 : -1 ≤ (n : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hlo : herbrandFunction (R := R) G n ≤ u := by
        simpa only [hinv] using
          (strictMonoOn_herbrandFunction (R := R) G).monotoneOn hn0 hψ hnle
      have hhi : u ≤ herbrandFunction (R := R) G ((n : ℝ) + 1) := by
        simpa only [hinv] using
          (strictMonoOn_herbrandFunction (R := R) G).monotoneOn hψ
            (by linarith : -1 ≤ (n : ℝ) + 1) hle
      exact Or.inl ⟨⟨n, hnN⟩, hlo, hhi, inverseHerbrandFunction_affine G n hlo hhi⟩

/-- Only finitely many positive indices can fail the lower-cardinality derivative formula. -/
theorem exists_herbrandFunction_finite_derivative_breaks [FaithfulSMul G R] :
    ∃ S : Finset ℝ, ∀ t : ℝ, 0 < t → t ∉ S →
      HasDerivAt (herbrandFunction (R := R) G)
        ((Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) : ℝ) /
          Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) t := by
  obtain ⟨T, hT⟩ := lowerRamificationGroupReal_eventually_eq_bot (R := R) G
  obtain ⟨N, hN⟩ := exists_nat_gt T
  have hgroups : ∀ s : ℝ, (N : ℝ) ≤ s →
      lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) s = ⊥ :=
    fun s hs => hT s (hN.le.trans hs)
  have hn0 : -1 ≤ (N : ℝ) := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have htail : ∀ s : ℝ, (N : ℝ) ≤ s →
      herbrandFunction (R := R) G s = herbrandFunction (R := R) G N +
        (s - N) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) :=
    fun s hs => herbrandFunction_affine_of_lower_eq_bot G hn0 hs
      (fun x hx => hgroups x hx.1.le)
  refine ⟨(Finset.range (N + 2)).image (fun n : ℕ => (n : ℝ) - 1), fun t ht hnot => ?_⟩
  by_cases htN : (N : ℝ) < t
  · rw [hgroups t htN.le, Nat.card_unique, Nat.cast_one]
    have hd : HasDerivAt (fun s : ℝ => herbrandFunction (R := R) G N +
        (s - N) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0))
        ((1 : ℝ) / Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0)) t := by
      simpa using (((hasDerivAt_id t).sub_const (N : ℝ)).div_const
        (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) : ℝ)).const_add
          (herbrandFunction (R := R) G N)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds htN] with s hs
    exact htail s hs.le
  · apply hasDerivAt_herbrandFunction G (by linarith)
    intro n hn
    apply hnot
    apply Finset.mem_image.mpr
    have hlt : (n : ℝ) < ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hlt' : n < N + 2 := by exact_mod_cast hlt
    exact ⟨n, Finset.mem_range.mpr hlt', by linarith⟩

end FontaineWintenberger
