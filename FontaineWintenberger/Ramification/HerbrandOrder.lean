/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Herbrand

/-!
# The Herbrand order isomorphism and its inverse

The actual integral-defined function is strictly increasing and onto its
source half-line. Its inverse is obtained from this proved order isomorphism.
-/

@[expose] public section

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

/-- The actual Herbrand integral induces an order isomorphism of the source half-line. -/
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

/-- Inverse Herbrand function; outside the source domain the argument is clamped to `-1`. -/
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
