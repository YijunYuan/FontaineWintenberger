/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Right jumps of monotone natural-valued functions

A monotone natural-valued function that is locally constant from the left has a discrete
sequence of positive right jumps. If the function is unbounded, this sequence is infinite,
tends to infinity, and partitions the positive half-line into intervals on which the
function is constant. The jump itself belongs to the interval on its left.
-/

@[expose] public section

open Filter

/-- A right jump is a point whose value is strictly less than the value at every later point. -/
def IsRightJump (f : ℝ → ℕ) (b : ℝ) : Prop := ∀ v : ℝ, b < v → f b < f v

namespace MonotoneOn

variable {f : ℝ → ℕ}
variable (hf : MonotoneOn f (Set.Ioi 0))

include hf in
/-- A bounded interval contains only finitely many positive right jumps of a monotone
natural-valued function. -/
theorem finite_setOf_rightJump_le (U : ℝ) :
    {u : ℝ | 0 < u ∧ IsRightJump f u ∧ u ≤ U}.Finite := by
  have hm : Set.MapsTo f {u : ℝ | 0 < u ∧ IsRightJump f u ∧ u ≤ U}
      (Set.Iic (f (max U 1))) := by
    intro u hu
    exact hf hu.1 (lt_of_lt_of_le zero_lt_one (le_max_right U 1))
      (hu.2.2.trans (le_max_left U 1))
  have hi : Set.InjOn f {u : ℝ | 0 < u ∧ IsRightJump f u ∧ u ≤ U} := by
    intro u hu v hv heq
    rcases lt_trichotomy u v with h | h | h
    · exact False.elim ((hu.2.1 v h).ne heq)
    · exact h
    · exact False.elim ((hv.2.1 u h).ne heq.symm)
  exact Set.Finite.of_injOn hm hi (Set.finite_Iic _)

variable (hleft : ∀ u : ℝ, 0 < u →
  ∃ v : ℝ, 0 < v ∧ v < u ∧ ∀ x ∈ Set.Ioc v u, f x = f u)

include hf hleft in
/-- An increase between two positive parameters is witnessed by a right jump between them.
The function retains its initial value at this jump. -/
theorem exists_rightJump_between {u w : ℝ} (hu : 0 < u) (hw : 0 < w)
    (huw : f u < f w) :
    ∃ b : ℝ, u ≤ b ∧ b < w ∧ IsRightJump f b ∧ f b = f u := by
  let s : Set ℝ := {v | u ≤ v ∧ f v = f u}
  have hs : s.Nonempty := ⟨u, le_rfl, rfl⟩
  have hbounded : BddAbove s := by
    refine ⟨w, fun v hv ↦ ?_⟩
    by_contra! hwv
    have hle := hf hw (hu.trans_le hv.1) hwv.le
    rw [hv.2] at hle
    exact (not_le_of_gt huw) hle
  let b := sSup s
  have hub : u ≤ b := le_csSup hbounded ⟨le_rfl, rfl⟩
  have hb : 0 < b := hu.trans_le hub
  obtain ⟨v, _, hvb, hv⟩ := hleft b hb
  obtain ⟨x, hx, hvx⟩ := exists_lt_of_lt_csSup hs hvb
  have hfb : f b = f u := (hv x ⟨hvx, le_csSup hbounded hx⟩).symm.trans hx.2
  have hbw : b < w := by
    by_contra! hwb
    have hle := hf hw hb hwb
    rw [hfb] at hle
    exact (not_le_of_gt huw) hle
  refine ⟨b, hub, hbw, fun v hbv ↦ ?_, hfb⟩
  refine lt_of_le_of_ne (hf hb (hb.trans hbv) hbv.le) ?_
  intro heq
  exact (not_le_of_gt hbv) (le_csSup hbounded
    (show v ∈ s from ⟨hub.trans hbv.le, heq.symm.trans hfb⟩))

include hf hleft in
/-- The absence of right jumps on a half-open interval forces its endpoint values to agree. -/
theorem eq_of_not_rightJump {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (h : ∀ b ∈ Set.Ico u v, ¬IsRightJump f b) : f u = f v := by
  apply (hf hu (hu.trans_le huv) huv).eq_of_not_lt
  intro hlt
  obtain ⟨b, hub, hbv, hb, _⟩ := hf.exists_rightJump_between hleft hu (hu.trans_le huv) hlt
  exact h b ⟨hub, hbv⟩ hb

variable (hunbounded : ∀ n : ℕ, ∃ u : ℝ, 0 < u ∧ n < f u)

include hf hleft hunbounded

/-- Each positive point lies on a plateau ending in a right jump. -/
theorem exists_rightJump_ge {u : ℝ} (hu : 0 < u) :
    ∃ b : ℝ, u ≤ b ∧ IsRightJump f b ∧ f b = f u := by
  obtain ⟨w, hw, huw⟩ := hunbounded (f u)
  obtain ⟨b, hub, _, hb, hfb⟩ := hf.exists_rightJump_between hleft hu hw huw
  exact ⟨b, hub, hb, hfb⟩

/-- The positive right jumps admit an exhaustive increasing enumeration. Their successive
intervals are the maximal constant intervals of the function on the positive half-line. -/
theorem exists_strictMono_rightJumps :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ n, 0 < b n) ∧ Tendsto b atTop atTop ∧
      (∀ u : ℝ, 0 < u → (IsRightJump f u ↔ u ∈ Set.range b)) ∧
      (∀ n u, b n < u → u ≤ b (n + 1) → f u = f (b (n + 1))) ∧
      (∀ u, 0 < u → u ≤ b 0 → f u = f (b 0)) := by
  classical
  let J := {u : ℝ // 0 < u ∧ IsRightJump f u}
  let g : J → ℕ := fun u ↦ f u
  have hg : StrictMono g := fun u v huv ↦ u.property.2 v huv
  have hinfinite : (Set.range g).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨u, hu, hnu⟩ := hunbounded n
    obtain ⟨b, hub, hb, hfb⟩ := hf.exists_rightJump_ge hleft hunbounded hu
    refine ⟨g ⟨b, hu.trans_le hub, hb⟩, ⟨⟨b, hu.trans_le hub, hb⟩, rfl⟩, ?_⟩
    simpa only [g, hfb] using hnu
  let := hinfinite.to_subtype
  let e : ℕ ≃o J := (Nat.Subtype.orderIsoOfNat (Set.range g)).trans (hg.orderIso g).symm
  let b : ℕ → ℝ := fun n ↦ e n
  have hb : StrictMono b := fun m n hmn ↦ e.strictMono hmn
  have hbpos (n : ℕ) : 0 < b n := (e n).property.1
  have hbj (n : ℕ) : IsRightJump f (b n) := (e n).property.2
  have hexhaust (u : ℝ) (hu : 0 < u) : IsRightJump f u ↔ u ∈ Set.range b := by
    constructor
    · intro hj
      obtain ⟨n, hn⟩ := e.surjective ⟨u, hu, hj⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    · rintro ⟨n, rfl⟩
      exact hbj n
  have hfb : StrictMono (fun n ↦ f (b n)) := fun m n hmn ↦ hbj m _ (hb hmn)
  have htop : Tendsto b atTop atTop := by
    apply hb.monotone.tendsto_atTop_atTop
    intro u
    let v := max u 1
    let n := f v + 1
    refine ⟨n, ?_⟩
    by_contra! hnu
    have hv : 0 < v := lt_of_lt_of_le zero_lt_one (le_max_right u 1)
    have hle := hf (hbpos n) hv (hnu.le.trans (le_max_left u 1))
    have hge := hfb.id_le n
    dsimp [n] at hle hge
    omega
  refine ⟨b, hb, hbpos, htop, hexhaust, ?_, ?_⟩
  · intro n u hnu hun
    apply hf.eq_of_not_rightJump hleft ((hbpos n).trans hnu) hun
    rintro c ⟨huc, hcn⟩ hc
    obtain ⟨m, rfl⟩ := (hexhaust c (((hbpos n).trans hnu).trans_le huc)).mp hc
    have hnm : n < m := hb.lt_iff_lt.mp (hnu.trans_le huc)
    have hmn : m < n + 1 := hb.lt_iff_lt.mp hcn
    omega
  · intro u hu hub
    apply hf.eq_of_not_rightJump hleft hu hub
    rintro c ⟨huc, hc0⟩ hc
    obtain ⟨m, rfl⟩ := (hexhaust c (hu.trans_le huc)).mp hc
    exact (hb.monotone (Nat.zero_le m)).not_gt hc0

end MonotoneOn
