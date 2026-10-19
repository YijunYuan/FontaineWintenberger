/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Different.Hilbert
public import FontaineWintenberger.Ramification.Herbrand.Subgroup
public import FontaineWintenberger.Ramification.Herbrand.Affine
public import FontaineWintenberger.Ramification.Lower.Tower
public import FontaineWintenberger.Ramification.Lower.FixedField

/-!
# The different and upper orbits of arbitrary subextensions

The order of the different in a tower is additive with the canonical
ramification-index weight. Hilbert's formula and the subgroup Herbrand
identity compute the upper orbit index without assuming a normal subfield
or a totally ramified Galois closure.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped nonZeroDivisors

open IsDiscreteValuationRing

section IdealOrders

variable (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- The canonical order of a product of DVR ideals is the sum of its orders,
including the zero ideal. -/
theorem maximalIdeal_emultiplicity_mul (I J : Ideal B) :
    emultiplicity (IsLocalRing.maximalIdeal B) (I * J) =
      emultiplicity (IsLocalRing.maximalIdeal B) I + emultiplicity (IsLocalRing.maximalIdeal B) J :=
          by
  obtain ⟨x, rfl⟩ := (inferInstance : I.IsPrincipal).principal
  obtain ⟨y, rfl⟩ := (inferInstance : J.IsPrincipal).principal
  rw [Ideal.span_singleton_mul_span_singleton, maximalIdeal_emultiplicity_span,
    maximalIdeal_emultiplicity_span, maximalIdeal_emultiplicity_span, addVal_mul]

/-- A nonzero DVR ideal has finite canonical order. -/
theorem maximalIdeal_emultiplicity_ne_top {I : Ideal B} (hI : I ≠ ⊥) :
    emultiplicity (IsLocalRing.maximalIdeal B) I ≠ ⊤ := by
  obtain ⟨x, rfl⟩ := (inferInstance : I.IsPrincipal).principal
  rw [maximalIdeal_emultiplicity_span, ne_eq, addVal_eq_top_iff]
  intro hx
  exact hI (by simp [hx])

variable (C : Type*) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra B C] [FaithfulSMul B C] [IsLocalHom (algebraMap B C)]

/-- Extending a DVR ideal multiplies its canonical order by the
canonical ramification index. -/
theorem maximalIdeal_emultiplicity_map (I : Ideal B) :
    emultiplicity (IsLocalRing.maximalIdeal C) (I.map (algebraMap B C)) =
      ((IsLocalRing.maximalIdeal C).ramificationIdx B : ℕ∞) * emultiplicity
          (IsLocalRing.maximalIdeal B) I := by
  obtain ⟨x, rfl⟩ := (inferInstance : I.IsPrincipal).principal
  rw [Ideal.map_span, Set.image_singleton, maximalIdeal_emultiplicity_span,
    maximalIdeal_emultiplicity_span, addVal_algebraMap]

end IdealOrders

section DifferentTower

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C] [Module.IsTorsionFree B C]
    [FaithfulSMul B C] [IsLocalHom (algebraMap B C)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]

/-- The different-order transitivity formula, with its inertia-order
weight rather than the full relative Galois degree. -/
theorem differentIdeal_order_tower :
    emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C) =
      emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal B C) +
        ((IsLocalRing.maximalIdeal C).ramificationIdx B : ℕ∞) *
          emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (A := A) (B := B) C,
    maximalIdeal_emultiplicity_mul, maximalIdeal_emultiplicity_map]

/-- All three differents are nonzero in a finite separable tower, so
the order-transitivity equality also holds in the natural numbers. -/
theorem differentIdeal_order_toNat_tower :
    (emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C)).toNat =
      (emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal B C)).toNat +
        (IsLocalRing.maximalIdeal C).ramificationIdx B *
          (emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat := by
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (FractionRing A) (FractionRing B) (FractionRing C)
  let : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) (FractionRing B) (FractionRing C)
  have hAB := maximalIdeal_emultiplicity_ne_top B (differentIdeal_ne_bot (A := A) (B := B))
  have hBC := maximalIdeal_emultiplicity_ne_top C (differentIdeal_ne_bot (A := B) (B := C))
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hAB
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hBC
  have h := differentIdeal_order_tower A B C
  rw [← ha, ← hb, ← Nat.cast_mul, ← Nat.cast_add] at h
  have hn := congrArg ENat.toNat h
  simpa only [← ha, ← hb, ENat.toNat_natCast] using hn

end DifferentTower

section HerbrandSums

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0

/-- At an integer, the Herbrand integral is the finite sum of the
positive lower-group cardinalities divided by the inertia order. -/
theorem herbrandFunction_nat_mul_card (N : ℕ) :
    herbrandFunction (R := R) G N * (Nat.card I₀ : ℝ) =
      ∑ i ∈ Finset.range N,
        (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (i + 1)) : ℝ) := by
  have hc : (Nat.card I₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  induction N with
  | zero => simp [herbrandFunction_of_nonpos G le_rfl]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ha := herbrandFunction_affine (R := R) G N
      (t := ((N + 1 : ℕ) : ℝ)) (by simp) (by simp)
    rw [ha]
    push_cast
    field_simp
    nlinarith

variable (H : Subgroup G)

local notation "H₀" => (H ⊓ I₀ : Subgroup G)
local notation "U" => upperRamificationGroup (R := R) G

/-- Upper orbits never outnumber the embedding cosets. -/
theorem upperOrbitIndex_le_fixingIndex (u : ℝ) : (H ⊔ U u).index ≤ H.index :=
  Nat.le_of_dvd (show 0 < H.index from Nat.card_pos)
    (Subgroup.index_dvd_of_le (show H ≤ H ⊔ U u from le_sup_left))

/-- The subgroup Herbrand identity gives the finite-cutoff integral of the
inertia-relative orbit deficit, for the subgroup action. -/
theorem subgroup_upperRelIndex_deficit_integral [FaithfulSMul G R] (N : ℕ) :
    (Nat.card H₀ : ℝ) *
        (∫ u in (0 : ℝ)..(herbrandFunction (R := R) G N),
          ((Nat.card I₀ : ℝ) / Nat.card H₀ - ((H₀ ⊔ U u).relIndex I₀ : ℝ))) =
      ∑ i ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (i + 1)) : ℝ) -
          Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (i + 1))) := by
  have hN : (-1 : ℝ) ≤ (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hU : 0 ≤ herbrandFunction (R := R) G N := by
    have hm := strictMonoOn_herbrandFunction (R := R) G
    have hz := herbrandFunction_of_nonpos (R := R) G (t := 0) le_rfl
    simpa only [hz] using hm.monotoneOn (by norm_num) hN (Nat.cast_nonneg N)
  have hchange := subgroup_herbrandFunction_comp_inverse_eq_integral (R := R) G H hU
  rw [inverseHerbrandFunction_herbrandFunction G hN] at hchange
  have hq : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hG := herbrandFunction_nat_mul_card (R := R) G N
  have hH := herbrandFunction_nat_mul_card (R := R) H N
  rw [card_lowerRamificationGroup_zero_subgroup] at hH
  have hsumH : (∑ i ∈ Finset.range N,
      (Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal R) (i + 1)) : ℝ)) =
      ∑ i ∈ Finset.range N,
        (Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal R) (i + 1)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun n : ℕ => (n : ℝ)) (by
      simpa only [lowerRamificationGroupReal_intCast, Nat.cast_add, Nat.cast_one] using
        card_lowerRamificationGroupReal_subgroup (R := R) G H ((i + 1 : ℕ) : ℤ))
  rw [hsumH] at hH
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_subgroup_upperRelIndex (R := R) G H hU),
    intervalIntegral.integral_const, ← hchange, sub_zero, smul_eq_mul,
    Finset.sum_sub_distrib]
  field_simp
  nlinarith

end HerbrandSums

section UpperOrbitIndices

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [Finite G]
variable (H : Subgroup G)

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0
local notation "H₀" => (H ⊓ I₀ : Subgroup G)
local notation "U" => upperRamificationGroup (R := R) G

/-- An integer lower cutoff gives an upper cutoff through
the Herbrand function. -/
theorem upperRamificationGroup_eq_bot_of_herbrand_cutoff {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal R) N = ⊥)
    {u : ℝ} (hu : herbrandFunction (R := R) G N ≤ u) : U u = ⊥ := by
  have hN' : (-1 : ℝ) ≤ (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hφ := herbrandFunction_mem_Ici (R := R) G hN'
  have hle := upperRamificationGroup_antitoneOn (R := R) G hφ (hφ.trans hu) hu
  have he : lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) (N : ℝ) =
      lowerRamificationGroup G (IsLocalRing.maximalIdeal R) N := by
    simpa only [Int.cast_natCast] using
      lowerRamificationGroupReal_intCast G (IsLocalRing.maximalIdeal R) (N : ℤ)
  rw [upperRamificationGroup_herbrandFunction G hN', he, hN] at hle
  exact bot_unique hle

/-- The upper orbit deficit vanishes beyond every transported
integer lower cutoff. -/
theorem upperOrbitDeficit_eq_zero_of_herbrand_cutoff {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal R) N = ⊥)
    {u : ℝ} (hu : herbrandFunction (R := R) G N ≤ u) :
    (H.index : ℝ) - (H ⊔ U u).index = 0 := by
  rw [upperRamificationGroup_eq_bot_of_herbrand_cutoff G hN hu, sup_bot_eq, sub_self]

/-- The absolute orbit index increases with the upper parameter. -/
theorem upperOrbitIndex_monotoneOn :
    MonotoneOn (fun u : ℝ => (H ⊔ U u).index) (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hle := sup_le_sup_left (upperRamificationGroup_antitoneOn (R := R) G
    (by linarith [hu] : -1 ≤ u) (by linarith [hv] : -1 ≤ v) huv) H
  exact Nat.le_of_dvd (show 0 < (H ⊔ U v).index from Nat.card_pos)
    (Subgroup.index_dvd_of_le hle)

/-- The absolute upper orbit index is integrable on every nonnegative
compact interval. -/
theorem intervalIntegrable_upperOrbitIndex {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable (fun v : ℝ => ((H ⊔ U v).index : ℝ))
      MeasureTheory.volume 0 u := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hu]
  intro v hv w hw hvw
  exact Nat.cast_le.mpr (upperOrbitIndex_monotoneOn (R := R) G H hv.1 hw.1 hvw)

/-- The absolute upper orbit index is the zero orbit index times the
inertia-relative index. No normality of the fixing subgroup is required. -/
theorem upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex {u : ℝ} (hu : 0 ≤ u) :
    (H ⊔ U u).index = (H ⊔ I₀).index * (H₀ ⊔ U u).relIndex I₀ := by
  have hU : U u ≤ I₀ := by
    simpa only [upperRamificationGroup_zero, lowerRamificationGroup_zero] using
      upperRamificationGroup_antitoneOn (R := R) G
        (by norm_num : -1 ≤ (0 : ℝ)) (by linarith : -1 ≤ u) hu
  let Q : Subgroup G := H ⊔ U u
  let V : Subgroup G := H ⊔ I₀
  let P : Subgroup G := H₀ ⊔ U u
  have hQI : Q ⊓ I₀ = P := by
    apply le_antisymm
    · rintro g ⟨hgQ, hgI⟩
      obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hgQ
      have hhI : h ∈ I₀ := by
        have he := (I₀).mul_mem hgI ((I₀).inv_mem (hU hz))
        simpa only [mul_inv_cancel_right] using he
      exact P.mul_mem ((show H₀ ≤ P from le_sup_left) ⟨hh, hhI⟩)
        ((show U u ≤ P from le_sup_right) hz)
    · exact le_inf (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
        (sup_le inf_le_right hU)
  have hQV : Q ≤ V := sup_le_sup_left hU H
  have hIV : I₀ ≤ V := le_sup_right
  have hPQ : P ≤ Q := by rw [← hQI]; exact inf_le_left
  have hPI : P ≤ I₀ := by rw [← hQI]; exact inf_le_right
  have hsup : Q ⊔ I₀ = V := by
    dsimp only [Q, V]
    rw [sup_assoc, sup_eq_right.mpr hU]
  have hrel : (I₀).relIndex V = P.relIndex Q := by
    rw [← hsup, Subgroup.relIndex_sup_right, ← hQI, Subgroup.inf_relIndex_left]
  have h₁ := Subgroup.relIndex_mul_relIndex P I₀ V hPI hIV
  have h₂ := Subgroup.relIndex_mul_relIndex P Q V hPQ hQV
  rw [hrel] at h₁
  have hc : 0 < P.relIndex Q := Nat.card_pos
  have hindex : Q.relIndex V = P.relIndex I₀ := by
    apply Nat.eq_of_mul_eq_mul_left hc
    nlinarith [h₁, h₂]
  have h := Subgroup.relIndex_mul_index hQV
  rw [hindex, mul_comm] at h
  exact h.symm

/-- The total fixing index factors into its zero orbit index and the
relative inertia order. -/
theorem fixingIndex_eq_zeroIndex_mul_inertiaRatio [FaithfulSMul G R] :
    (H.index : ℝ) = (H ⊔ I₀).index * ((Nat.card I₀ : ℝ) / Nat.card H₀) := by
  obtain ⟨v, hv⟩ := upperRamificationGroup_eventually_eq_bot (R := R) G
  have h := upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex (R := R) G H
    (u := max v 0) (le_max_right _ _)
  rw [hv _ (le_max_left _ _), sup_bot_eq, sup_bot_eq] at h
  have hc := (H₀).relIndex_mul_card I₀
  rw [inf_eq_left.mpr inf_le_right] at hc
  have hratio : ((H₀).relIndex I₀ : ℝ) = (Nat.card I₀ : ℝ) / Nat.card H₀ := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr Nat.card_pos.ne')).mpr
    exact_mod_cast hc
  have hr := congrArg (fun n : ℕ => (n : ℝ)) h
  rw [Nat.cast_mul, hratio] at hr
  exact hr

/-- An arbitrary prime-index fixing subgroup with full inertia product has
one finite nonnegative upper break. The endpoint belongs to the first
interval, including when the break is zero. -/
theorem exists_prime_index_upperOrbitIndex_profile [FaithfulSMul G R]
    (hp : H.index.Prime) (hzero : H ⊔ I₀ = ⊤) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ u : ℝ, 0 ≤ u →
      (H ⊔ U u).index = if u ≤ b then 1 else H.index := by
  have hH : H ≠ ⊤ := by
    intro h
    have hi : H.index = 1 := Subgroup.index_eq_one.mpr h
    exact hp.ne_one hi
  obtain ⟨b, hb, hprofile⟩ := exists_first_upper_break_of_fixingSubgroup (R := R) G H hH hzero
  refine ⟨b, hb, fun u hu => ?_⟩
  have htop := hprofile u hu
  by_cases hub : u ≤ b
  · rw [ite_eq_left hub]
    exact Subgroup.index_eq_one.mpr (htop.mpr hub)
  · rw [ite_eq_right hub]
    rcases hp.eq_one_or_self_of_dvd (H ⊔ U u).index
      (Subgroup.index_dvd_of_le (show H ≤ H ⊔ U u from le_sup_left)) with h | h
    · exact False.elim (hub (htop.mp (Subgroup.index_eq_one.mp h)))
    · exact h

end UpperOrbitIndices

section HilbertCutoff

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C]
    [FaithfulSMul A C] [IsLocalHom (algebraMap A C)] [Module.Finite A C]
    [HenselianLocalRing C]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
variable (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G C] [IsGaloisGroup G A C]

/-- Hilbert's formula at any lower cutoff, on canonical integer rings
with their fraction fields and no chosen different-order certificate. -/
theorem differentIdeal_order_eq_sum_lower_card_of_cutoff {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C) =
      ∑ i ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) - 1 : ℕ) : ℕ∞) := by
  classical
  let := Fintype.ofFinite G
  let : FiniteDimensional (FractionRing A) (FractionRing C) :=
    .of_isLocalization A C A⁰
  obtain ⟨θ, hθ⟩ := exists_integral_generator (R := A) (S := C)
  rw [differentIdeal_order_eq_sum_ramificationOrder A C (FractionRing A) (FractionRing C) G hθ]
  apply sum_ramificationOrder_eq_sum_lower_card
  intro g hg
  have hnot : g ∉ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N := by
    simpa only [hN, Subgroup.mem_bot] using hg
  have hf : ramificationOrder (R := C) G g ≠ ⊤ := by
    intro hf
    apply hnot
    simp [mem_lowerRamificationGroup_iff_le_order, hf]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hf
  have hlt : (k : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by
    simpa [mem_lowerRamificationGroup_iff_le_order, ← hk] using hnot
  have hn : k < N + 1 := by exact_mod_cast hlt
  rw [← hk]
  exact_mod_cast (show k ≤ N by omega)

/-- The finite real Hilbert formula retains the canonical ideal order and
the lower-group cardinalities. -/
theorem differentIdeal_order_toReal_eq_sum_lower_card_of_cutoff {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    ((emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C)).toNat : ℝ) =
      ∑ i ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) - 1) := by
  classical
  let := Fintype.ofFinite G
  have h := differentIdeal_order_eq_sum_lower_card_of_cutoff A C G hN
  let S : ℕ := ∑ i ∈ Finset.range N,
    (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) - 1)
  have hs : (S : ℕ∞) = ∑ i ∈ Finset.range N,
      ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) - 1 : ℕ) : ℕ∞) := by
    exact Nat.cast_sum _ _
  rw [← hs] at h
  have hn := congrArg ENat.toNat h
  change (emultiplicity (IsLocalRing.maximalIdeal C) (differentIdeal A C)).toNat = S at hn
  rw [hn, show (S : ℝ) = ∑ i ∈ Finset.range N,
      ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) - 1 : ℕ) : ℝ)
      from Nat.cast_sum _ _]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.cast_one] using Nat.cast_sub (R := ℝ)
    (Nat.card_pos : 0 < Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i))

end HilbertCutoff

section SubextensionDifferent

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B C : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [FaithfulSMul A B] [FaithfulSMul A C] [FaithfulSMul B C]
    [IsLocalHom (algebraMap A C)]
    [IsLocalHom (algebraMap B C)] [HenselianLocalRing C]
    [PerfectField (IsLocalRing.ResidueField A)] [PerfectField (IsLocalRing.ResidueField B)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
variable (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G C] [IsGaloisGroup G A C]
variable (H : Subgroup G) [IsGaloisGroup H B C]

local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal C) 0
local notation "H₀" => (H ⊓ I₀ : Subgroup G)
local notation "U" => upperRamificationGroup (R := C) G

/-- Subtraction of the two Hilbert formulas computes the different
of an arbitrary intermediate extension. The subgroup need not be normal. -/
theorem subextension_different_order_mul_inertia_eq_lower_sum {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    (Nat.card H₀ : ℝ) *
        ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
      ∑ i ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) -
          Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i)) := by
  classical
  let := Fintype.ofFinite G
  classical
  let : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) (FractionRing B) (FractionRing C)
  have hNH : lowerRamificationGroup H (IsLocalRing.maximalIdeal C) N = ⊥ := by
    rw [← lowerRamificationGroup_subgroupOf, hN]
    simp
  have hAC := differentIdeal_order_toReal_eq_sum_lower_card_of_cutoff A C G hN
  have hBC := differentIdeal_order_toReal_eq_sum_lower_card_of_cutoff B C H hNH
  have hcard : Nat.card H₀ = (IsLocalRing.maximalIdeal C).ramificationIdx B := by
    rw [← card_lowerRamificationGroup_zero_subgroup (R := C) G H]
    let := hasSeparableResidueFieldsAt_maximalIdeal B C
    exact card_lowerRamificationGroup_zero B C H
  have ht := congrArg (fun n : ℕ => (n : ℝ)) (differentIdeal_order_toNat_tower A B C)
  push_cast at ht
  rw [← hcard] at ht
  have hcards : (∑ i ∈ Finset.range N,
      ((Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal C) i) : ℝ) - 1)) =
      ∑ i ∈ Finset.range N,
        ((Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    simpa only [lowerRamificationGroupReal_intCast] using
      card_lowerRamificationGroupReal_subgroup (R := C) G H (i : ℤ)
  rw [hcards] at hBC
  have hs : (∑ i ∈ Finset.range N,
      ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) -
        Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i))) =
      (∑ i ∈ Finset.range N,
        ((Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) - 1)) -
      ∑ i ∈ Finset.range N,
        ((Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, ← hAC, ← hBC]
  linarith

/-- The different order is the inertia-relative index deficit
integral up to any integer lower cutoff transported by the Herbrand
function. This allows an arbitrary nonnormal intermediate extension. -/
theorem subextension_different_order_eq_upperRelIndex_integral [FaithfulSMul G C]
    {N : ℕ} (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
      (Nat.card I₀ : ℝ) / Nat.card H₀ - 1 +
        ∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
          ((Nat.card I₀ : ℝ) / Nat.card H₀ - ((H₀ ⊔ U u).relIndex I₀ : ℝ)) := by
  classical
  let := Fintype.ofFinite G
  let F : ℕ → ℝ := fun i =>
    (Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i) : ℝ) -
      Nat.card ↥(H ⊓ lowerRamificationGroup G (IsLocalRing.maximalIdeal C) i)
  have hsum := subextension_different_order_mul_inertia_eq_lower_sum A B C G H hN
  have hint := subgroup_upperRelIndex_deficit_integral (R := C) G H N
  have hF : F N = 0 := by
    dsimp only [F]
    rw [hN, inf_bot_eq]
    simp
  have hshift : (∑ i ∈ Finset.range N, F (i + 1)) =
      (∑ i ∈ Finset.range N, F i) - F 0 := by
    have h₁ := Finset.sum_range_succ F N
    have h₂ := Finset.sum_range_succ' F N
    rw [hF] at h₁
    linarith
  change _ = ∑ i ∈ Finset.range N, F i at hsum
  change _ = ∑ i ∈ Finset.range N, F (i + 1) at hint
  rw [hshift, ← hsum] at hint
  have hq : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  dsimp only [F, Nat.cast_zero] at hint
  apply mul_left_cancel₀ hq
  rw [mul_add]
  have hfrac : (Nat.card H₀ : ℝ) * ((Nat.card I₀ : ℝ) / Nat.card H₀ - 1) =
      (Nat.card I₀ : ℝ) - Nat.card H₀ := by
    field_simp
  rw [hfrac]
  linarith

omit [Module.Finite A B] [FaithfulSMul A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] in
/-- The inertia-order ratio is the ramification index of the
intermediate extension, even when the full ambient extension has a residue
extension and the intermediate extension is nonnormal. -/
theorem card_inertia_div_card_subgroup_inertia :
    (Nat.card I₀ : ℝ) / Nat.card H₀ =
      ((IsLocalRing.maximalIdeal B).ramificationIdx A : ℝ) := by
  have hG : Nat.card I₀ = (IsLocalRing.maximalIdeal C).ramificationIdx A := by
    let := hasSeparableResidueFieldsAt_maximalIdeal A C
    exact card_lowerRamificationGroup_zero A C G
  have hH : Nat.card H₀ = (IsLocalRing.maximalIdeal C).ramificationIdx B := by
    rw [← card_lowerRamificationGroup_zero_subgroup (R := C) G H]
    let := hasSeparableResidueFieldsAt_maximalIdeal B C
    exact card_lowerRamificationGroup_zero B C H
  rw [hG, hH, local_ramificationIdx_tower A B C, Nat.cast_mul]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (local_ramificationIdx_pos B C).ne')

/-- The intrinsic finite-cutoff different formula, expressed entirely with
the different, canonical ramification index, and upper groups. -/
theorem subextension_different_order_eq_ramificationIdx_integral [FaithfulSMul G C]
    {N : ℕ} (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
      ((IsLocalRing.maximalIdeal B).ramificationIdx A : ℝ) - 1 +
        ∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
          (((IsLocalRing.maximalIdeal B).ramificationIdx A : ℝ) -
            ((H₀ ⊔ U u).relIndex I₀ : ℝ)) := by
  classical
  let := Fintype.ofFinite G
  simpa only [card_inertia_div_card_subgroup_inertia A B C G H] using
    subextension_different_order_eq_upperRelIndex_integral A B C G H hN

/-- The different as an integral of absolute upper orbit indices.
The zero orbit index is the residue-degree factor in a finite field
extension. No normality of the intermediate fixing subgroup is assumed. -/
theorem subextension_different_order_eq_upperOrbitIndex_integral [FaithfulSMul G C]
    {N : ℕ} (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    ((H ⊔ I₀).index : ℝ) *
        ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
      (H.index : ℝ) - (H ⊔ I₀).index +
        ∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
          ((H.index : ℝ) - (H ⊔ U u).index) := by
  classical
  let := Fintype.ofFinite G
  have hN' : (-1 : ℝ) ≤ (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hU : 0 ≤ herbrandFunction (R := C) G N := by
    have h := (strictMonoOn_herbrandFunction (R := C) G).monotoneOn
      (by norm_num : (0 : ℝ) ∈ Set.Ici (-1)) hN' (Nat.cast_nonneg N)
    simpa only [herbrandFunction_of_nonpos G le_rfl] using h
  have hn := fixingIndex_eq_zeroIndex_mul_inertiaRatio (R := C) G H
  rw [card_inertia_div_card_subgroup_inertia A B C G H] at hn
  have hd := subextension_different_order_eq_ramificationIdx_integral A B C G H hN
  have hint : (∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
      ((H.index : ℝ) - (H ⊔ U u).index)) =
      ((H ⊔ I₀).index : ℝ) *
        ∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
          (((IsLocalRing.maximalIdeal B).ramificationIdx A : ℝ) -
            ((H₀ ⊔ U u).relIndex I₀ : ℝ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hU]
    intro u hu
    have hfactor := congrArg (fun n : ℕ => (n : ℝ))
      (upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex (R := C) G H hu.1)
    rw [Nat.cast_mul] at hfactor
    dsimp only
    rw [hn, hfactor]
    ring
  rw [hint]
  nlinarith

/-- A totally ramified prime-degree subextension has one finite upper
orbit break, and its different determines that break. The subextension may be
nonnormal, and its Galois closure may have a nontrivial residue extension. -/
theorem subextension_prime_degree_different_profile [FaithfulSMul G C]
    (hp : H.index.Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx A = H.index) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → (H ⊔ U u).index = if u ≤ b then 1 else H.index) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat : ℝ) =
        ((H.index : ℝ) - 1) * (b + 1) := by
  classical
  let := Fintype.ofFinite G
  have hn := fixingIndex_eq_zeroIndex_mul_inertiaRatio (R := C) G H
  rw [card_inertia_div_card_subgroup_inertia A B C G H, he] at hn
  have hnonzero : (H.index : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hzeroIndex : (H ⊔ I₀).index = 1 := by
    have hr : ((H ⊔ I₀).index : ℝ) = 1 := by
      apply mul_right_cancel₀ hnonzero
      nlinarith [hn]
    exact_mod_cast hr
  have hzero : H ⊔ I₀ = ⊤ := Subgroup.index_eq_one.mp hzeroIndex
  obtain ⟨b, hb, hprofile⟩ := exists_prime_index_upperOrbitIndex_profile (R := C) G H hp hzero
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := C) G
  let v : ℝ := herbrandFunction (R := C) G N
  have hN' : (-1 : ℝ) ≤ (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hv : 0 ≤ v := by
    have h := (strictMonoOn_herbrandFunction (R := C) G).monotoneOn
      (by norm_num : (0 : ℝ) ∈ Set.Ici (-1)) hN' (Nat.cast_nonneg N)
    simpa only [herbrandFunction_of_nonpos G le_rfl] using h
  have hbot : U v = ⊥ :=
    upperRamificationGroup_eq_bot_of_herbrand_cutoff (R := C) G (hN N le_rfl) le_rfl
  have hbv : b < v := by
    by_contra h
    have hvb : v ≤ b := by linarith
    have h := hprofile v hv
    rw [hbot, sup_bot_eq, ite_eq_left hvb] at h
    exact hp.ne_one h
  let F : ℝ → ℝ := fun u => (H.index : ℝ) - (H ⊔ U u).index
  have hsmall : (∫ u in (0 : ℝ)..b, F u) = ((H.index : ℝ) - 1) * b := by
    calc
      _ = ∫ _ in (0 : ℝ)..b, ((H.index : ℝ) - 1) := by
        apply intervalIntegral.integral_congr_ae
        apply Filter.Eventually.of_forall
        intro u hu
        rw [Set.uIoc_of_le hb] at hu
        dsimp only [F]
        rw [hprofile u hu.1.le, ite_eq_left hu.2, Nat.cast_one]
      _ = _ := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        ring
  have hbig : (∫ u in b..v, F u) = 0 := by
    calc
      _ = ∫ _ in b..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        apply Filter.Eventually.of_forall
        intro u hu
        rw [Set.uIoc_of_le hbv.le] at hu
        dsimp only [F]
        rw [hprofile u (hb.trans hu.1.le), ite_eq_right (not_le.mpr hu.1), sub_self]
      _ = _ := by simp
  have hiSmall : IntervalIntegrable F MeasureTheory.volume 0 b :=
    intervalIntegrable_const.sub (intervalIntegrable_upperOrbitIndex (R := C) G H hb)
  have hiIndex : IntervalIntegrable (fun u : ℝ => ((H ⊔ U u).index : ℝ))
      MeasureTheory.volume b v := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hbv.le]
    intro u hu w hw huw
    exact Nat.cast_le.mpr (upperOrbitIndex_monotoneOn (R := C) G H
      (hb.trans hu.1) (hb.trans hw.1) huw)
  have hiBig : IntervalIntegrable F MeasureTheory.volume b v := intervalIntegrable_const.sub hiIndex
  have hadd := intervalIntegral.integral_add_adjacent_intervals hiSmall hiBig
  have hd := subextension_different_order_eq_upperOrbitIndex_integral A B C G H (hN N le_rfl)
  rw [hzeroIndex, Nat.cast_one, one_mul] at hd
  change _ = (H.index : ℝ) - 1 + ∫ u in (0 : ℝ)..v, F u at hd
  rw [← hadd, hsmall, hbig, add_zero] at hd
  refine ⟨b, hb, hprofile, ?_⟩
  nlinarith [hd]

end SubextensionDifferent

section Spectral

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (M : IntermediateField K L)

local notation "B" => Valuation.valuationSubring
  (Valuation.comap (algebraMap M L) (spectralValuation K L))
local notation "C" => spectralIntegerRing K L
local notation "G" => L ≃ₐ[K] L
local notation "H" => M.fixingSubgroup
local notation "I₀" => lowerRamificationGroup G (IsLocalRing.maximalIdeal C) 0
local notation "U" => upperRamificationGroup (R := C) G

/-- The integers of an arbitrary intermediate field are the
invariants of its fixing subgroup. No normality is required. -/
theorem intermediate_spectral_integer_isGaloisGroup : IsGaloisGroup H B C := by
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have : IsGaloisGroup H M L := IsGaloisGroup.intermediateField G K L M
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top 𝒪[K]
  have : SMulDistribClass H C L := {
    smul_distrib_smul := fun h x z => by
      change (h : L ≃ₐ[K] L) ((x : L) * z) = ((h • x : C) : L) * (h : L ≃ₐ[K] L) z
      exact map_mul (h : L ≃ₐ[K] L) (x : L) z }
  exact IsGaloisGroup.of_isFractionRing H B C M L

variable [PerfectField 𝓀[K]]

/-- The zero orbit index is exactly the residue-field degree of
the intermediate extension. -/
theorem intermediate_spectral_zeroOrbitIndex_eq_residueDegree :
    letI := intermediate_spectral_isDiscreteValuationRing K L M
    (H ⊔ I₀).index =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField B) := by
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have : Module.Finite B C := Module.Finite.of_restrictScalars_finite 𝒪[K] B C
  have := intermediate_spectral_integer_isGaloisGroup K L M
  have : PerfectField (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField 𝒪[K])
  have hn := fixingIndex_eq_zeroIndex_mul_inertiaRatio (R := C) G H
  rw [card_inertia_div_card_subgroup_inertia 𝒪[K] B C G H] at hn
  rw [(IntermediateField.finrank_eq_fixingSubgroup_index L M).symm] at hn
  have hd := congrArg (fun n : ℕ => (n : ℝ))
    (local_ramificationIdx_mul_residueDegree_eq_finrank 𝒪[K] B K M)
  rw [Nat.cast_mul] at hd
  have he : ((IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (local_ramificationIdx_pos 𝒪[K] B).ne'
  have hf : ((H ⊔ I₀).index : ℝ) =
      Module.finrank (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField B) := by
    apply mul_right_cancel₀ he
    nlinarith [hd, hn]
  exact_mod_cast hf

/-- The upper-orbit different formula on the intermediate integer
and residue fields, with their algebra maps. -/
theorem intermediate_spectral_different_order_eq_upperOrbitIndex_integral {N : ℕ}
    (hN : lowerRamificationGroup G (IsLocalRing.maximalIdeal C) N = ⊥) :
    letI := intermediate_spectral_isDiscreteValuationRing K L M
    ((Module.finrank (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField B) : ℝ) *
        ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ)) =
      (Module.finrank K M : ℝ) -
          Module.finrank (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField B) +
        ∫ u in (0 : ℝ)..(herbrandFunction (R := C) G N),
          ((Module.finrank K M : ℝ) - (H ⊔ U u).index) := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have : Module.Finite B C := Module.Finite.of_restrictScalars_finite 𝒪[K] B C
  have := intermediate_spectral_integer_isGaloisGroup K L M
  have : PerfectField (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField 𝒪[K])
  let : MulSemiringAction G (FractionRing C) := IsFractionRing.mulSemiringAction G C _
  let : IsGalois (FractionRing 𝒪[K]) (FractionRing C) :=
    IsGaloisGroup.isGalois G (FractionRing 𝒪[K]) (FractionRing C)
  have h := subextension_different_order_eq_upperOrbitIndex_integral 𝒪[K] B C G H hN
  simpa only [intermediate_spectral_zeroOrbitIndex_eq_residueDegree K L M,
    (IntermediateField.finrank_eq_fixingSubgroup_index L M).symm] using h

/-- A concrete prime-degree totally ramified intermediate extension has
the expected one-break profile and different formula. The finite
Galois closure may have a nontrivial residue extension. -/
theorem intermediate_spectral_prime_degree_different_profile
    (hp : (Module.finrank K M).Prime)
    (he : (IsLocalRing.maximalIdeal B).ramificationIdx 𝒪[K] = Module.finrank K M) :
    letI := intermediate_spectral_isDiscreteValuationRing K L M
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u : ℝ, 0 ≤ u → (H ⊔ U u).index = if u ≤ b then 1 else Module.finrank K M) ∧
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal 𝒪[K] B)).toNat : ℝ) =
        ((Module.finrank K M : ℝ) - 1) * (b + 1) := by
  classical
  have := intermediate_spectral_isDiscreteValuationRing K L M
  have : Module.Finite B C := Module.Finite.of_restrictScalars_finite 𝒪[K] B C
  have := intermediate_spectral_integer_isGaloisGroup K L M
  have : PerfectField (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField 𝒪[K])
  let : MulSemiringAction G (FractionRing C) := IsFractionRing.mulSemiringAction G C _
  let : IsGalois (FractionRing 𝒪[K]) (FractionRing C) :=
    IsGaloisGroup.isGalois G (FractionRing 𝒪[K]) (FractionRing C)
  have hindex : (H).index = Module.finrank K M :=
    (IntermediateField.finrank_eq_fixingSubgroup_index L M).symm
  simpa only [hindex] using subextension_prime_degree_different_profile 𝒪[K] B C G H
    (by simpa only [hindex] using hp) (by simpa only [hindex] using he)

end Spectral

end FontaineWintenberger
