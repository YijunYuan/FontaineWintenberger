/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Lower ramification groups

## Integer lower ramification groups

The nonnegative lower group is the inertia subgroup of the corresponding
power of the maximal ideal. Integer indices at most `-1` give the full group.
The construction first applies to a ring action and an ideal; it then specializes
to the canonical action on a valuation subring by its decomposition subgroup.

This implements the integer part of Serre, *Local Fields*, Chapter IV, §1.

## Lower groups and normalized integral valuations

For a discrete valuation ring, ideal-power membership agrees with a lower
bound on mathlib's canonical normalized additive valuation `addVal`.

## Real lower numbering

The real lower groups are the existing ideal-inertia groups at the integer
ceiling. Their valuation bound uses the same intrinsic order, including
infinity and negative indices.

## The normalized field valuation of a discrete valuation subring

We use mathlib's canonical adic valuation of the maximal ideal. Its valuation
ring is the intrinsic valuation subring. The lower groups therefore
agree with the normalized valuation bounds on the ambient field.

## Main definitions

* `lowerRamificationGroup`: The integer lower group attached to an ideal.
* `ramificationOrder`: Serre's unshifted order: the infimum of the valuations of all integral
  displacements.
* `lowerRamificationGroupReal`: Real lower numbering, extending canonical integer ideal-inertia
  groups by ceilings.

## Main results

* `inertia_normal`: An invariant ideal has normal inertia.
* `lowerRamificationGroup_normal`: Lower groups are normal when the ambient action preserves the
  ideal.
* `smul_maximalIdeal`: Every ring automorphism preserves the unique maximal ideal of a local ring.
* `lowerRamificationGroup_zero_eq_ker_residue`: The zero lower group is exactly the kernel of the
  residue-field action.
* `mem_maximalIdeal_pow_iff_addVal`: A power of the maximal ideal is a closed ball for the
  normalized additive valuation, including at zero and at exponent zero.
* `addVal_smul`: Ring automorphisms preserve the canonical normalized integral valuation.
* `mem_lowerRamificationGroup_iff_addVal`: The ideal-inertia definition is the normalized valuation
  definition.
* `mem_lowerRamificationGroup_nat_iff_addVal`: Natural lower indices have the source's unshifted
  valuation bound `n + 1`.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- The integer lower group attached to an ideal. For `n ≥ 0` its elements
act trivially modulo `I ^ (n + 1)`; for `n ≤ -1` it is the full group.
When the ambient action preserves `I`, it is the kernel of the quotient action. -/
def lowerRamificationGroup (I : Ideal R) (n : ℤ) : Subgroup G :=
  (I ^ (n + 1).toNat).inertia G

theorem mem_lowerRamificationGroup_iff (I : Ideal R) (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G I n ↔ ∀ x : R, g • x - x ∈ I ^ (n + 1).toNat :=
  Ideal.mem_inertia

@[simp]
theorem lowerRamificationGroup_neg_one (I : Ideal R) :
    lowerRamificationGroup G I (-1) = ⊤ := by
  simp [lowerRamificationGroup]

theorem lowerRamificationGroup_of_le_neg_one (I : Ideal R) {n : ℤ} (hn : n ≤ -1) :
    lowerRamificationGroup G I n = ⊤ := by
  have h : (n + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  simp [lowerRamificationGroup, h]

@[simp]
theorem lowerRamificationGroup_zero (I : Ideal R) :
    lowerRamificationGroup G I 0 = I.inertia G := by
  simp [lowerRamificationGroup]

theorem lowerRamificationGroup_nat (I : Ideal R) (n : ℕ) :
    lowerRamificationGroup G I n = (I ^ (n + 1)).inertia G := by
  simp [lowerRamificationGroup]

theorem lowerRamificationGroup_antitone (I : Ideal R) :
    Antitone (lowerRamificationGroup G I) := by
  intro m n hmn
  apply AddSubgroup.inertia_mono
  exact I.pow_le_pow_right (Int.toNat_le_toNat (by omega))

@[simp]
theorem lowerRamificationGroup_subgroupOf (I : Ideal R) (n : ℤ) (H : Subgroup G) :
    (lowerRamificationGroup G I n).subgroupOf H = lowerRamificationGroup H I n :=
  rfl

theorem lowerRamificationGroup_map_subtype (I : Ideal R) (n : ℤ) (H : Subgroup G) :
    (lowerRamificationGroup H I n).map H.subtype = lowerRamificationGroup G I n ⊓ H :=
  AddSubgroup.inertia_map_subtype _ H

/-- An invariant ideal has normal inertia. -/
theorem inertia_normal (I : Ideal R) (hI : ∀ g : G, g • I = I) :
    (I.inertia G).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  rw [← Ideal.inertia_smul, hI]

/-- Lower groups are normal when the ambient action preserves the ideal. -/
theorem lowerRamificationGroup_normal (I : Ideal R) (hI : ∀ g : G, g • I = I) (n : ℤ) :
    (lowerRamificationGroup G I n).Normal := by
  apply inertia_normal
  intro g
  change (I ^ (n + 1).toNat).map (MulSemiringAction.toRingHom G R g) = _
  rw [Ideal.map_pow, ← Ideal.pointwise_smul_def, hI]

section LocalRing

variable [IsLocalRing R]

/-- Every ring automorphism preserves the unique maximal ideal of a local ring. -/
theorem smul_maximalIdeal (g : G) :
    g • IsLocalRing.maximalIdeal R = IsLocalRing.maximalIdeal R := by
  exact IsLocalRing.map_maximalIdeal_of_surjective (MulSemiringAction.toRingAut G R g).toRingHom
    (MulSemiringAction.toRingAut G R g).surjective

instance maximalIdeal_lowerRamificationGroup_normal (n : ℤ) :
    (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n).Normal :=
  lowerRamificationGroup_normal G _ (smul_maximalIdeal G) n

/-- The zero lower group is exactly the kernel of the residue-field action. -/
theorem lowerRamificationGroup_zero_eq_ker_residue :
    lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0 =
      (MulSemiringAction.toRingAut G (IsLocalRing.ResidueField R)).ker := by
  ext g
  rw [lowerRamificationGroup_zero, Ideal.mem_inertia, MonoidHom.mem_ker]
  constructor
  · intro hg
    ext a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    change g • IsLocalRing.residue R x = IsLocalRing.residue R x
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hg x)
  · intro hg x
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, IsLocalRing.ResidueField.residue_smul]
    have h := congrArg (fun e : RingAut (IsLocalRing.ResidueField R) =>
      e (IsLocalRing.residue R x)) hg
    exact sub_eq_zero.mpr h

end LocalRing

end FontaineWintenberger

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- Fix the primitive scalar action to the intrinsic decomposition action, even
when the full automorphism group also acts on the valuation ring. -/
instance decompositionSubgroupSMul (A : ValuationSubring L) :
    SMul (A.decompositionSubgroup K) A :=
  (ValuationSubring.decompositionSubgroupMulSemiringAction K A).toSMul

attribute [instance 1100] decompositionSubgroupSMul

/-- The decomposition subgroup acts faithfully on its valuation subring:
every field element or its inverse belongs to the subring. -/
instance decompositionSubgroup_faithfulSMul (A : ValuationSubring L) :
    FaithfulSMul (A.decompositionSubgroup K) A where
  eq_of_smul_eq_smul {g h} he := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rcases A.mem_or_inv_mem x with hx | hx
    · exact congrArg Subtype.val (he ⟨x, hx⟩)
    · have hi := congrArg Subtype.val (he ⟨x⁻¹, hx⟩)
      change (g : L ≃ₐ[K] L) (x⁻¹) = (h : L ≃ₐ[K] L) (x⁻¹) at hi
      simpa only [map_inv₀, inv_inj] using hi

/-- Lower ramification groups for the intrinsic action of the decomposition
subgroup on a valuation subring. -/
def lowerRamificationGroup (A : ValuationSubring L) (n : ℤ) :
    Subgroup (A.decompositionSubgroup K) :=
  FontaineWintenberger.lowerRamificationGroup (A.decompositionSubgroup K)
    (IsLocalRing.maximalIdeal A) n

theorem mem_lowerRamificationGroup_iff (A : ValuationSubring L) (n : ℤ)
    (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔
      ∀ x : A, g • x - x ∈ IsLocalRing.maximalIdeal A ^ (n + 1).toNat :=
  Iff.rfl

@[simp]
theorem lowerRamificationGroup_neg_one (A : ValuationSubring L) :
    A.lowerRamificationGroup K (-1) = ⊤ :=
  FontaineWintenberger.lowerRamificationGroup_neg_one _ _

@[simp]
theorem lowerRamificationGroup_zero (A : ValuationSubring L) :
    A.lowerRamificationGroup K 0 = A.inertiaSubgroup K :=
  FontaineWintenberger.lowerRamificationGroup_zero_eq_ker_residue _

theorem lowerRamificationGroup_antitone (A : ValuationSubring L) :
    Antitone (A.lowerRamificationGroup K) :=
  FontaineWintenberger.lowerRamificationGroup_antitone _ _

instance lowerRamificationGroup_normal (A : ValuationSubring L) (n : ℤ) :
    (A.lowerRamificationGroup K n).Normal :=
  FontaineWintenberger.maximalIdeal_lowerRamificationGroup_normal _ n

end ValuationSubring

namespace FontaineWintenberger

open IsDiscreteValuationRing hiding maximalIdeal
open IsLocalRing
open scoped Pointwise

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A power of the maximal ideal is a closed ball for the normalized additive
valuation, including at zero and at exponent zero. -/
theorem mem_maximalIdeal_pow_iff_addVal (x : R) (n : ℕ) :
    x ∈ maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R x := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hπ.addVal_pow]

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- Ring automorphisms preserve the canonical normalized integral valuation. -/
@[simp]
theorem addVal_smul (g : G) (x : R) : addVal R (g • x) = addVal R x := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← mem_maximalIdeal_pow_iff_addVal, ← mem_maximalIdeal_pow_iff_addVal]
  have h : g • (maximalIdeal R ^ n) = maximalIdeal R ^ n := by
    change (maximalIdeal R ^ n).map (MulSemiringAction.toRingHom G R g) = _
    rw [Ideal.map_pow, ← Ideal.pointwise_smul_def, smul_maximalIdeal]
  simpa only [h] using
    (Ideal.smul_mem_pointwise_smul_iff (a := g) (S := maximalIdeal R ^ n) (x := x))

/-- The ideal-inertia definition is the normalized valuation definition. -/
theorem mem_lowerRamificationGroup_iff_addVal (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ∀ x : R, ((n + 1).toNat : ℕ∞) ≤ addVal R (g • x - x) := by
  simp only [mem_lowerRamificationGroup_iff, mem_maximalIdeal_pow_iff_addVal]

/-- Natural lower indices have the source's unshifted valuation bound `n + 1`. -/
theorem mem_lowerRamificationGroup_nat_iff_addVal (n : ℕ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ∀ x : R, (n + 1 : ℕ∞) ≤ addVal R (g • x - x) := by
  simpa using mem_lowerRamificationGroup_iff_addVal G (n : ℤ) g

/-- Serre's unshifted order: the infimum of the valuations of all integral
displacements. This uses the intrinsic ring, rather than a chosen generator. -/
noncomputable def ramificationOrder (g : G) : ℕ∞ :=
  ⨅ x : R, addVal R (g • x - x)

theorem ramificationOrder_le (g : G) (x : R) :
    ramificationOrder (R := R) G g ≤ addVal R (g • x - x) :=
  iInf_le _ x

theorem mem_lowerRamificationGroup_iff_le_order (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ((n + 1).toNat : ℕ∞) ≤ ramificationOrder (R := R) G g := by
  rw [mem_lowerRamificationGroup_iff_addVal, ramificationOrder, le_iInf_iff]

@[simp]
theorem ramificationOrder_one : ramificationOrder (R := R) G 1 = ⊤ := by
  simp [ramificationOrder]

@[simp]
theorem ramificationOrder_inv (g : G) :
    ramificationOrder (R := R) G g⁻¹ = ramificationOrder (R := R) G g := by
  apply iInf_congr
  intro x
  rw [← addVal_smul G g (g⁻¹ • x - x), smul_sub, smul_inv_smul,
    ← neg_sub (g • x) x, AddValuation.map_neg]

theorem ramificationOrder_le_conj (r g : G) :
    ramificationOrder (R := R) G g ≤ ramificationOrder (R := R) G (r * g * r⁻¹) := by
  apply le_iInf
  intro x
  have h : (r * g * r⁻¹) • x - x = r • (g • (r⁻¹ • x) - r⁻¹ • x) := by
    simp [smul_sub, mul_smul]
  rw [h, addVal_smul]
  exact ramificationOrder_le G g _

@[simp]
theorem ramificationOrder_conj (r g : G) :
    ramificationOrder (R := R) G (r * g * r⁻¹) = ramificationOrder (R := R) G g := by
  apply le_antisymm
  · simpa [mul_assoc] using ramificationOrder_le_conj (R := R) G r⁻¹ (r * g * r⁻¹)
  · exact ramificationOrder_le_conj G r g

theorem min_order_le_order_mul (g h : G) :
    min (ramificationOrder (R := R) G g) (ramificationOrder (R := R) G h) ≤
      ramificationOrder (R := R) G (g * h) := by
  apply le_iInf
  intro x
  have he : (g * h) • x - x = (g • (h • x) - h • x) + (h • x - x) := by
    simp [mul_smul]
  rw [he]
  exact (min_le_min (ramificationOrder_le G g (h • x)) (ramificationOrder_le G h x)).trans
    (addVal_add (R := R))

theorem ramificationOrder_mul_of_ne (g h : G)
    (hne : ramificationOrder (R := R) G g ≠ ramificationOrder (R := R) G h) :
    ramificationOrder (R := R) G (g * h) =
      min (ramificationOrder (R := R) G g) (ramificationOrder (R := R) G h) := by
  have h₁ := min_order_le_order_mul (R := R) G g h
  have h₂ := min_order_le_order_mul (R := R) G (g * h) h⁻¹
  have h₃ := min_order_le_order_mul (R := R) G g⁻¹ (g * h)
  simp only [ramificationOrder_inv, mul_inv_cancel_right, inv_mul_cancel_left] at h₂ h₃
  rcases lt_or_gt_of_ne hne with hlt | hlt <;> order

theorem ramificationOrder_eq_top_iff [FaithfulSMul G R] (g : G) :
    ramificationOrder (R := R) G g = ⊤ ↔ g = 1 := by
  constructor
  · intro hg
    apply FaithfulSMul.eq_of_smul_eq_smul (α := R)
    intro x
    have hv : addVal R (g • x - x) = ⊤ :=
      top_le_iff.mp (hg ▸ ramificationOrder_le G g x)
    simpa only [sub_eq_zero, one_smul] using addVal_eq_top_iff.mp hv
  · rintro rfl
    exact ramificationOrder_one G

/-- A finite faithful action has eventually trivial lower groups. -/
theorem lowerRamificationGroup_eventually_eq_bot [Finite G] [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lowerRamificationGroup G (maximalIdeal R) n = ⊥ := by
  classical
  let := Fintype.ofFinite G
  let N := Finset.univ.sup (fun g : G => (ramificationOrder (R := R) G g).toNat)
  refine ⟨N, fun n hn => ?_⟩
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  by_contra hne
  have hfinite : ramificationOrder (R := R) G g ≠ ⊤ :=
    (ramificationOrder_eq_top_iff G g).not.mpr hne
  have hbound : (ramificationOrder (R := R) G g).toNat ≤ N :=
    Finset.le_sup (f := fun g : G => (ramificationOrder (R := R) G g).toNat) (Finset.mem_univ g)
  have hmem := (mem_lowerRamificationGroup_iff_le_order G (n : ℤ) g).mp hg
  have : (n + 1 : ℕ∞) ≤ (ramificationOrder (R := R) G g).toNat := by
    simpa [ENat.natCast_toNat hfinite] using hmem
  have : n + 1 ≤ (ramificationOrder (R := R) G g).toNat := by exact_mod_cast this
  omega

end FontaineWintenberger

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]

/-- Intrinsic unshifted integral order for the decomposition-group action. -/
noncomputable def ramificationOrder (g : A.decompositionSubgroup K) : ℕ∞ :=
  FontaineWintenberger.ramificationOrder (R := A) (A.decompositionSubgroup K) g

theorem mem_lowerRamificationGroup_iff_addVal (n : ℤ) (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔
      ∀ x : A, ((n + 1).toNat : ℕ∞) ≤ IsDiscreteValuationRing.addVal A (g • x - x) :=
  FontaineWintenberger.mem_lowerRamificationGroup_iff_addVal _ n g

theorem mem_lowerRamificationGroup_iff_le_order (n : ℤ) (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔ ((n + 1).toNat : ℕ∞) ≤ A.ramificationOrder K g :=
  FontaineWintenberger.mem_lowerRamificationGroup_iff_le_order _ n g

@[simp]
theorem ramificationOrder_eq_top_iff (g : A.decompositionSubgroup K) :
    A.ramificationOrder K g = ⊤ ↔ g = 1 :=
  FontaineWintenberger.ramificationOrder_eq_top_iff _ g

theorem lowerRamificationGroup_eventually_eq_bot [Finite (L ≃ₐ[K] L)] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A.lowerRamificationGroup K n = ⊥ :=
  FontaineWintenberger.lowerRamificationGroup_eventually_eq_bot _

end ValuationSubring

namespace FontaineWintenberger

open scoped ENNReal

variable (G : Type*) {R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- Real lower numbering, extending canonical integer ideal-inertia groups by ceilings. -/
noncomputable def lowerRamificationGroupReal (I : Ideal R) (t : ℝ) : Subgroup G :=
  lowerRamificationGroup G I ⌈t⌉

@[simp]
theorem lowerRamificationGroupReal_intCast (I : Ideal R) (n : ℤ) :
    lowerRamificationGroupReal G I (n : ℝ) = lowerRamificationGroup G I n := by
  simp [lowerRamificationGroupReal]

theorem lowerRamificationGroupReal_antitone (I : Ideal R) :
    Antitone (lowerRamificationGroupReal G I) :=
  (lowerRamificationGroup_antitone G I).comp_monotone Int.ceil_mono

theorem lowerRamificationGroupReal_of_le_neg_one (I : Ideal R) {t : ℝ} (ht : t ≤ -1) :
    lowerRamificationGroupReal G I t = ⊤ :=
  lowerRamificationGroup_of_le_neg_one G I (Int.ceil_le.mpr (by simpa using ht))

@[simp]
theorem lowerRamificationGroupReal_zero (I : Ideal R) :
    lowerRamificationGroupReal G I 0 = I.inertia G := by
  simp [lowerRamificationGroupReal]

@[simp]
theorem lowerRamificationGroupReal_subgroupOf (I : Ideal R) (t : ℝ) (H : Subgroup G) :
    (lowerRamificationGroupReal G I t).subgroupOf H = lowerRamificationGroupReal H I t := rfl

theorem lowerRamificationGroupReal_map_subtype (I : Ideal R) (t : ℝ) (H : Subgroup G) :
    (lowerRamificationGroupReal H I t).map H.subtype = lowerRamificationGroupReal G I t ⊓ H :=
  lowerRamificationGroup_map_subtype G I ⌈t⌉ H

instance maximalIdeal_lowerRamificationGroupReal_normal [IsLocalRing R] (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).Normal :=
  maximalIdeal_lowerRamificationGroup_normal G ⌈t⌉

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- The ceiling bound is exactly the source's real displacement-order bound. -/
theorem mem_lowerRamificationGroupReal_iff_le_order (t : ℝ) (g : G) :
    g ∈ lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t ↔
      ENNReal.ofReal (t + 1) ≤ (ramificationOrder (R := R) G g : ℝ≥0∞) := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_le_order]
  generalize ramificationOrder (R := R) G g = j
  cases j using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.toENNReal_coe, ENat.natCast_le_natCast, ENNReal.ofReal_le_natCast]
    rw [Int.toNat_le]
    constructor
    · intro h
      have hc : ⌈t⌉ ≤ (n : ℤ) - 1 := by omega
      have hr := Int.ceil_le.mp hc
      push_cast at hr
      linarith
    · intro h
      have hc : ⌈t⌉ ≤ (n : ℤ) - 1 := Int.ceil_le.mpr (by push_cast; linarith)
      omega

/-- Finite faithful actions are eventually trivial also in real lower numbering. -/
theorem lowerRamificationGroupReal_eventually_eq_bot [Finite G] [FaithfulSMul G R] :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t = ⊥ := by
  obtain ⟨N, hN⟩ := lowerRamificationGroup_eventually_eq_bot (R := R) G
  refine ⟨N, fun t ht => ?_⟩
  have hceil : (N : ℤ) ≤ ⌈t⌉ := by exact_mod_cast ht.trans (Int.le_ceil t)
  have hnonneg : 0 ≤ ⌈t⌉ := (Int.natCast_nonneg N).trans hceil
  have h := hN ⌈t⌉.toNat (by omega)
  simpa only [lowerRamificationGroupReal, Int.toNat_of_nonneg hnonneg] using h

end FontaineWintenberger

namespace FontaineWintenberger

open IsDiscreteValuationRing

variable {R E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field E] [Algebra R E] [IsFractionRing R E]

/-- Ideal powers agree with the canonical normalized valuation on the field
of fractions, including at zero. -/
theorem mem_maximalIdeal_pow_iff_valuation (x : R) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔
      (maximalIdeal R).valuation E (algebraMap R E x) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact ((maximalIdeal R).intValuation_le_pow_iff_mem x n).symm

end FontaineWintenberger

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

local notation "w" => IsDedekindDomain.HeightOneSpectrum.valuation L
  (IsDiscreteValuationRing.maximalIdeal A)

/-- The canonical normalized field valuation has the valuation ring. -/
theorem normalizedValuation_valuationSubring : (w).valuationSubring = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    change (a : L) = x at ha
    exact ha ▸ a.property
  · intro hx
    exact (IsDiscreteValuationRing.maximalIdeal A).valuation_le_one (⟨x, hx⟩ : A)

theorem mem_maximalIdeal_pow_iff_normalizedValuation (x : A) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal A ^ n ↔ w (x : L) ≤ WithZero.exp (-(n : ℤ)) :=
  FontaineWintenberger.mem_maximalIdeal_pow_iff_valuation x n

variable (K : Type*) [Field K] [Algebra K L]

/-- On integral elements, invariance of the normalized field valuation follows
from invariance of the canonical integral valuation. -/
theorem normalizedValuation_coe_smul (g : A.decompositionSubgroup K) (x : A) :
    w ((g • x : A) : L) = w (x : L) := by
  change w (algebraMap A L (g • x)) = w (algebraMap A L x)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.intValuation_maximalIdeal, FontaineWintenberger.addVal_smul]

/-- Every decomposition-group element preserves the normalized field valuation. -/
theorem normalizedValuation_apply (g : A.decompositionSubgroup K) (x : L) :
    w ((g : L ≃ₐ[K] L) x) = w x := by
  rcases A.mem_or_inv_mem x with hx | hx
  · exact normalizedValuation_coe_smul A K g ⟨x, hx⟩
  · have h := normalizedValuation_coe_smul A K g ⟨x⁻¹, hx⟩
    change w ((g : L ≃ₐ[K] L) (x⁻¹)) = w (x⁻¹) at h
    simpa only [map_inv₀, inv_inj] using h

/-- Lower groups defined through ideal inertia agree with the normalized
valuation bounds on the ambient field. -/
theorem mem_lowerRamificationGroup_iff_normalizedValuation (n : ℤ)
    (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔
      ∀ x : A, w ((g : L ≃ₐ[K] L) (x : L) - (x : L)) ≤
        WithZero.exp (-((n + 1).toNat : ℤ)) := by
  rw [mem_lowerRamificationGroup_iff]
  exact forall_congr' fun x => mem_maximalIdeal_pow_iff_normalizedValuation A (g • x - x) _

end ValuationSubring
