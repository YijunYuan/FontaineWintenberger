module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Integer lower ramification groups

The nonnegative lower group is the inertia subgroup of the corresponding
power of the maximal ideal. Integer indices at most `-1` give the full group.
The construction first applies to a ring action and an ideal; it then specializes
to the canonical action on a valuation subring by its decomposition subgroup.

This implements the integer part of Serre, *Local Fields*, Chapter IV, §1.
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
