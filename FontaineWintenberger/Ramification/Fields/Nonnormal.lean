/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Fields.Tame
public import FontaineWintenberger.Ramification.Herbrand.Subgroup
public import FontaineWintenberger.Ramification.Lower.Tower
public import FontaineWintenberger.Mathlib.GroupTheory.Index
public import FontaineWintenberger.Mathlib.FieldTheory.RelIndex
public import Mathlib.FieldTheory.LinearDisjoint

/-!
# Inertia indices for nonnormal subextensions

The relative inertia cardinality and ramification-index tower give
the ramification index of any fixed field, without normality of its fixing
subgroup. Coprimality then supplies the wild compositum reduction.

## Main results

* `fixedField_ramificationIdx_eq_relIndex`: The ramification index of any fixed field is its
  inertia-relative fixing-group index.
* `fixedField_sup_inertia_eq_top`: Total ramification of the nonnormal fixed field makes inertia
  transitive on its embeddings.
* `fixedField_ramificationIdx_eq_finrank_iff`: Total ramification of the fixed field is exactly
  transitivity of the inertia action, without a normality hypothesis.
* `fixedField_sup_wild_eq_top`: Wild inertia is transitive on the embeddings of a totally ramified
  p-power-degree fixed field, including nonnormal fixed fields.
* `fixedField_wild_linearDisjoint`: The tame fixed field is linearly disjoint from every totally
  ramified p-power-degree fixed field.
* `fixedField_wild_compositum_finrank`: The compositum over the tame fixed field retains the full
  degree of the nonnormal wild field.
* `fixedField_wild_norm_baseChange`: The norm from the tame compositum is the norm under the base
  inclusion.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
-/

@[expose] public section

namespace FontaineWintenberger

private theorem relIndex_eq_index_of_sup_eq_top
    {G : Type*} [Group G] [Finite G] (H D : Subgroup G) [D.Normal]
    (hHD : H ⊔ D = ⊤) : H.relIndex D = H.index := by
  have hD : D.relIndex H = D.index := by
    rw [← Subgroup.relIndex_sup_right H D, hHD, Subgroup.relIndex_top_right]
  have h : H.relIndex D * D.index = D.relIndex H * H.index := by
    rw [← Subgroup.index_inf, inf_comm, Subgroup.index_inf]
  rw [hD, mul_comm (H.relIndex D)] at h
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero
    (inferInstance : D.FiniteIndex).index_ne_zero) h

private theorem sup_eq_top_of_relIndex_eq_index
    {G : Type*} [Group G] [Finite G] (H D : Subgroup G) [D.Normal]
    (hHD : H.relIndex D = H.index) : H ⊔ D = ⊤ := by
  have h : H.relIndex D * D.index = D.relIndex H * H.index := by
    rw [← Subgroup.index_inf, inf_comm, Subgroup.index_inf]
  rw [hHD, mul_comm H.index] at h
  have hD : D.index = D.relIndex H :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero
      (inferInstance : H.FiniteIndex).index_ne_zero) h
  have hi := Subgroup.relIndex_mul_index (show D ≤ H ⊔ D from le_sup_right)
  rw [Subgroup.relIndex_sup_right, ← hD] at hi
  apply Subgroup.index_eq_one.mp
  apply Nat.mul_left_cancel (Nat.pos_of_ne_zero
    (inferInstance : D.FiniteIndex).index_ne_zero)
  simpa only [mul_one] using hi

private theorem sup_eq_top_of_coprime_inertia_index
    {G : Type*} [Group G] [Finite G] (H D P : Subgroup G) [D.Normal]
    (hHD : H ⊔ D = ⊤) (hPD : P ≤ D)
    (hc : Nat.Coprime H.index (P.relIndex D)) : H ⊔ P = ⊤ := by
  have hND : (H ⊔ P) ⊔ D = ⊤ := by
    rw [sup_assoc, sup_eq_right.mpr hPD, hHD]
  have hi := relIndex_eq_index_of_sup_eq_top (H ⊔ P) D hND
  have hd : (H ⊔ P).index ∣ P.relIndex D := by
    rw [← hi]
    exact Subgroup.relIndex_dvd_of_le_left D (show P ≤ H ⊔ P from le_sup_right)
  exact Subgroup.index_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hc
      (Subgroup.index_dvd_of_le (show H ≤ H ⊔ P from le_sup_left)) hd)

private theorem norm_compositum_of_linearDisjoint
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A B : IntermediateField K L) (h : A.LinearDisjoint B) (x : B) :
    Algebra.norm A
      (⟨(x : L), (show B ≤ A ⊔ B from le_sup_right) x.property⟩ :
        IntermediateField.extendScalars (show A ≤ A ⊔ B from le_sup_left)) =
      algebraMap K A (Algebra.norm K x) := by
  let C := A ⊔ B
  let A' : IntermediateField K C := A.restrict le_sup_left
  let B' : IntermediateField K C := B.restrict le_sup_right
  let a : A ≃ₐ[K] A' := IntermediateField.restrictAlgEquiv le_sup_left
  let b : B ≃ₐ[K] B' := IntermediateField.restrictAlgEquiv le_sup_right
  have hd : A'.LinearDisjoint B' := h.algEquiv_of_isAlgebraic A' B' a b (Or.inl inferInstance)
  have ht : A' ⊔ B' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_sup,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict,
      IntermediateField.lift_top]
  let : Algebra A C := (IntermediateField.inclusion (show A ≤ C from
      le_sup_left)).toRingHom.toAlgebra
  have hn := hd.norm_algebraMap ht (b x)
  rw [Algebra.norm_eq_of_algEquiv b] at hn
  apply a.injective
  change a.toRingEquiv (Algebra.norm A
    (IntermediateField.inclusion (show B ≤ C from le_sup_right) x)) = _
  rw [Algebra.norm_eq_of_ringEquiv a.toRingEquiv (by ext z; rfl)]
  exact hn

section Fields

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField 𝓀[K]]

local notation "G" => L ≃ₐ[K] L
local notation "B" => spectralIntegerRing K L
local notation "D" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0

/-- The ramification index of any fixed field is its
inertia-relative fixing-group index. The subgroup need not be normal. -/
theorem fixedField_ramificationIdx_eq_relIndex (H : Subgroup G) :
    (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
      H.relIndex D := by
  let A := ((spectralValuation K L).comap
    (algebraMap (IntermediateField.fixedField H) L)).valuationSubring
  let := intermediate_spectral_isDiscreteValuationRing K L (IntermediateField.fixedField H)
  have ht := local_ramificationIdx_tower 𝒪[K] A B
  rw [← spectralIntegerRing_card_lower_zero K L, ← fixedField_card_inertia K L H,
    card_lowerRamificationGroup_zero_subgroup] at ht
  apply Nat.mul_right_cancel (Nat.card_pos (α := ↥(H ⊓ D)))
  exact ht.symm.trans (H.relIndex_mul_card D).symm

/-- Total ramification of the nonnormal fixed field makes inertia
transitive on its embeddings. -/
theorem fixedField_sup_inertia_eq_top (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H)) : H ⊔ D = ⊤ := by
  apply sup_eq_top_of_relIndex_eq_index H D
  rw [← fixedField_ramificationIdx_eq_relIndex K L H, he,
    IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField]

/-- Total ramification of the fixed field is exactly transitivity
of the inertia action, without a normality hypothesis. -/
theorem fixedField_ramificationIdx_eq_finrank_iff (H : Subgroup G) :
    (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H) ↔ H ⊔ D = ⊤ := by
  rw [fixedField_ramificationIdx_eq_relIndex K L H,
    IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField]
  exact ⟨sup_eq_top_of_relIndex_eq_index H D, relIndex_eq_index_of_sup_eq_top H D⟩

local notation "P" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 1

/-- Wild inertia is transitive on the embeddings of a totally
ramified p-power-degree fixed field, including nonnormal fixed fields. -/
theorem fixedField_sup_wild_eq_top (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n) :
    H ⊔ P = ⊤ := by
  apply sup_eq_top_of_coprime_inertia_index H D P
    (fixedField_sup_inertia_eq_top K L H he)
    (lowerRamificationGroup_antitone G (IsLocalRing.maximalIdeal B) (by norm_num : (0 : ℤ) ≤ 1))
  have hdegree : H.index = p ^ n := by
    rw [← IntermediateField.fixingSubgroup_fixedField H,
      ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact hd
  rw [hdegree, ← wild_fixedField_ramificationIdx_eq_relIndex K L]
  exact (wild_fixedField_ramificationIdx_coprime K L p).pow_left n

/-- The tame fixed field is linearly disjoint from every
totally ramified p-power-degree fixed field. -/
theorem fixedField_wild_linearDisjoint (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n) :
    (IntermediateField.fixedField P).LinearDisjoint (IntermediateField.fixedField H) := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  apply le_antisymm ?_ bot_le
  intro x hx
  apply (IsGalois.mem_bot_iff_fixed x).mpr
  have hp : P ≤ MulAction.stabilizer G x := by
    intro g hg
    exact (IntermediateField.mem_fixedField_iff P x).mp hx.1 g hg
  have hh : H ≤ MulAction.stabilizer G x := by
    intro g hg
    exact (IntermediateField.mem_fixedField_iff H x).mp hx.2 g hg
  have ht : (⊤ : Subgroup G) ≤ MulAction.stabilizer G x := by
    rw [← fixedField_sup_wild_eq_top K L p H he n hd]
    exact sup_le hh hp
  exact fun g => ht (Subgroup.mem_top g)

/-- The compositum over the tame fixed field retains the full degree
of the nonnormal wild field. -/
theorem fixedField_wild_compositum_finrank (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n) :
    Module.finrank (IntermediateField.fixedField P)
      (IntermediateField.extendScalars
        (show IntermediateField.fixedField P ≤
          IntermediateField.fixedField P ⊔ IntermediateField.fixedField H from le_sup_left)) =
      Module.finrank K (IntermediateField.fixedField H) := by
  rw [← fixingSubgroup_relIndex_eq_finrank K,
    IntermediateField.fixingSubgroup_sup,
    IntermediateField.fixingSubgroup_fixedField, IntermediateField.fixingSubgroup_fixedField,
    Subgroup.inf_relIndex_left,
    relIndex_eq_index_of_sup_eq_top H P (fixedField_sup_wild_eq_top K L p H he n hd),
    IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField]

/-- The norm from the tame compositum is the norm
under the base inclusion. This consumes linear disjointness. -/
theorem fixedField_wild_norm_baseChange (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p] (H : Subgroup G)
    (he : (IsLocalRing.maximalIdeal
      ((spectralValuation K L).comap
        (algebraMap (IntermediateField.fixedField H) L)).valuationSubring).ramificationIdx 𝒪[K] =
          Module.finrank K (IntermediateField.fixedField H))
    (n : ℕ) (hd : Module.finrank K (IntermediateField.fixedField H) = p ^ n)
    (x : IntermediateField.fixedField H) :
    Algebra.norm (IntermediateField.fixedField P)
      (⟨(x : L), (show IntermediateField.fixedField H ≤
        IntermediateField.fixedField P ⊔ IntermediateField.fixedField H from le_sup_right)
            x.property⟩ :
          IntermediateField.extendScalars
            (show IntermediateField.fixedField P ≤
              IntermediateField.fixedField P ⊔ IntermediateField.fixedField H from le_sup_left)) =
      algebraMap K (IntermediateField.fixedField P) (Algebra.norm K x) :=
  norm_compositum_of_linearDisjoint _ _ (fixedField_wild_linearDisjoint K L p H he n hd) x

end Fields

end FontaineWintenberger
