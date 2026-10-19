/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.Ramification.Fields.Tame
public import FontaineWintenberger.Mathlib.FieldTheory.RelIndex
public import Mathlib.FieldTheory.Relrank

/-!
# Wild tails of separable APF extensions

A finite APF stage supplies a tail of the finite intermediate fields
whose residue maps are surjective and whose degrees are powers of
the residue characteristic. No normality of the infinite extension or its
finite intermediate fields is assumed.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FiniteGroups

variable {G : Type*} [Group G] [Finite G]

/-- The coset index in a product with a normal subgroup is its
intersection index inside that subgroup; the other factor need not be normal. -/
theorem relIndex_sup_eq_relIndex_of_normal_right (A U : Subgroup G) [U.Normal] :
    A.relIndex (A ⊔ U) = A.relIndex U := by
  have h₁ := Subgroup.relIndex_inf_mul_relIndex A U (A ⊔ U)
  have h₂ := Subgroup.relIndex_inf_mul_relIndex U A (A ⊔ U)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right] at h₁
  rw [inf_eq_left.mpr le_sup_left, inf_comm] at h₂
  have hn : U.relIndex A ≠ 0 := by
    change (U.subgroupOf A).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  exact mul_left_cancel₀ hn (h₂.trans (h₁.symm.trans (Nat.mul_comm _ _)))

/-- Every intermediate index in a finite normal p-group product
is a power of p, without normality of the three intervening subgroups. -/
theorem relIndex_eq_prime_pow_of_le_sup
    (q : ℕ) [Fact q.Prime] (A B C U : Subgroup G) [U.Normal]
    (hU : IsPGroup q U) (hAB : A ≤ B) (hBC : B ≤ C) (hCU : C ≤ A ⊔ U) :
    ∃ n : ℕ, B.relIndex C = q ^ n := by
  have hd₁ : B.relIndex C ∣ A.relIndex C := by
    rw [← Subgroup.relIndex_mul_relIndex A B C hAB hBC]
    exact ⟨A.relIndex B, by ring⟩
  have hd₂ : A.relIndex C ∣ A.relIndex (A ⊔ U) := by
    rw [← Subgroup.relIndex_mul_relIndex A C (A ⊔ U) (hAB.trans hBC) hCU]
    exact ⟨C.relIndex (A ⊔ U), rfl⟩
  have hd₃ : A.relIndex (A ⊔ U) ∣ Nat.card U := by
    rw [relIndex_sup_eq_relIndex_of_normal_right]
    exact Subgroup.relIndex_dvd_card A U
  have hd := hd₁.trans (hd₂.trans hd₃)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU
  rw [hm] at hd
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp hd
  exact ⟨n, hn⟩

end FiniteGroups

section SeparableModel

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K

/-- Above the upper-one stage, every finite subextension
step has p-power degree. The larger field and the infinite extension may
both be nonnormal over the base. -/
theorem finrank_eq_prime_pow_of_apfFiniteStage_one_le
    (L E F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (hFL : F ≤ L) (hEF : E ≤ F) (hstage : apfFiniteStage K L 1 ≤ E) :
    ∃ n : ℕ, Module.finrank E (IntermediateField.extendScalars hEF) = p ^ n := by
  let Ω := finiteGaloisNormalClosure K F
  let M := E.comap Ω.toIntermediateField.val
  let N := F.comap Ω.toIntermediateField.val
  have hFΩ : F ≤ Ω.toIntermediateField := le_finiteGaloisNormalClosure K F
  have hEΩ : E ≤ Ω.toIntermediateField := hEF.trans hFΩ
  have hM : M.map Ω.toIntermediateField.val = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hEΩ hx⟩, hx, rfl⟩
  have hN : N.map Ω.toIntermediateField.val = F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hFΩ hx⟩, hx, rfl⟩
  let ρ : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* (Ω ≃ₐ[K] Ω) :=
    AlgEquiv.restrictNormalHom Ω
  let A := L.fixingSubgroup.map ρ
  let B := N.fixingSubgroup
  let C := M.fixingSubgroup
  let U := upperRamificationGroup (R := spectralIntegerRing K Ω) (Ω ≃ₐ[K] Ω) 1
  have hρ : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Ω) (SeparableClosure K)
  have hfixE : E.fixingSubgroup = C.comap ρ := by
    rw [← hM]
    exact IntermediateField.map_fixingSubgroup (F := K) (E := Ω)
      (E' := SeparableClosure K) (L := M)
  have hfixF : F.fixingSubgroup = B.comap ρ := by
    rw [← hN]
    exact IntermediateField.map_fixingSubgroup (F := K) (E := Ω)
      (E' := SeparableClosure K) (L := N)
  have hmapE : E.fixingSubgroup.map ρ = C := by
    rw [hfixE, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hρ, top_inf_eq]
  have hmapF : F.fixingSubgroup.map ρ = B := by
    rw [hfixF, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hρ, top_inf_eq]
  have hAB : A ≤ B := by
    rw [← hmapF]
    exact Subgroup.map_mono (IntermediateField.fixingSubgroup_le hFL)
  have hBC : B ≤ C :=
    IntermediateField.fixingSubgroup_le (show M ≤ N from fun _ hx => hEF hx)
  have hCU : C ≤ A ⊔ U := by
    have hfix : E.fixingSubgroup ≤ apfSubgroup K L 1 :=
      (IntermediateField.fixingSubgroup_le hstage).trans_eq
        (fixingSubgroup_apfFiniteStage K L 1)
    have h := Subgroup.map_mono (f := ρ) hfix
    rw [hmapE] at h
    change C ≤ (L.fixingSubgroup ⊔ absoluteUpperRamificationGroup K 1).map ρ at h
    rw [Subgroup.map_sup, absolute_map_upperRamificationGroup K Ω 1 (by norm_num)] at h
    exact h
  have hU : IsPGroup p U := by
    let : CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p :=
      charP_of_injective_algebraMap
        (algebraMap 𝓀[K]
          (IsLocalRing.ResidueField (spectralIntegerRing K Ω))).injective p
    exact (lowerRamificationGroup_one_isPGroup (Ω ≃ₐ[K] Ω) p).to_le
      (upperRamificationGroup_le_lower_one (Ω ≃ₐ[K] Ω) (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn⟩ := relIndex_eq_prime_pow_of_le_sup p A B C U hU hAB hBC hCU
  refine ⟨n, ?_⟩
  rw [← fixingSubgroup_relIndex_eq_finrank K E F hEF, hfixF,
    Subgroup.relIndex_comap, hmapE]
  exact hn

end SeparableModel

section AbstractExtension

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Surjectivity of the residue inclusion makes the finite
step totally ramified, using its spectral integer-ring map. -/
theorem FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (hs : Function.Surjective
      (spectralResidueInclusion K (IntermediateField.inclusion hEF))) :
    letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
    (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
        (spectralIntegerRing K E.val) =
      Module.finrank E.val (IntermediateField.extendScalars hEF) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite
      𝒪[K] _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have hf : Module.finrank (IsLocalRing.ResidueField (spectralIntegerRing K E.val))
      (IsLocalRing.ResidueField (spectralIntegerRing K F.val)) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(spectralResidueInclusion K (IntermediateField.inclusion hEF)).injective, hs⟩
  have h := local_ramificationIdx_mul_residueDegree_eq_finrank
    (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) E.val F.val
  rw [hf, mul_one] at h
  exact h

/-- A finite intermediate field in the abstract APF extension gives
surjective residue maps and p-power degrees on every finite step
above it, including nonnormal steps. -/
theorem IsAPF.exists_finiteIntermediateField_residue_surjective_and_degree_prime_pow
    [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, T ≤ E → ∀ hEF : E ≤ F,
      Function.Surjective
          (spectralResidueInclusion K (IntermediateField.inclusion hEF)) ∧
        ∃ n : ℕ, Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ n := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨T₁, hT₁⟩ := exists_finiteIntermediateField_map_eq_apfFiniteStage K L j
    (by norm_num : -1 ≤ (1 : ℝ))
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_finiteIntermediateField_residueInclusion_surjective K L
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E F hE hEF ↦
    ⟨hT₀ E F ((FiniteIntermediateField.le_sup_left T₀ T₁).trans hE) hEF, ?_⟩⟩
  have : FiniteDimensional K (F.val.map j) :=
    Module.Finite.equiv (IntermediateField.equivMap F.val j).toLinearEquiv
  have hFL : F.val.map j ≤ j.fieldRange := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have hmap : E.val.map j ≤ F.val.map j := IntermediateField.map_mono j hEF
  have hstage : apfFiniteStage K j.fieldRange 1 ≤ E.val.map j := by
    rw [← hT₁]
    exact IntermediateField.map_mono j ((FiniteIntermediateField.le_sup_right T₀ T₁).trans hE)
  obtain ⟨n, hn⟩ := finrank_eq_prime_pow_of_apfFiniteStage_one_le K
    j.fieldRange (E.val.map j) (F.val.map j) hFL hmap hstage
  refine ⟨n, ?_⟩
  rw [← IntermediateField.relfinrank_eq_finrank_of_le hmap,
    IntermediateField.relfinrank_map_map,
    IntermediateField.relfinrank_eq_finrank_of_le hEF] at hn
  exact hn

/-- Every separable APF extension has a finite wild tail:
all residue inclusions are onto, all degrees are powers of the
residue characteristic, and every step is totally ramified on its
spectral integer rings. -/
theorem IsAPF.exists_finiteIntermediateField_wild_tail [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, T ≤ E → ∀ hEF : E ≤ F,
      Function.Surjective
          (spectralResidueInclusion K (IntermediateField.inclusion hEF)) ∧
        (∃ n : ℕ, Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ n) ∧
        letI : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
        letI : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
        letI := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
        (IsLocalRing.maximalIdeal (spectralIntegerRing K F.val)).ramificationIdx
            (spectralIntegerRing K E.val) =
          Module.finrank E.val (IntermediateField.extendScalars hEF) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_residue_surjective_and_degree_prime_pow K L
  refine ⟨T, fun E F hE hEF ↦ ?_⟩
  obtain ⟨hs, hn⟩ := hT E F hE hEF
  exact ⟨hs, hn, FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective
      K L
    E F hEF hs⟩

end AbstractExtension

end FontaineWintenberger
