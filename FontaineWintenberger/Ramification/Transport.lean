/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Upper

/-!
# Equivariant relabelling of intrinsic ramification

Changing the acting group's presentation preserves actual displacements,
lower groups, the integral Herbrand function, its inverse and upper groups.
-/

@[expose] public section

namespace FontaineWintenberger

section ActionEquiv

variable {G G' R : Type*} [Group G] [Group G'] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [MulSemiringAction G' R]
variable (e : G ≃* G') (he : ∀ (g : G) (a : R), e g • a = g • a)

include e he

theorem ramificationOrder_mulEquiv (g : G) :
    ramificationOrder (R := R) G' (e g) = ramificationOrder (R := R) G g := by
  simp only [ramificationOrder, he]

theorem lowerRamificationGroup_map_mulEquiv (n : ℤ) :
    (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n).map e.toMonoidHom =
      lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) n := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    change e h ∈ lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) n
    rw [mem_lowerRamificationGroup_iff_le_order, ramificationOrder_mulEquiv e he]
    exact (mem_lowerRamificationGroup_iff_le_order G n h).mp hh
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [mem_lowerRamificationGroup_iff_le_order,
      ← ramificationOrder_mulEquiv e he, e.apply_symm_apply]
    exact (mem_lowerRamificationGroup_iff_le_order G' n g).mp hg

theorem lowerRamificationGroupReal_map_mulEquiv (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).map e.toMonoidHom =
      lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal R) t :=
  lowerRamificationGroup_map_mulEquiv e he _

theorem card_lowerRamificationGroupReal_mulEquiv (t : ℝ) :
    Nat.card (lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal R) t) =
      Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
  rw [← lowerRamificationGroupReal_map_mulEquiv e he t]
  exact Subgroup.card_map_of_injective e.injective

theorem herbrandFunction_mulEquiv (t : ℝ) :
    herbrandFunction (R := R) G' t = herbrandFunction (R := R) G t := by
  have hzero : Nat.card (lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) 0) =
      Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
    simpa [lowerRamificationGroupReal] using card_lowerRamificationGroupReal_mulEquiv e he 0
  simp only [herbrandFunction, hzero, card_lowerRamificationGroupReal_mulEquiv e he]

variable [Finite G] [Finite G']

theorem inverseHerbrandFunction_mulEquiv {u : ℝ} (hu : -1 ≤ u) :
    inverseHerbrandFunction (R := R) G' u = inverseHerbrandFunction (R := R) G u := by
  apply (strictMonoOn_herbrandFunction (R := R) G).injOn
    (inverseHerbrandFunction_mem_Ici G' u) (inverseHerbrandFunction_mem_Ici G u)
  rw [← herbrandFunction_mulEquiv e he, herbrandFunction_inverseHerbrandFunction G' hu,
    herbrandFunction_inverseHerbrandFunction G hu]

theorem upperRamificationGroup_map_mulEquiv {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := R) G u).map e.toMonoidHom =
      upperRamificationGroup (R := R) G' u := by
  rw [upperRamificationGroup, upperRamificationGroup,
    lowerRamificationGroupReal_map_mulEquiv e he, inverseHerbrandFunction_mulEquiv e he hu]

end ActionEquiv

section IntermediateField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (F : IntermediateField K L) [IsGalois K F]

local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀

/-- Ordinary field restriction preserves the actual restricted intermediate integer ring. -/
theorem restrictNormal_mem_intermediate_decomposition (s : L ≃ₐ[K] L) :
    s.restrictNormal F ∈ D₀ := by
  generalize hH : F.fixingSubgroup = H
  have : H.Normal := hH ▸ inferInstance
  have hF : IntermediateField.fixedField H = F := by
    rw [← hH]
    exact IsGalois.fixedField_fixingSubgroup F
  subst F
  exact restrictNormal_mem_fixedField_decomposition K L H s

noncomputable def intermediateDecompositionRestriction : (L ≃ₐ[K] L) →* D₀ :=
  (AlgEquiv.restrictNormalHom F).codRestrict _
    (restrictNormal_mem_intermediate_decomposition K L F)

variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

/-- The actual quotient theorem on an arbitrary Galois intermediate field's pullback ring. -/
theorem intermediate_map_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    (upperRamificationGroup (R := B₀) (L ≃ₐ[K] L) u).map
      (intermediateDecompositionRestriction K L F) =
        upperRamificationGroup (R := A₀) D₀ u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  generalize hH : F.fixingSubgroup = H
  have : H.Normal := hH ▸ inferInstance
  have hF : IntermediateField.fixedField H = F := by
    rw [← hH]
    exact IsGalois.fixedField_fixingSubgroup F
  subst F
  simpa only [fixedFieldDecompositionRestriction, intermediateDecompositionRestriction] using
    fixedField_map_upperRamificationGroup K L H u hu

/-- Ordinary field restriction maps actual spectral upper groups onto actual spectral upper
groups. -/
theorem restrictNormalHom_map_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := B₀) (L ≃ₐ[K] L) u).map (AlgEquiv.restrictNormalHom F) =
      upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  have h := congrArg (Subgroup.map (D₀).subtype)
    (intermediate_map_upperRamificationGroup K L F u hu)
  rw [Subgroup.map_map] at h
  have hcomp : (D₀).subtype.comp (intermediateDecompositionRestriction K L F) =
      AlgEquiv.restrictNormalHom F := by
    ext s
    rfl
  rw [hcomp] at h
  have := intermediate_spectral_hasExtension K L F
  have hring := spectralIntegerRing_eq_extension_valuationSubring K F
    (Valuation.comap (algebraMap F L) (spectralValuation K L))
  have htransport (A : ValuationSubring F) [IsDiscreteValuationRing A]
      (hA : A = spectralIntegerRing K F) :
      (upperRamificationGroup (R := A) (A.decompositionSubgroup K) u).map
        (A.decompositionSubgroup K).subtype =
          upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
    subst A
    exact upperRamificationGroup_map_mulEquiv
      (spectralDecompositionEquiv K F) (fun _ _ => rfl) hu
  exact h.trans (htransport A₀ hring.symm)

end IntermediateField

end FontaineWintenberger
