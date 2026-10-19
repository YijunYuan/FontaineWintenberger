/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Tower.Wild

/-!
# Unbounded finite ramification and the residue prime

An infinite algebraic extension has arbitrarily large finite subextension
degrees. On the APF wild tail these degrees are ramification indices,
so the residue prime belongs to every fixed ideal power eventually.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FiniteDegrees

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]

/-- The relative degrees above any finite intermediate field tend to infinity
when the algebraic extension is infinite. -/
theorem FiniteIntermediateField.exists_tail_finrank_ge [Fact (¬ Module.Finite K L)]
    (D : FiniteIntermediateField K L) (n : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∃ hDT : D ≤ T, ∀ E : FiniteIntermediateField K L, ∀ hTE : T
        ≤ E,
      n ≤ Module.finrank D.val (IntermediateField.extendScalars (hDT.trans hTE)) := by
  obtain ⟨F, hF, hdegree⟩ :=
    IntermediateField.exists_lt_finrank_of_infinite_dimensional (Fact.out : ¬ Module.Finite K L)
      (Module.finrank K D.val * n)
  let F₀ : FiniteIntermediateField K L := ⟨F, hF⟩
  let T := FiniteIntermediateField.sup D F₀
  refine ⟨T, FiniteIntermediateField.le_sup_left D F₀, fun E hTE => ?_⟩
  have hDE : D ≤ E := (FiniteIntermediateField.le_sup_left D F₀).trans hTE
  have hFE : F ≤ E.val := (FiniteIntermediateField.le_sup_right D F₀).trans hTE
  have hmono := IntermediateField.finrank_le_of_le_right hFE
  have hmul := IntermediateField.finrank_bot_mul_relfinrank hDE
  rw [IntermediateField.relfinrank_eq_finrank_of_le hDE] at hmul
  have hpos : 0 < Module.finrank K D.val := Module.finrank_pos
  nlinarith

end FiniteDegrees

section APF

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- On an APF wild tail, the canonical ramification indices above
every fixed finite intermediate field tend to infinity. -/
theorem IsAPF.exists_finiteIntermediateField_ramificationIdx_unbounded [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∃ W : FiniteIntermediateField K L, ∀ D : FiniteIntermediateField K L, W ≤ D → ∀ n : ℕ,
      ∃ T : FiniteIntermediateField K L, ∃ hDT : D ≤ T, ∀ E : FiniteIntermediateField K L, ∀ hTE :
          T ≤ E,
        letI : Algebra D.val E.val :=
          (IntermediateField.inclusion (hDT.trans hTE)).toRingHom.toAlgebra
        letI : IsScalarTower K D.val E.val := IsScalarTower.of_algebraMap_eq' rfl
        letI := spectralValuation_hasExtension_tower K (E := D.val) (L := E.val)
        n ≤ (IsLocalRing.maximalIdeal (spectralIntegerRing K E.val)).ramificationIdx
          (spectralIntegerRing K D.val) := by
  obtain ⟨W, hW⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  refine ⟨W, fun D hWD n => ?_⟩
  obtain ⟨T, hDT, hT⟩ := FiniteIntermediateField.exists_tail_finrank_ge K L D n
  refine ⟨T, hDT, fun E hTE => ?_⟩
  let : Algebra D.val E.val :=
    (IntermediateField.inclusion (hDT.trans hTE)).toRingHom.toAlgebra
  have : IsScalarTower K D.val E.val := IsScalarTower.of_algebraMap_eq' rfl
  have := spectralValuation_hasExtension_tower K (E := D.val) (L := E.val)
  rw [(hW D E hWD (hDT.trans hTE)).2.2]
  exact hT E hTE

/-- The residue prime belongs to every fixed power of the maximal
ideal on a sufficiently large finite-layer tail. The proof also
covers equal characteristic, where the prime is already zero. -/
theorem IsAPF.exists_finiteIntermediateField_natCast_mem_maximalIdeal_pow [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (n : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      (p : spectralIntegerRing K E.val) ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n := by
  obtain ⟨W, hW⟩ := IsAPF.exists_finiteIntermediateField_ramificationIdx_unbounded K L
  obtain ⟨T, hWT, hT⟩ := hW W le_rfl n
  refine ⟨T, fun E hTE => ?_⟩
  let : Algebra W.val E.val :=
    (IntermediateField.inclusion (hWT.trans hTE)).toRingHom.toAlgebra
  have : IsScalarTower K W.val E.val := IsScalarTower.of_algebraMap_eq' rfl
  have := spectralValuation_hasExtension_tower K (E := W.val) (L := E.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K W.val) (spectralValuation K E.val)
  let : CharP (IsLocalRing.ResidueField (spectralIntegerRing K W.val)) p :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField
        (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField (spectralIntegerRing K W.val))).injective p
  have hp : (p : spectralIntegerRing K W.val) ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K W.val) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hmap := Ideal.mem_map_of_mem
    (algebraMap (spectralIntegerRing K W.val) (spectralIntegerRing K E.val)) hp
  rw [map_maximalIdeal_eq_pow_ramificationIdx, map_natCast] at hmap
  exact Ideal.pow_le_pow_right (hT E hTE) hmap

/-- The image of the residue prime in each finite field
is eventually in the image of every maximal-ideal power. -/
theorem IsAPF.exists_finiteIntermediateField_natCast_mem_image_maximalIdeal_pow [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (n : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      (p : E.val) ∈ (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
          Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_natCast_mem_maximalIdeal_pow K L n
  exact ⟨T, fun E hTE => ⟨(p : spectralIntegerRing K E.val), hT E hTE, by simp⟩⟩

end APF

end FontaineWintenberger
