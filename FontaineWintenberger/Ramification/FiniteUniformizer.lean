/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.InertiaFixedField
public import FontaineWintenberger.Ramification.Generator
public import FontaineWintenberger.Ramification.ValuedAutomorphism

/-!
# Every uniformizer computes finite inertia ramification

The actual inertia fixed field has the same residue field as the original
finite Galois extension. Consequently every uniformizer generates the top
integer ring over its integers. This gives Serre's reduction to the totally
ramified case without any hypothesis on the residue characteristic.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

local notation "B" => spectralIntegerRing K L
local notation "G" => L ≃ₐ[K] L
local notation "I" => lowerRamificationGroup G (IsLocalRing.maximalIdeal B) 0
local notation "U" => IntermediateField.fixedField I
local notation "A" => Valuation.valuationSubring
  (Valuation.comap (algebraMap U L) (spectralValuation K L))

/-- Every original uniformizer generates the original integers over the
actual integers of the inertia fixed field. -/
theorem inertia_fixedField_adjoin_uniformizer {π : B} (hπ : Irreducible π) :
    Algebra.adjoin A {π} = ⊤ := by
  have := intermediate_spectral_isDiscreteValuationRing K L U
  have := fixedField_integer_moduleFinite K L I
  exact adjoin_uniformizer_eq_top (inertia_fixedField_residue_surjective K L) hπ

/-- Every actual uniformizer attains the intrinsic displacement infimum for
every inertia automorphism, including the identity. -/
theorem ramificationOrder_eq_uniformizer_of_mem_inertia
    {s : G} (hs : s ∈ I) {π : B} (hπ : Irreducible π) :
    ramificationOrder (R := B) G s =
      IsDiscreteValuationRing.addVal B (s • π - π) := by
  have := fixedField_integer_isGaloisGroup K L I
  exact ramificationOrder_eq_generator I
    (inertia_fixedField_adjoin_uniformizer K L hπ) ⟨s, hs⟩

/-- The finite signed embedding number has the uniformizer displacement
formula with the original integer ring's normalization. -/
theorem embeddingRamificationNumber_aut_eq_uniformizer
    {s : G} (hs : s ∈ I) {π : B} (hπ : Irreducible π) :
    embeddingRamificationNumber K s.toAlgHom (AlgHom.id K L) =
      ((IsDiscreteValuationRing.addVal B (s • π - π) : ℝ≥0∞) : EReal) - 1 := by
  rw [embeddingRamificationNumber_aut,
    ramificationOrder_eq_uniformizer_of_mem_inertia K L hs hπ]

/-- The same formula as an actual value on the original field. -/
theorem ramificationOrder_eq_normalizedAdditiveValue_uniformizer
    {s : G} (hs : s ∈ I) {π : B} (hπ : Irreducible π) :
    ((ramificationOrder (R := B) G s : ℝ≥0∞) : EReal) =
      normalizedAdditiveValue B (s (π : L) - (π : L)) := by
  rw [ramificationOrder_eq_uniformizer_of_mem_inertia K L hs hπ]
  exact (normalizedAdditiveValue_coe B (s • π - π)).symm

/-- Dividing by any original uniformizer computes the signed finite
ramification number, also at the identity's infinite endpoint. -/
theorem embeddingRamificationNumber_aut_eq_uniformizer_ratio
    {s : G} (hs : s ∈ I) {π : B} (hπ : Irreducible π) :
    embeddingRamificationNumber K s.toAlgHom (AlgHom.id K L) =
      normalizedAdditiveValue B (s (π : L) / (π : L) - 1) := by
  have hπL : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have he : s (π : L) / (π : L) - 1 =
      ((s • π - π : B) : L) / (π : L) := div_sub_one hπL
  rw [he, normalizedAdditiveValue_div B _ _ hπL,
    normalizedAdditiveValue_coe, normalizedAdditiveValue_coe,
    IsDiscreteValuationRing.addVal_uniformizer hπ]
  simpa only [ENat.toENNReal_one, EReal.coe_ennreal_one] using
    embeddingRamificationNumber_aut_eq_uniformizer K L hs hπ

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Outside inertia the original integral displacement infimum is zero. -/
theorem ramificationOrder_eq_zero_of_not_mem_inertia
    {s : G} (hs : s ∉ I) : ramificationOrder (R := B) G s = 0 := by
  by_contra hn
  apply hs
  exact (mem_lowerRamificationGroup_iff_le_order G 0 s).mpr
    (by simpa using Order.one_le_iff_ne_zero.mpr hn)

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Outside inertia the original signed finite number is minus one. -/
theorem embeddingRamificationNumber_aut_eq_neg_one_of_not_mem_inertia
    {s : G} (hs : s ∉ I) :
    embeddingRamificationNumber K s.toAlgHom (AlgHom.id K L) = -1 := by
  rw [embeddingRamificationNumber_aut,
    ramificationOrder_eq_zero_of_not_mem_inertia K L hs]
  simp

/-- The ratio formula is independent of every choice of original uniformizer. -/
theorem finite_uniformizer_ratio_normalizedAdditiveValue_eq
    {s : G} (hs : s ∈ I) {π ϖ : B} (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    normalizedAdditiveValue B (s (π : L) / (π : L) - 1) =
      normalizedAdditiveValue B (s (ϖ : L) / (ϖ : L) - 1) :=
  (embeddingRamificationNumber_aut_eq_uniformizer_ratio K L hs hπ).symm.trans
    (embeddingRamificationNumber_aut_eq_uniformizer_ratio K L hs hϖ)

end FontaineWintenberger
