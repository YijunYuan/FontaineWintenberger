/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.Index
public import FontaineWintenberger.LocalField.Spectral.CompatibleNorm
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Degree and total ramification for DVR extensions

The finite-flat degree identity has a single term for a finite local DVR
extension. Its residue-degree-one consequence makes every uniformizer an
integral generator. All indices are Mathlib's canonical ideal indices.
-/

@[expose] public section

namespace FontaineWintenberger

section LocalRings

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]

local notation "mR" => IsLocalRing.maximalIdeal R
local notation "mS" => IsLocalRing.maximalIdeal S

omit [FaithfulSMul R S] [Module.Finite R S] in
/-- Canonical local inertia degree is the residue-field degree. -/
theorem local_inertiaDeg_eq_finrank_residueField :
    (mS).inertiaDeg R =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  Ideal.inertiaDeg_eq_of_isMaximal mR mS

omit [IsLocalHom (algebraMap R S)] in
/-- The fundamental degree identity for a finite injective local map of DVRs. -/
theorem local_ramificationIdx_mul_inertiaDeg :
    (mS).ramificationIdx R * (mS).inertiaDeg R = Module.finrank R S := by
  classical
  have hp : Ideal.primesOver mR S = {mS} :=
    IsLocalRing.primesOver_eq (A := S) (R := R)
      (IsDiscreteValuationRing.maximalIdeal R).ne_bot
  let : Unique (Ideal.primesOver mR S) :=
    { default := ⟨mS, by rw [hp]; simp⟩
      uniq := fun q => Subtype.ext (by
        have hq := q.property
        simpa only [hp, Set.mem_singleton_iff] using hq) }
  have hd : ((default : Ideal.primesOver mR S) : Ideal S) = mS := rfl
  simpa [hd] using
    Ideal.sum_ramification_inertia_eq_finrank mR S

/-- The fundamental degree identity expressed on the canonical local residue fields. -/
theorem local_ramificationIdx_mul_finrank_residueField :
    (mS).ramificationIdx R *
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) =
        Module.finrank R S := by
  rw [← local_inertiaDeg_eq_finrank_residueField R S]
  exact local_ramificationIdx_mul_inertiaDeg R S

/-- Total ramification by degree is equivalent to surjectivity of the residue map. -/
theorem ramificationIdx_eq_finrank_iff_residue_surjective :
    (mS).ramificationIdx R = Module.finrank R S ↔
      Function.Surjective (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)) := by
  rw [← local_ramificationIdx_mul_finrank_residueField R S]
  have he := local_ramificationIdx_pos R S
  have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) ↔ Function.Surjective
        (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :=
    ⟨fun h => h.2, fun h => ⟨(algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)).injective, h⟩⟩
  rw [← hbij, ← Algebra.finrank_eq_one_iff_bijective_algebraMap]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_left he
    simpa using h.symm
  · intro h
    rw [h, mul_one]

/-- Every uniformizer generates a totally ramified finite local DVR extension. -/
theorem adjoin_uniformizer_eq_top_of_ramificationIdx_eq_finrank
    (he : (mS).ramificationIdx R = Module.finrank R S) {π : S} (hπ : Irreducible π) :
    Algebra.adjoin R {π} = ⊤ :=
  adjoin_uniformizer_eq_top
    ((ramificationIdx_eq_finrank_iff_residue_surjective R S).mp he) hπ

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [IsScalarTower R K L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]

/-- The local fundamental degree identity on the fraction fields. -/
theorem local_ramificationIdx_mul_residueDegree_eq_finrank :
    (mS).ramificationIdx R *
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) =
        Module.finrank K L := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact local_ramificationIdx_mul_finrank_residueField R S

/-- Total ramification on the field degree makes every integral uniformizer a generator. -/
theorem adjoin_uniformizer_eq_top_of_ramificationIdx_eq_field_finrank
    (he : (mS).ramificationIdx R = Module.finrank K L) {π : S} (hπ : Irreducible π) :
    Algebra.adjoin R {π} = ⊤ := by
  apply adjoin_uniformizer_eq_top_of_ramificationIdx_eq_finrank R S _ hπ
  rwa [← IsFractionRing.finrank_eq R K S L]

end LocalRings

section ChosenExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
variable [(NormedField.valuation (K := K)).HasExtension w]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => Valuation.valuationSubring w

/-- The chosen extension valuation ring satisfies the fundamental degree identity. -/
theorem extensionValuationSubring_ramificationIdx_mul_residueDegree :
    (IsLocalRing.maximalIdeal OL).ramificationIdx OK *
      Module.finrank (IsLocalRing.ResidueField OK) (IsLocalRing.ResidueField OL) =
        Module.finrank K L := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact local_ramificationIdx_mul_residueDegree_eq_finrank OK OL K L

/-- Any uniformizer of a totally ramified chosen finite extension generates its integers. -/
theorem extensionValuationSubring_adjoin_uniformizer_eq_top
    (he : (IsLocalRing.maximalIdeal OL).ramificationIdx OK = Module.finrank K L)
    {π : OL} (hπ : Irreducible π) : Algebra.adjoin OK {π} = ⊤ := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact adjoin_uniformizer_eq_top_of_ramificationIdx_eq_field_finrank OK OL K L he hπ

end ChosenExtension

section Valued

variable (K : Type*) [Field K] (ΓK : Type*) [LinearOrderedCommGroupWithZero ΓK]
variable [val : Valued K ΓK] [Valuation.IsRankOneDiscrete val.v] [CompleteSpace K]
variable [IsDiscreteValuationRing val.v.valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]
variable {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL] (w : Valuation L ΓL)
variable [val.v.HasExtension w]

noncomputable local instance : Valuation.RankOne val.v :=
  Valuation.IsRankOneDiscrete.rankOne val.v (e := 2) (by norm_num)

noncomputable local instance : NontriviallyNormedField K := discreteValuedNormedField K ΓK

local instance : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (Valued.isNonarchimedean_norm K ΓK)

local notation "R" => Valuation.valuationSubring val.v
local notation "S" => Valuation.valuationSubring w

/-- Finiteness over the valuation ring, with its canonical inclusion. -/
theorem discreteValued_extension_moduleFinite : Module.Finite R S := by
  have := discreteValued_norm_hasExtension K ΓK L w
  have := discreteValued_isCompleteDiscreteValuedField K ΓK
  let e := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (discreteValued_valuationSubring K ΓK))
  apply Module.Finite.of_equiv_equiv
    (A₁ := (NormedField.valuation (K := K)).valuationSubring)
    (B₁ := S) (A₂ := R) (B₂ := S) e (RingEquiv.refl S)
  ext r
  rfl

/-- The field degree identity over the valuation ring. -/
theorem discreteValued_extension_ramificationIdx_mul_residueDegree :
    (IsLocalRing.maximalIdeal S).ramificationIdx R *
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) =
        Module.finrank K L := by
  have := discreteValued_extension_isDiscreteValuationRing K ΓK L w
  have := discreteValued_extension_moduleFinite K ΓK L w
  exact local_ramificationIdx_mul_residueDegree_eq_finrank R S K L

/-- Every uniformizer of a totally ramified source-valued extension generates its integers. -/
theorem discreteValued_extension_adjoin_uniformizer_eq_top
    (he : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L)
    {π : S} (hπ : Irreducible π) : Algebra.adjoin R {π} = ⊤ := by
  have := discreteValued_extension_isDiscreteValuationRing K ΓK L w
  have := discreteValued_extension_moduleFinite K ΓK L w
  exact adjoin_uniformizer_eq_top_of_ramificationIdx_eq_field_finrank R S K L he hπ

end Valued

end FontaineWintenberger
