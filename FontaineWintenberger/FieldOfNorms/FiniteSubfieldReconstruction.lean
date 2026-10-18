/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionHom
public import FontaineWintenberger.FieldOfNorms.NormUnionKrull
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Actual finite subfields of the canonical norm-field union

Finite basis images lie in an original finite stage. A finite original Galois
overfield and its actual fixed fields then reconstruct the original finite
subfield, without requiring the target union to be separably closed.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FixedField

variable (K L P : Type*) [Field K] [Field L] [Field P]
    [Algebra K L] [Algebra K P] [Algebra L P] [IsScalarTower K L P]
    [FiniteDimensional L P] [IsGalois L P] [Algebra.IsAlgebraic K P]

/-- The original fixed-family descent applies to every subgroup of the
original finite Galois group, with its literal restricted action. -/
theorem mem_range_finiteNormLimitMap_fixedField_iff
    (H : Subgroup (P ≃ₐ[L] P)) (β : NormLimit K P) :
    letI : IsScalarTower K (IntermediateField.fixedField H) P :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
      inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
    β ∈ Set.range (finiteNormLimitMap K (IntermediateField.fixedField H) P) ↔
      ∀ σ : H, normLimitMap (σ.val.restrictScalars K) β = β := by
  let : IsScalarTower K (IntermediateField.fixedField H) P :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
    inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
  rw [mem_range_finiteNormLimitMap_iff_fixed]
  let e := IntermediateField.subgroupEquivAlgEquiv H
  constructor
  · intro h σ
    have he : (e σ).restrictScalars K = σ.val.restrictScalars K :=
      AlgEquiv.ext (fun _ => rfl)
    exact he ▸ h (e σ)
  · intro h σ
    have he : (e.symm σ).val.restrictScalars K = σ.restrictScalars K :=
      AlgEquiv.ext (fun _ => rfl)
    exact he ▸ h (e.symm σ)

end FixedField

section FiniteGalois

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L P : Type*) [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra L P] [IsScalarTower K L P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]
    [FiniteDimensional L P] [IsGalois L P]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hP : IsAPF K P)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteP : ¬ Module.Finite K P)

/-- Every actual subfield of an original finite Galois norm field is the
literal image of the original field fixed by its genuine subgroup. -/
theorem exists_fixedField_finiteNormLimit_range :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K P p hP hInfiniteP
    letI := (finiteNormLimitRingHom K L P p hL hP hInfiniteL hInfiniteP).toAlgebra
    ∀ D : IntermediateField (NormLimit K L) (NormLimit K P),
      ∃ H : Subgroup (P ≃ₐ[L] P),
        letI : IsScalarTower K (IntermediateField.fixedField H) P :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
          inferInstanceAs (Algebra.IsAlgebraic K
            ((IntermediateField.fixedField H).restrictScalars K))
        Set.range (finiteNormLimitMap K (IntermediateField.fixedField H) P) =
          (D : Set (NormLimit K P)) := by
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K P p hP hInfiniteP
  let := (finiteNormLimitRingHom K L P p hL hP hInfiniteL hInfiniteP).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K L P p hP hInfiniteP
  have := finiteNormLimit_isGaloisGroup K L P p hL hP hInfiniteL hInfiniteP
  intro D
  let H := fixingSubgroup (P ≃ₐ[L] P) (D : Set (NormLimit K P))
  refine ⟨H, ?_⟩
  let : IsScalarTower K (IntermediateField.fixedField H) P :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
    inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
  have hD : (FixedPoints.intermediateField H :
      IntermediateField (NormLimit K L) (NormLimit K P)) = D :=
    IsGaloisGroup.fixedPoints_fixingSubgroup (P ≃ₐ[L] P) (NormLimit K L)
      (NormLimit K P) D
  ext β
  rw [mem_range_finiteNormLimitMap_fixedField_iff]
  change β ∈ (FixedPoints.intermediateField H :
    IntermediateField (NormLimit K L) (NormLimit K P)) ↔ β ∈ D
  rw [hD]

end FiniteGalois

section NormUnion

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- Transporting an actual finite subfield of an actual original stage into
the ambient extension gives exactly its original canonical union image. -/
theorem separableNormUnionOf_map_subfield (P : FiniteLayer L Ω)
    (Q : FiniteLayer L P.val) (α : NormLimit K Q.val) :
    letI : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
    letI : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K Q.val :=
      inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
    letI : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
    letI : Algebra.IsSeparable Q.val P.val :=
      Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
    separableNormUnionOf K L Ω p hL hInfinite (FiniteLayer.map P.val.val Q)
        (normLimitMap ((FiniteLayer.equivMap P.val.val Q).restrictScalars K) α) =
      separableNormUnionOf K L Ω p hL hInfinite P
        (finiteNormLimitMap K Q.val P.val α) := by
  let : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
  let : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K Q.val :=
    inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
  let : Algebra.IsSeparable K Q.val :=
    inferInstanceAs (Algebra.IsSeparable K (Q.val.restrictScalars K))
  let : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
  let : Algebra.IsSeparable Q.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
  let R := FiniteLayer.map P.val.val Q
  let e := FiniteLayer.equivMap P.val.val Q
  let : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
  have hRP : R ≤ P := by
    rintro x ⟨a, ha, rfl⟩
    exact a.property
  let : Algebra R.val P.val := (IntermediateField.inclusion hRP).toRingHom.toAlgebra
  let : IsScalarTower K R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite R.val P.val := Module.Finite.right L R.val P.val
  let : Algebra.IsSeparable R.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L R.val P.val
  have hn := finiteNormLimitMap_naturality K (e.restrictScalars K)
    (AlgEquiv.refl : P.val ≃ₐ[K] P.val) (fun _ => rfl) α
  have hv : separableNormUnionTransition K L Ω p hL hInfinite R P hRP
      (normLimitMap (e.restrictScalars K) α) = finiteNormLimitMap K Q.val P.val α := by
    change finiteNormLimitMap K R.val P.val (normLimitMap (e.restrictScalars K) α) = _
    simpa only [normLimitMap_refl] using hn.symm
  exact (separableNormUnionOf_transition K L Ω p hL hInfinite R P hRP _).symm.trans
    (congrArg (separableNormUnionOf K L Ω p hL hInfinite P) hv)

variable [IsSepClosure L Ω]

/-- Every actual finite subfield of the canonical union is the canonical
image of a genuine finite original intermediate field. -/
theorem separableNormUnion_exists_finite_subfield_preimage :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    letI : Module (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) := Algebra.toModule
    letI : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) :=
      (Algebra.toModule : Module (NormLimit K L)
        (SeparableNormUnion K L Ω p hL hInfinite)).toDistribMulAction.toMulAction
    ∀ (D : IntermediateField (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite))
      [FiniteDimensional (NormLimit K L) D],
      ∃ N : FiniteLayer L Ω,
        letI := separableNormUnionStageField K L Ω p hL hInfinite N
        letI := separableNormUnionStageAlgebra K L Ω p hL hInfinite N
        (separableNormUnionOfAlgHom K L Ω p hL hInfinite N).fieldRange = D := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  let : Module (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L Ω p hL hInfinite)).toDistribMulAction.toMulAction
  let (N : FiniteLayer L Ω) : Algebra.IsSeparable K N.val :=
    Algebra.IsSeparable.trans K L N.val
  let (N : FiniteLayer L Ω) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L Ω p hL hInfinite N
  let (N : FiniteLayer L Ω) : Algebra (NormLimit K L) (NormLimit K N.val) :=
    separableNormUnionStageAlgebra K L Ω p hL hInfinite N
  intro D _
  obtain ⟨Q, g, hg⟩ := separableNormUnion_exists_algHom_factor K L Ω p hL hInfinite D.val
  let P : FiniteLayer L Ω := ⟨IntermediateField.normalClosure L Q.val Ω, inferInstance⟩
  have hQP : Q ≤ P := IntermediateField.le_normalClosure Q.val
  let : IsGalois L P.val := ⟨⟩
  let D' := D.comap (separableNormUnionOfAlgHom K L Ω p hL hInfinite P)
  obtain ⟨H, hH⟩ := exists_fixedField_finiteNormLimit_range K L P.val p hL
    (separableNormUnionStage_isAPF K L Ω hL P) hInfinite
    (separableNormUnionStage_infinite K L Ω hInfinite P) D'
  let M : FiniteLayer L P.val := ⟨IntermediateField.fixedField H, inferInstance⟩
  let : IsScalarTower K M.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K M.val :=
    inferInstanceAs (Algebra.IsAlgebraic K (M.val.restrictScalars K))
  let : Module.Finite M.val P.val := Module.Finite.right L M.val P.val
  let : Algebra.IsSeparable M.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L M.val P.val
  let N := FiniteLayer.map P.val.val M
  let e := (FiniteLayer.equivMap P.val.val M).restrictScalars K
  refine ⟨N, ?_⟩
  ext z
  constructor
  · rintro ⟨αN, rfl⟩
    obtain ⟨α, rfl⟩ := (normLimitMulEquiv e).surjective αN
    have hm : finiteNormLimitMap K M.val P.val α ∈ D' :=
      (Set.ext_iff.mp hH _).mp ⟨α, rfl⟩
    have hm' : separableNormUnionOf K L Ω p hL hInfinite P
        (finiteNormLimitMap K M.val P.val α) ∈ D := hm
    exact (congrArg (fun z => z ∈ D)
      (separableNormUnionOf_map_subfield K L Ω p hL hInfinite P M α)).mpr hm'
  · intro hz
    let β := separableNormUnionTransition K L Ω p hL hInfinite Q P hQP (g ⟨z, hz⟩)
    have hj : separableNormUnionOf K L Ω p hL hInfinite P β = z :=
      (separableNormUnionOf_transition K L Ω p hL hInfinite Q P hQP _).trans
        (AlgHom.congr_fun hg ⟨z, hz⟩)
    have hβ : β ∈ D' := by
      change separableNormUnionOf K L Ω p hL hInfinite P β ∈ D
      exact hj.symm ▸ hz
    have hr : β ∈ Set.range (finiteNormLimitMap K M.val P.val) :=
      (Set.ext_iff.mp hH β).mpr hβ
    obtain ⟨α, hα⟩ := hr
    refine ⟨normLimitMap e α, ?_⟩
    exact (separableNormUnionOf_map_subfield K L Ω p hL hInfinite P M α).trans
      ((congrArg (separableNormUnionOf K L Ω p hL hInfinite P) hα).trans hj)

/-- Actual finite original images preserve and reflect inclusion. Reflection
uses their genuine finite fixers and only the original Galois correspondence. -/
theorem separableNormUnionFiniteImage_le_iff (Q R : FiniteLayer L Ω) :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    separableNormUnionFiniteImage K L Ω p hL hInfinite Q ≤
      separableNormUnionFiniteImage K L Ω p hL hInfinite R ↔ Q ≤ R := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  constructor
  · intro h
    have hfix : R.val.fixingSubgroup ≤ Q.val.fixingSubgroup := by
      intro σ hσ
      apply (separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L Ω p hL hInfinite Q σ).mp
      exact IntermediateField.fixingSubgroup_le h
        ((separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L Ω p hL hInfinite R σ).mpr hσ)
    have hh := IntermediateField.fixedField_le hfix
    change Q.val ≤ R.val
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using hh
  · intro h z hz
    obtain ⟨α, rfl⟩ := (mem_separableNormUnionFiniteImage K L Ω p hL hInfinite Q z).mp hz
    exact (mem_separableNormUnionFiniteImage K L Ω p hL hInfinite R _).mpr
      ⟨separableNormUnionTransition K L Ω p hL hInfinite Q R h α,
        separableNormUnionOf_transition K L Ω p hL hInfinite Q R h α⟩

/-- Equal canonical images determine equal actual original finite fields. -/
theorem separableNormUnionFiniteImage_injective :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    Function.Injective (separableNormUnionFiniteImage K L Ω p hL hInfinite) := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  intro Q R h
  exact le_antisymm
    ((separableNormUnionFiniteImage_le_iff K L Ω p hL hInfinite Q R).mp h.le)
    ((separableNormUnionFiniteImage_le_iff K L Ω p hL hInfinite R Q).mp h.ge)

/-- Reconstruction gives a unique actual finite original subfield, and its
image is the literal canonical original image inside the same union. -/
theorem separableNormUnion_existsUnique_finite_subfield_preimage :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    letI : Module (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) := Algebra.toModule
    letI : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) :=
      (Algebra.toModule : Module (NormLimit K L)
        (SeparableNormUnion K L Ω p hL hInfinite)).toDistribMulAction.toMulAction
    ∀ (D : IntermediateField (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite))
      [FiniteDimensional (NormLimit K L) D],
      ∃! N : FiniteLayer L Ω,
        separableNormUnionFiniteImage K L Ω p hL hInfinite N = D := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  let : Module (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p hL hInfinite) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L Ω p hL hInfinite)).toDistribMulAction.toMulAction
  intro D _
  obtain ⟨N, hN⟩ := separableNormUnion_exists_finite_subfield_preimage K L Ω p hL hInfinite D
  refine ⟨N, hN, fun R hR => ?_⟩
  exact separableNormUnionFiniteImage_injective K L Ω p hL hInfinite (hR.trans hN.symm)

end NormUnion

end FontaineWintenberger
