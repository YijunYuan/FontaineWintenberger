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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L P : Type*) [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra L P] [IsScalarTower K L P]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]
    [FiniteDimensional L P] [IsGalois L P]

local notation "p" => residueChar K

variable [IsAPF K L] [IsAPF K P]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K P)]

/-- Every actual subfield of an original finite Galois norm field is the
literal image of the original field fixed by its genuine subgroup. -/
theorem exists_fixedField_finiteNormLimit_range :
    letI := (finiteNormLimitRingHom K L P).toAlgebra
    ∀ D : IntermediateField (NormLimit K L) (NormLimit K P),
      ∃ H : Subgroup (P ≃ₐ[L] P),
        letI : IsScalarTower K (IntermediateField.fixedField H) P :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
          inferInstanceAs (Algebra.IsAlgebraic K
            ((IntermediateField.fixedField H).restrictScalars K))
        Set.range (finiteNormLimitMap K (IntermediateField.fixedField H) P) =
          (D : Set (NormLimit K P)) := by
  let := (finiteNormLimitRingHom K L P).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K L P
  have := finiteNormLimit_isGaloisGroup K L P
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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Transporting an actual finite subfield of an actual original stage into
the ambient extension gives exactly its original canonical union image. -/
theorem separableNormUnionOf_map_subfield (P : FiniteLayer L Ω)
    (Q : FiniteLayer L P.val) (α : NormLimit K Q.val) :
    letI : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K Q.val :=
      inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
    letI : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
    letI : Algebra.IsSeparable Q.val P.val :=
      Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
    separableNormUnionOf K L Ω (FiniteLayer.map P.val.val Q)
        (normLimitMap ((FiniteLayer.equivMap P.val.val Q).restrictScalars K) α) =
      separableNormUnionOf K L Ω P
        (finiteNormLimitMap K Q.val P.val α) := by
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
  have hv : separableNormUnionTransition K L Ω R P hRP
      (normLimitMap (e.restrictScalars K) α) = finiteNormLimitMap K Q.val P.val α := by
    change finiteNormLimitMap K R.val P.val (normLimitMap (e.restrictScalars K) α) = _
    simpa only [normLimitMap_refl] using hn.symm
  exact (separableNormUnionOf_transition K L Ω R P hRP _).symm.trans
    (congrArg (separableNormUnionOf K L Ω P) hv)

variable [IsSepClosure L Ω]

/-- Every actual finite subfield of the canonical union is the canonical
image of a genuine finite original intermediate field. -/
theorem separableNormUnion_exists_finite_subfield_preimage :
    ∀ (D : IntermediateField (NormLimit K L) (SeparableNormUnion K L Ω))
      [FiniteDimensional (NormLimit K L) D],
      ∃ N : FiniteLayer L Ω,
        (separableNormUnionOfAlgHom K L Ω N).fieldRange = D := by
  intro D _
  obtain ⟨Q, g, hg⟩ := separableNormUnion_exists_algHom_factor K L Ω D.val
  let P : FiniteLayer L Ω := ⟨IntermediateField.normalClosure L Q.val Ω, inferInstance⟩
  have hQP : Q ≤ P := IntermediateField.le_normalClosure Q.val
  have : IsGalois L P.val := ⟨⟩
  -- an opaque stage: instance search on `NormLimit K P.val` keys on `P`, not on its value
  clear_value P
  let D' := D.comap (separableNormUnionOfAlgHom K L Ω P)
  obtain ⟨H, hH⟩ := exists_fixedField_finiteNormLimit_range K L P.val D'
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
    have hm' : separableNormUnionOf K L Ω P
        (finiteNormLimitMap K M.val P.val α) ∈ D := hm
    exact (congrArg (fun z => z ∈ D)
      (separableNormUnionOf_map_subfield K L Ω P M α)).mpr hm'
  · intro hz
    let β := separableNormUnionTransition K L Ω Q P hQP (g ⟨z, hz⟩)
    have hj : separableNormUnionOf K L Ω P β = z :=
      (separableNormUnionOf_transition K L Ω Q P hQP _).trans
        (AlgHom.congr_fun hg ⟨z, hz⟩)
    have hβ : β ∈ D' := by
      change separableNormUnionOf K L Ω P β ∈ D
      exact hj.symm ▸ hz
    have hr : β ∈ Set.range (finiteNormLimitMap K M.val P.val) :=
      (Set.ext_iff.mp hH β).mpr hβ
    obtain ⟨α, hα⟩ := hr
    refine ⟨normLimitMap e α, ?_⟩
    exact (separableNormUnionOf_map_subfield K L Ω P M α).trans
      ((congrArg (separableNormUnionOf K L Ω P) hα).trans hj)

/-- Actual finite original images preserve and reflect inclusion. Reflection
uses their genuine finite fixers and only the original Galois correspondence. -/
theorem separableNormUnionFiniteImage_le_iff (Q R : FiniteLayer L Ω) :
    separableNormUnionFiniteImage K L Ω Q ≤
      separableNormUnionFiniteImage K L Ω R ↔ Q ≤ R := by
  constructor
  · intro h
    have hfix : R.val.fixingSubgroup ≤ Q.val.fixingSubgroup := by
      intro σ hσ
      apply (separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L Ω Q σ).mp
      exact IntermediateField.fixingSubgroup_le h
        ((separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L Ω R σ).mpr hσ)
    have hh := IntermediateField.fixedField_le hfix
    change Q.val ≤ R.val
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using hh
  · intro h z hz
    obtain ⟨α, rfl⟩ := (mem_separableNormUnionFiniteImage K L Ω Q z).mp hz
    exact (mem_separableNormUnionFiniteImage K L Ω R _).mpr
      ⟨separableNormUnionTransition K L Ω Q R h α,
        separableNormUnionOf_transition K L Ω Q R h α⟩

/-- Equal canonical images determine equal actual original finite fields. -/
theorem separableNormUnionFiniteImage_injective :
    Function.Injective (separableNormUnionFiniteImage K L Ω) := by
  intro Q R h
  exact le_antisymm
    ((separableNormUnionFiniteImage_le_iff K L Ω Q R).mp h.le)
    ((separableNormUnionFiniteImage_le_iff K L Ω R Q).mp h.ge)

/-- Reconstruction gives a unique actual finite original subfield, and its
image is the literal canonical original image inside the same union. -/
theorem separableNormUnion_existsUnique_finite_subfield_preimage :
    ∀ (D : IntermediateField (NormLimit K L) (SeparableNormUnion K L Ω))
      [FiniteDimensional (NormLimit K L) D],
      ∃! N : FiniteLayer L Ω,
        separableNormUnionFiniteImage K L Ω N = D := by
  intro D _
  obtain ⟨N, hN⟩ := separableNormUnion_exists_finite_subfield_preimage K L Ω D
  refine ⟨N, hN, fun R hR => ?_⟩
  exact separableNormUnionFiniteImage_injective K L Ω (hR.trans hN.symm)

end NormUnion

end FontaineWintenberger
