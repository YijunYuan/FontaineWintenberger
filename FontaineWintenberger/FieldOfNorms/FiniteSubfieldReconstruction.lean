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
# Actual finite subfields of the canonical relative field of norms

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
theorem mem_range_finiteFieldOfNormsMap_fixedField_iff
    (H : Subgroup (P ≃ₐ[L] P)) (β : FieldOfNorms K P) :
    letI : IsScalarTower K (IntermediateField.fixedField H) P :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
      inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
    β ∈ Set.range (FieldOfNorms.finiteMap K (IntermediateField.fixedField H) P) ↔
      ∀ σ : H, FieldOfNorms.map (σ.val.restrictScalars K) β = β := by
  let : IsScalarTower K (IntermediateField.fixedField H) P :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
    inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
  rw [mem_range_finiteFieldOfNormsMap_iff_fixed]
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
theorem exists_fixedField_finiteFieldOfNorms_range :
    letI := (FieldOfNorms.finiteRingHom K L P).toAlgebra
    ∀ D : IntermediateField (FieldOfNorms K L) (FieldOfNorms K P),
      ∃ H : Subgroup (P ≃ₐ[L] P),
        letI : IsScalarTower K (IntermediateField.fixedField H) P :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
          inferInstanceAs (Algebra.IsAlgebraic K
            ((IntermediateField.fixedField H).restrictScalars K))
        Set.range (FieldOfNorms.finiteMap K (IntermediateField.fixedField H) P) =
          (D : Set (FieldOfNorms K P)) := by
  let := (FieldOfNorms.finiteRingHom K L P).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K L P
  have := FieldOfNorms.finite_isGaloisGroup K L P
  intro D
  let H := fixingSubgroup (P ≃ₐ[L] P) (D : Set (FieldOfNorms K P))
  refine ⟨H, ?_⟩
  let : IsScalarTower K (IntermediateField.fixedField H) P :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
    inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
  have hD : (FixedPoints.intermediateField H :
      IntermediateField (FieldOfNorms K L) (FieldOfNorms K P)) = D :=
    IsGaloisGroup.fixedPoints_fixingSubgroup (P ≃ₐ[L] P) (FieldOfNorms K L)
      (FieldOfNorms K P) D
  ext β
  rw [mem_range_finiteFieldOfNormsMap_fixedField_iff]
  change β ∈ (FixedPoints.intermediateField H :
    IntermediateField (FieldOfNorms K L) (FieldOfNorms K P)) ↔ β ∈ D
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
the ambient extension gives exactly its original relative field of norms image. -/
theorem RelFieldOfNorms.of_map_subfield (P : FiniteIntermediateField L Ω)
    (Q : FiniteIntermediateField L P.val) (α : FieldOfNorms K Q.val) :
    letI : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K Q.val :=
      inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
    letI : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
    letI : Algebra.IsSeparable Q.val P.val :=
      Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
    RelFieldOfNorms.of K L Ω (FiniteIntermediateField.map P.val.val Q)
        (FieldOfNorms.map ((FiniteIntermediateField.equivMap P.val.val Q).restrictScalars K) α) =
      RelFieldOfNorms.of K L Ω P
        (FieldOfNorms.finiteMap K Q.val P.val α) := by
  let : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K Q.val :=
    inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
  let : Algebra.IsSeparable K Q.val :=
    inferInstanceAs (Algebra.IsSeparable K (Q.val.restrictScalars K))
  let : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
  let : Algebra.IsSeparable Q.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
  let R := FiniteIntermediateField.map P.val.val Q
  let e := FiniteIntermediateField.equivMap P.val.val Q
  have hRP : R ≤ P := by
    rintro x ⟨a, ha, rfl⟩
    exact a.property
  let : Algebra R.val P.val := (IntermediateField.inclusion hRP).toRingHom.toAlgebra
  let : IsScalarTower K R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite R.val P.val := Module.Finite.right L R.val P.val
  let : Algebra.IsSeparable R.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L R.val P.val
  have hn := FieldOfNorms.finiteMap_naturality K (e.restrictScalars K)
    (AlgEquiv.refl : P.val ≃ₐ[K] P.val) (fun _ => rfl) α
  have hv : RelFieldOfNorms.transition K L Ω R P hRP
      (FieldOfNorms.map (e.restrictScalars K) α) = FieldOfNorms.finiteMap K Q.val P.val α := by
    change FieldOfNorms.finiteMap K R.val P.val (FieldOfNorms.map (e.restrictScalars K) α) = _
    simpa only [FieldOfNorms.map_refl] using hn.symm
  exact (RelFieldOfNorms.of_transition K L Ω R P hRP _).symm.trans
    (congrArg (RelFieldOfNorms.of K L Ω P) hv)

variable [IsSepClosure L Ω]

/-- Every actual finite subfield of the relative field of norms is the canonical
image of a genuine finite original intermediate field. -/
theorem RelFieldOfNorms._exists_finite_subfield_preimage :
    ∀ (D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω))
      [FiniteDimensional (FieldOfNorms K L) D],
      ∃ N : FiniteIntermediateField L Ω,
        (RelFieldOfNorms.ofAlgHom K L Ω N).fieldRange = D := by
  intro D _
  obtain ⟨Q, g, hg⟩ := RelFieldOfNorms._exists_algHom_factor K L Ω D.val
  let P : FiniteIntermediateField L Ω := ⟨IntermediateField.normalClosure L Q.val Ω, inferInstance⟩
  have hQP : Q ≤ P := IntermediateField.le_normalClosure Q.val
  have : IsGalois L P.val := ⟨⟩
  -- an opaque stage: instance search on `FieldOfNorms K P.val` keys on `P`, not on its value
  clear_value P
  let D' := D.comap (RelFieldOfNorms.ofAlgHom K L Ω P)
  obtain ⟨H, hH⟩ := exists_fixedField_finiteFieldOfNorms_range K L P.val D'
  let M : FiniteIntermediateField L P.val := ⟨IntermediateField.fixedField H, inferInstance⟩
  let : IsScalarTower K M.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K M.val :=
    inferInstanceAs (Algebra.IsAlgebraic K (M.val.restrictScalars K))
  let : Module.Finite M.val P.val := Module.Finite.right L M.val P.val
  let : Algebra.IsSeparable M.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L M.val P.val
  let N := FiniteIntermediateField.map P.val.val M
  let e := (FiniteIntermediateField.equivMap P.val.val M).restrictScalars K
  refine ⟨N, ?_⟩
  ext z
  constructor
  · rintro ⟨αN, rfl⟩
    obtain ⟨α, rfl⟩ := (FieldOfNorms.mulEquiv e).surjective αN
    have hm : FieldOfNorms.finiteMap K M.val P.val α ∈ D' :=
      (Set.ext_iff.mp hH _).mp ⟨α, rfl⟩
    have hm' : RelFieldOfNorms.of K L Ω P
        (FieldOfNorms.finiteMap K M.val P.val α) ∈ D := hm
    exact (congrArg (fun z => z ∈ D)
      (RelFieldOfNorms.of_map_subfield K L Ω P M α)).mpr hm'
  · intro hz
    let β := RelFieldOfNorms.transition K L Ω Q P hQP (g ⟨z, hz⟩)
    have hj : RelFieldOfNorms.of K L Ω P β = z :=
      (RelFieldOfNorms.of_transition K L Ω Q P hQP _).trans
        (AlgHom.congr_fun hg ⟨z, hz⟩)
    have hβ : β ∈ D' := by
      change RelFieldOfNorms.of K L Ω P β ∈ D
      exact hj.symm ▸ hz
    have hr : β ∈ Set.range (FieldOfNorms.finiteMap K M.val P.val) :=
      (Set.ext_iff.mp hH β).mpr hβ
    obtain ⟨α, hα⟩ := hr
    refine ⟨FieldOfNorms.map e α, ?_⟩
    exact (RelFieldOfNorms.of_map_subfield K L Ω P M α).trans
      ((congrArg (RelFieldOfNorms.of K L Ω P) hα).trans hj)

/-- Actual finite original images preserve and reflect inclusion. Reflection
uses their genuine finite fixers and only the original Galois correspondence. -/
theorem RelFieldOfNorms.finiteImage_le_iff (Q R : FiniteIntermediateField L Ω) :
    RelFieldOfNorms.finiteImage K L Ω Q ≤
      RelFieldOfNorms.finiteImage K L Ω R ↔ Q ≤ R := by
  constructor
  · intro h
    have hfix : R.val.fixingSubgroup ≤ Q.val.fixingSubgroup := by
      intro σ hσ
      apply (RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff K L Ω Q σ).mp
      exact IntermediateField.fixingSubgroup_le h
        ((RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff K L Ω R σ).mpr hσ)
    have hh := IntermediateField.fixedField_le hfix
    change Q.val ≤ R.val
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using hh
  · intro h z hz
    obtain ⟨α, rfl⟩ := (mem_relFieldOfNormsFiniteImage K L Ω Q z).mp hz
    exact (mem_relFieldOfNormsFiniteImage K L Ω R _).mpr
      ⟨RelFieldOfNorms.transition K L Ω Q R h α,
        RelFieldOfNorms.of_transition K L Ω Q R h α⟩

/-- Equal canonical images determine equal actual original finite fields. -/
theorem RelFieldOfNorms.finiteImage_injective :
    Function.Injective (RelFieldOfNorms.finiteImage K L Ω) := by
  intro Q R h
  exact le_antisymm
    ((RelFieldOfNorms.finiteImage_le_iff K L Ω Q R).mp h.le)
    ((RelFieldOfNorms.finiteImage_le_iff K L Ω R Q).mp h.ge)

/-- Reconstruction gives a unique actual finite original subfield, and its
image is the literal canonical original image inside the same union. -/
theorem RelFieldOfNorms._existsUnique_finite_subfield_preimage :
    ∀ (D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω))
      [FiniteDimensional (FieldOfNorms K L) D],
      ∃! N : FiniteIntermediateField L Ω,
        RelFieldOfNorms.finiteImage K L Ω N = D := by
  intro D _
  obtain ⟨N, hN⟩ := RelFieldOfNorms._exists_finite_subfield_preimage K L Ω D
  refine ⟨N, hN, fun R hR => ?_⟩
  exact RelFieldOfNorms.finiteImage_injective K L Ω (hR.trans hN.symm)

end NormUnion

end FontaineWintenberger
