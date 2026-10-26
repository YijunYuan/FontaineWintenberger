/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Relative.Hom
public import FontaineWintenberger.FieldOfNorms.Relative.Krull
public import FontaineWintenberger.FieldOfNorms.Relative.SeparablyClosed
public import FontaineWintenberger.LocalField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Closure

/-!
# The essential image of the field of norms functor

## Finite subfields of the canonical relative field of norms

Finite basis images lie in a finite stage. A finite Galois
overfield and its fixed fields then reconstruct the finite
subfield, without requiring the target union to be separably closed.

## Finite essential image of the norm-field functor

The proved separable closure of the norm field and reconstruction
of its finite subfields realize every finite separable target as a
finite norm field.

## Algebraic essential image of the relative field of norms

Unique reconstruction of finite subfields gives a directed family.
Its intermediate-field supremum has precisely the prescribed image
under the same canonical relative field of norms embedding.

## Main definitions

* `exists_relFieldOfNorms_algEquiv`: The algebraic essential image with no prescribed closure: the
  standard separable closure supplies that choice.

## Main results

* `FieldOfNorms.mem_range_inclusion_fixedField_iff`: The fixed-family descent applies to every
  subgroup of the finite Galois group, with its restricted action.
* `FieldOfNorms.exists_fixedField_inclusion_range`: Every subfield of a finite Galois norm field is
  the image of the field fixed by its subgroup.
* `RelFieldOfNorms.of_map_subfield`: Transporting a finite subfield of a stage into the ambient
  extension gives exactly its relative field of norms image.
* `RelFieldOfNorms.exists_finite_subfield_preimage`: Every finite subfield of the relative field of
  norms is the canonical image of a finite intermediate field.
* `RelFieldOfNorms.finiteImage_le_iff`: Finite images preserve and reflect inclusion.
* `RelFieldOfNorms.finiteImage_injective`: Equal canonical images determine equal finite fields.
* `RelFieldOfNorms.existsUnique_finite_subfield_preimage`: Reconstruction gives an unique finite
  subfield, and its image is the canonical image inside the same union.
* `exists_finite_fieldOfNorms_algEquiv_of_separableClosure`: Every finite separable extension of the
  norm field is isomorphic over that same field to a finite norm-field stage in the prescribed
  separable closure.

## Notation

The following notation is local to this file.

* `p` denotes the residue characteristic `residueChar K`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section FixedField

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L P : Type*) [Field L] [Field P] [Algebra K L] [Algebra K P]
    [Algebra L P] [IsScalarTower K L P] [Algebra.IsSeparable K L] [Algebra.IsSeparable K P]
    [FiniteDimensional L P] [IsGalois L P]
    [IsAPF K L] [IsAPF K P] [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K P)]

/-- The fixed-family descent applies to every subgroup of the
finite Galois group, with its restricted action. -/
theorem FieldOfNorms.mem_range_inclusion_fixedField_iff
    (H : Subgroup (P ≃ₐ[L] P)) (β : FieldOfNorms K P) :
    letI : IsScalarTower K (IntermediateField.fixedField H) P :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
      inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
    β ∈ Set.range (FieldOfNorms.inclusion K (IntermediateField.fixedField H) P) ↔
      ∀ σ : H, FieldOfNorms.mapEquiv (σ.val.restrictScalars K) β = β := by
  let : IsScalarTower K (IntermediateField.fixedField H) P :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
    inferInstanceAs (Algebra.IsAlgebraic K ((IntermediateField.fixedField H).restrictScalars K))
  rw [FieldOfNorms.mem_range_inclusion_iff_fixed]
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

/-- Every subfield of a finite Galois norm field is the
image of the field fixed by its subgroup. -/
theorem FieldOfNorms.exists_fixedField_inclusion_range :
    letI := (FieldOfNorms.inclusion K L P).toAlgebra
    ∀ D : IntermediateField (FieldOfNorms K L) (FieldOfNorms K P),
      ∃ H : Subgroup (P ≃ₐ[L] P),
        letI : IsScalarTower K (IntermediateField.fixedField H) P :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : Algebra.IsAlgebraic K (IntermediateField.fixedField H) :=
          inferInstanceAs (Algebra.IsAlgebraic K
            ((IntermediateField.fixedField H).restrictScalars K))
        Set.range (FieldOfNorms.inclusion K (IntermediateField.fixedField H) P) =
          (D : Set (FieldOfNorms K P)) := by
  let := (FieldOfNorms.inclusion K L P).toAlgebra
  let := FieldOfNorms.galoisAction K L P
  have := FieldOfNorms.isGaloisGroup K L P
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
  rw [FieldOfNorms.mem_range_inclusion_fixedField_iff]
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

/-- Transporting a finite subfield of a stage into
the ambient extension gives exactly its relative field of norms image. -/
theorem RelFieldOfNorms.of_map_subfield (P : FiniteIntermediateField L Ω)
    (Q : FiniteIntermediateField L P.val) (α : FieldOfNorms K Q.val) :
    letI : IsScalarTower K Q.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.IsAlgebraic K Q.val :=
      inferInstanceAs (Algebra.IsAlgebraic K (Q.val.restrictScalars K))
    letI : Module.Finite Q.val P.val := Module.Finite.right L Q.val P.val
    letI : Algebra.IsSeparable Q.val P.val :=
      Algebra.isSeparable_tower_top_of_isSeparable L Q.val P.val
    RelFieldOfNorms.of K L Ω (FiniteIntermediateField.map P.val.val Q)
        (FieldOfNorms.mapEquiv
          ((FiniteIntermediateField.equivMap P.val.val Q).restrictScalars K) α) =
      RelFieldOfNorms.of K L Ω P
        (FieldOfNorms.inclusion K Q.val P.val α) := by
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
  have hn := FieldOfNorms.mapEquiv_inclusion (e.restrictScalars K)
    (AlgEquiv.refl : P.val ≃ₐ[K] P.val) (fun _ => rfl) α
  have hv : RelFieldOfNorms.transition K L Ω R P hRP
      (FieldOfNorms.mapEquiv (e.restrictScalars K) α) = FieldOfNorms.inclusion K Q.val P.val α := by
    change FieldOfNorms.inclusion K R.val P.val (FieldOfNorms.mapEquiv (e.restrictScalars K) α) = _
    simpa only [FieldOfNorms.mapEquiv_refl] using hn.symm
  exact (RelFieldOfNorms.of_transition K L Ω R P hRP _).symm.trans
    (congrArg (RelFieldOfNorms.of K L Ω P) hv)

variable [IsSepClosure L Ω]

/-- Every finite subfield of the relative field of norms is the canonical
image of a finite intermediate field. -/
theorem RelFieldOfNorms.exists_finite_subfield_preimage :
    ∀ (D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω))
      [FiniteDimensional (FieldOfNorms K L) D],
      ∃ N : FiniteIntermediateField L Ω,
        (RelFieldOfNorms.ofAlgHom K L Ω N).fieldRange = D := by
  intro D _
  obtain ⟨Q, g, hg⟩ := RelFieldOfNorms.exists_algHom_factor K L Ω D.val
  let P : FiniteIntermediateField L Ω := ⟨IntermediateField.normalClosure L Q.val Ω, inferInstance⟩
  have hQP : Q ≤ P := IntermediateField.le_normalClosure Q.val
  have : IsGalois L P.val := ⟨⟩
  -- an opaque stage: instance search on `FieldOfNorms K P.val` keys on `P`, not on its value
  clear_value P
  let D' := D.comap (RelFieldOfNorms.ofAlgHom K L Ω P)
  obtain ⟨H, hH⟩ := FieldOfNorms.exists_fixedField_inclusion_range K L P.val D'
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
    obtain ⟨α, rfl⟩ := (FieldOfNorms.mapEquiv e).surjective αN
    have hm : FieldOfNorms.inclusion K M.val P.val α ∈ D' :=
      (Set.ext_iff.mp hH _).mp ⟨α, rfl⟩
    have hm' : RelFieldOfNorms.of K L Ω P
        (FieldOfNorms.inclusion K M.val P.val α) ∈ D := hm
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
    have hr : β ∈ Set.range (FieldOfNorms.inclusion K M.val P.val) :=
      (Set.ext_iff.mp hH β).mpr hβ
    obtain ⟨α, hα⟩ := hr
    refine ⟨FieldOfNorms.mapEquiv e α, ?_⟩
    exact (RelFieldOfNorms.of_map_subfield K L Ω P M α).trans
      ((congrArg (RelFieldOfNorms.of K L Ω P) hα).trans hj)

/-- Finite images preserve and reflect inclusion. Reflection
uses their finite fixers and only the Galois correspondence. -/
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

/-- Equal canonical images determine equal finite fields. -/
theorem RelFieldOfNorms.finiteImage_injective :
    Function.Injective (RelFieldOfNorms.finiteImage K L Ω) := by
  intro Q R h
  exact le_antisymm
    ((RelFieldOfNorms.finiteImage_le_iff K L Ω Q R).mp h.le)
    ((RelFieldOfNorms.finiteImage_le_iff K L Ω R Q).mp h.ge)

/-- Reconstruction gives an unique finite subfield, and its
image is the canonical image inside the same union. -/
theorem RelFieldOfNorms.existsUnique_finite_subfield_preimage :
    ∀ (D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω))
      [FiniteDimensional (FieldOfNorms K L) D],
      ∃! N : FiniteIntermediateField L Ω,
        RelFieldOfNorms.finiteImage K L Ω N = D := by
  intro D _
  obtain ⟨N, hN⟩ := RelFieldOfNorms.exists_finite_subfield_preimage K L Ω D
  refine ⟨N, hN, fun R hR => ?_⟩
  exact RelFieldOfNorms.finiteImage_injective K L Ω (hR.trans hN.symm)

end NormUnion

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every finite separable extension of the norm field is
isomorphic over that same field to a finite norm-field stage in
the prescribed separable closure. -/
theorem exists_finite_fieldOfNorms_algEquiv_of_separableClosure :
    ∀ (F : Type*) [Field F] [Algebra (FieldOfNorms K L) F]
      [Module.Finite (FieldOfNorms K L) F] [Algebra.IsSeparable (FieldOfNorms K L) F],
      ∃ N : FiniteIntermediateField L Ω,
        Nonempty (FieldOfNorms K N.val ≃ₐ[FieldOfNorms K L] F) := by
  intro F _ _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let : IsSepClosed (RelFieldOfNorms K L Ω) :=
    RelFieldOfNorms.isSepClosed K L Ω
  let t : F →ₐ[FieldOfNorms K L] RelFieldOfNorms K L Ω := IsSepClosed.lift
  let : Module.Finite (FieldOfNorms K L) t.fieldRange :=
    Module.Finite.equiv t.equivFieldRange.toLinearEquiv
  obtain ⟨N, hN, _⟩ := RelFieldOfNorms.existsUnique_finite_subfield_preimage
    K L Ω t.fieldRange
  let i := RelFieldOfNorms.ofAlgHom K L Ω N
  refine ⟨N, ⟨i.equivFieldRange.trans ((IntermediateField.equivOfEq hN).trans
    t.equivFieldRange.symm)⟩⟩

/-- Without prescribing a separable closure, every finite
separable target is still a finite norm-field stage. -/
theorem exists_finite_fieldOfNorms_algEquiv :
    ∀ (F : Type*) [Field F] [Algebra (FieldOfNorms K L) F]
      [Module.Finite (FieldOfNorms K L) F] [Algebra.IsSeparable (FieldOfNorms K L) F],
      ∃ N : FiniteIntermediateField L (SeparableClosure L),
        Nonempty (FieldOfNorms K N.val ≃ₐ[FieldOfNorms K L] F) := by
  intro F _ _ _ _
  exact exists_finite_fieldOfNorms_algEquiv_of_separableClosure
    K L (SeparableClosure L) F

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

section DirectedFields

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

/-- Every finite subfield of a directed union lies in a single
member, by the compactness of its finitely generated intermediate field. -/
theorem FiniteIntermediateField.exists_le_of_le_directed_iSup {ι : Type*} [Nonempty ι]
    (A : ι → IntermediateField L Ω) (hA : Directed (· ≤ ·) A)
    (Q : FiniteIntermediateField L Ω) (hQ : Q.val ≤ ⨆ i, A i) :
    ∃ i, Q.val ≤ A i := by
  have hfg : Q.val.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  have hc : IsCompactElement Q.val :=
    hs ▸ IntermediateField.adjoin_finset_isCompactElement s
  obtain ⟨B, ⟨i, rfl⟩, hi⟩ := hc (Set.range A) (⨆ i, A i)
    (Set.range_nonempty A) hA.directedOn_range isLUB_iSup hQ
  exact ⟨i, hi⟩

end DirectedFields

section Images

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A finite subfield contained in an intermediate field
has its entire canonical norm-field image in that intermediate union's
inclusion map. -/
theorem RelFieldOfNorms.finiteImage_le_fieldRange_of_le
    (M : IntermediateField L Ω) (N : FiniteIntermediateField L Ω) (hNM : N.val ≤ M) :
    RelFieldOfNorms.finiteImage K L Ω N ≤
      (RelFieldOfNorms.algMap K L M Ω M.val).fieldRange := by
  let Q₀ := N.val.comap M.val
  let q : Q₀ →ₐ[L] N.val :=
    { toFun := fun a => ⟨(a.val : Ω), a.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      commutes' _ := rfl }
  have hq : Function.Surjective q := by
    intro a
    exact ⟨⟨⟨a.val, hNM a.property⟩, a.property⟩, rfl⟩
  let e := AlgEquiv.ofBijective q ⟨q.injective, hq⟩
  have : Module.Finite L Q₀ := Module.Finite.equiv e.symm.toLinearEquiv
  let Q : FiniteIntermediateField L M := ⟨Q₀, this⟩
  have hmap : FiniteIntermediateField.map M.val Q = N := by
    apply Subtype.ext
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨a, hNM ha⟩, ha, rfl⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_relFieldOfNormsFiniteImage K L Ω N z).mp hz
  obtain ⟨b, hb⟩ := (FieldOfNorms.mapEquiv (e.restrictScalars K)).surjective a
  refine ⟨RelFieldOfNorms.of K L M Q b, ?_⟩
  change RelFieldOfNorms.mapEquiv K L M Ω M.val
    (RelFieldOfNorms.of K L M Q b) = _
  rw [RelFieldOfNorms.map_of, RelFieldOfNorms.stageMap_apply]
  have h := RelFieldOfNorms.of_transport_congr K L Ω
    (FiniteIntermediateField.map M.val Q) N ((FiniteIntermediateField.equivMap M.val
        Q).restrictScalars K)
    (e.restrictScalars K) hmap (fun _ => rfl) b
  exact h.trans (congrArg (RelFieldOfNorms.of K L Ω N) hb)

end Images

section Reconstruction

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every intermediate field of the same canonical closure union
is the image of the relative field of norms of an intermediate
field. The field is the directed supremum of the unique finite
preimages, with inclusion supplied by finite reconstruction. -/
theorem RelFieldOfNorms.exists_subfield_preimage :
    ∀ D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω),
      ∃ M : IntermediateField L Ω,
        (RelFieldOfNorms.algMap K L M Ω M.val).fieldRange = D := by
  classical
  let : Algebra.IsSeparable (FieldOfNorms K L) (RelFieldOfNorms K L Ω) :=
    RelFieldOfNorms.isSeparable K L Ω
  intro D
  have hpre (P : FiniteIntermediateField (FieldOfNorms K L) D) :
      ∃ N : FiniteIntermediateField L Ω, RelFieldOfNorms.finiteImage K L Ω N =
        (FiniteIntermediateField.map D.val P).val := by
    exact (RelFieldOfNorms.existsUnique_finite_subfield_preimage
      K L Ω (FiniteIntermediateField.map D.val P).val).exists
  choose A hA using hpre
  have hmono : Monotone A := by
    intro P Q hPQ
    apply (RelFieldOfNorms.finiteImage_le_iff K L Ω (A P) (A Q)).mp
    rw [hA P, hA Q]
    exact FiniteIntermediateField.map_mono D.val hPQ
  have hdir : Directed (· ≤ ·) (fun P => (A P).val) := by
    intro P Q
    exact ⟨FiniteIntermediateField.sup P Q, hmono (FiniteIntermediateField.le_sup_left P Q),
      hmono (FiniteIntermediateField.le_sup_right P Q)⟩
  let M : IntermediateField L Ω := ⨆ P, (A P).val
  let j := RelFieldOfNorms.algMap K L M Ω M.val
  refine ⟨M, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨Q, a, rfl⟩ := RelFieldOfNorms.exists_stage K L M x
    let Q' := FiniteIntermediateField.map M.val Q
    have hQ' : Q'.val ≤ M := by
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    obtain ⟨P, hQP⟩ := FiniteIntermediateField.exists_le_of_le_directed_iSup
      (fun P => (A P).val) hdir Q' hQ'
    have hQA := (RelFieldOfNorms.finiteImage_le_iff K L Ω Q' (A P)).mpr hQP
    have hAD : RelFieldOfNorms.finiteImage K L Ω (A P) ≤ D := by
      rw [hA P]
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    apply hAD
    apply hQA
    change RelFieldOfNorms.mapEquiv K L M Ω M.val
      (RelFieldOfNorms.of K L M Q a) ∈ _
    rw [RelFieldOfNorms.map_of]
    exact (mem_relFieldOfNormsFiniteImage K L Ω Q' _).mpr ⟨_, rfl⟩
  · intro hz
    obtain ⟨P, hP⟩ := FiniteIntermediateField.exists_mem (L := FieldOfNorms K L) (M := D) ⟨z, hz⟩
    have hzP : z ∈ (FiniteIntermediateField.map D.val P).val := ⟨⟨z, hz⟩, hP, rfl⟩
    have hzA : z ∈ RelFieldOfNorms.finiteImage K L Ω (A P) :=
      (hA P).symm ▸ hzP
    exact RelFieldOfNorms.finiteImage_le_fieldRange_of_le
      K L Ω M (A P) (le_iSup (fun P => (A P).val) P) hzA

/-- Every separable algebraic target is the same relative field of norms
of an intermediate field in the prescribed separable
closure. Both identifications are the canonical image maps. -/
theorem exists_relFieldOfNorms_algEquiv_of_separableClosure :
    ∀ (F : Type*) [Field F] [Algebra (FieldOfNorms K L) F]
      [Algebra.IsSeparable (FieldOfNorms K L) F],
      ∃ M : IntermediateField L Ω,
        Nonempty (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] F) := by
  intro F _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let : IsSepClosed (RelFieldOfNorms K L Ω) :=
    RelFieldOfNorms.isSepClosed K L Ω
  let t : F →ₐ[FieldOfNorms K L] RelFieldOfNorms K L Ω := IsSepClosed.lift
  obtain ⟨M, hM⟩ := RelFieldOfNorms.exists_subfield_preimage
    K L Ω t.fieldRange
  let j := RelFieldOfNorms.algMap K L M Ω M.val
  exact ⟨M, ⟨j.equivFieldRange.trans ((IntermediateField.equivOfEq hM).trans
    t.equivFieldRange.symm)⟩⟩

/-- The algebraic essential image with no prescribed
closure: the standard separable closure supplies that choice. -/
theorem exists_relFieldOfNorms_algEquiv
    (F : Type*) [Field F] [Algebra (FieldOfNorms K L) F]
    [Algebra.IsSeparable (FieldOfNorms K L) F] :
    ∃ M : IntermediateField L (SeparableClosure L),
      Nonempty (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] F) :=
  exists_relFieldOfNorms_algEquiv_of_separableClosure
    K L (SeparableClosure L) F

end Reconstruction

end FontaineWintenberger
