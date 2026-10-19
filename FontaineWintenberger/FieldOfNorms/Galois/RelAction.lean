/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Galois.Action
public import FontaineWintenberger.FieldOfNorms.Relative.Defs

/-!
# The ambient Galois action on the relative field of norms

## The ambient action on the relative field of norms

Normality of the base intermediate field makes ambient automorphisms
transport its finite overfields to finite overfields. The resulting
norm-field maps act on the same directed union.

Reference: the finite-subextension action in Wintenberger, Remark 3.2.4.

## Valuations under finite-stage isomorphisms

A commuting base square identifies the positive normalization
exponents, so the same stage isomorphism preserves rational valuations.

Reference: Wintenberger, Remark 3.2.4, the finite-stage valuation argument.

## The ambient action on the relative field of norms

Ambient finite-image transports descend to the same relative field of norms.
They extend the absolute base action and preserve its rational valuation.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]

/-- Normality makes every ambient image contain the same base field. -/
theorem RelFieldOfNorms.absoluteImage_contains (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    L ≤ (N.val.restrictScalars K).map σ.toAlgHom := by
  intro z hz
  refine ⟨(((σ.restrictNormal L).symm ⟨z, hz⟩ : L) : M), ?_, ?_⟩
  · exact N.val.algebraMap_mem _
  · change σ (((σ.restrictNormal L).symm ⟨z, hz⟩ : L) : M) = z
    simpa only [AlgEquiv.apply_symm_apply] using
      (AlgEquiv.restrictNormal_apply L σ ((σ.restrictNormal L).symm ⟨z, hz⟩)).symm

/-- The ambient image, retaining its underlying subfield. -/
def RelFieldOfNorms.absoluteLayerField (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    IntermediateField L M :=
  IntermediateField.extendScalars (RelFieldOfNorms.absoluteImage_contains K M L σ N)

/-- Semilinear transport along the base automorphism preserves finite degree. -/
theorem RelFieldOfNorms.absoluteLayer_finite (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    Module.Finite L (RelFieldOfNorms.absoluteLayerField K M L σ N) := by
  let e : N.val ≃ₐ[K] (RelFieldOfNorms.absoluteLayerField K M L σ N) :=
    IntermediateField.equivMap (N.val.restrictScalars K) σ.toAlgHom
  apply Module.Finite.of_equiv_equiv (σ.restrictNormal L).toRingEquiv e.toRingEquiv
  apply RingHom.ext
  intro a
  exact Subtype.ext (AlgEquiv.restrictNormal_commutes σ L a)

/-- The finite image index over the same normal base. -/
def RelFieldOfNorms.absoluteLayer (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    FiniteIntermediateField L M :=
  ⟨RelFieldOfNorms.absoluteLayerField K M L σ N, RelFieldOfNorms.absoluteLayer_finite K M L σ N⟩

/-- Restrict the ambient automorphism to its image field. -/
def RelFieldOfNorms.absoluteLayerEquiv (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    N.val ≃ₐ[K] (RelFieldOfNorms.absoluteLayer K M L σ N).val :=
  IntermediateField.equivMap (N.val.restrictScalars K) σ.toAlgHom

/-- The restricted map is the automorphism in the ambient field. -/
@[simp]
theorem coe_relFieldOfNormsAbsoluteLayerEquiv (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M)
    (x : N.val) :
    (RelFieldOfNorms.absoluteLayerEquiv K M L σ N x : M) = σ (x : M) := rfl

/-- Membership in the image index is ambient image membership. -/
@[simp]
theorem mem_relFieldOfNormsAbsoluteLayer (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) (z : M) :
    z ∈ (RelFieldOfNorms.absoluteLayer K M L σ N).val ↔ ∃ x ∈ N.val, σ x = z := Iff.rfl

/-- Ambient transport preserves inclusions of the finite overfields. -/
theorem RelFieldOfNorms.absoluteLayer_mono (σ : M ≃ₐ[K] M) {N P : FiniteIntermediateField L M}
    (hNP : N ≤ P) :
    RelFieldOfNorms.absoluteLayer K M L σ N ≤ RelFieldOfNorms.absoluteLayer K M L σ P := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hNP hx, rfl⟩

/-- The identity ambient automorphism leaves every finite image index unchanged. -/
@[simp]
theorem RelFieldOfNorms.absoluteLayer_one (N : FiniteIntermediateField L M) :
    RelFieldOfNorms.absoluteLayer K M L 1 N = N := by
  apply Subtype.ext
  apply SetLike.ext
  intro z
  change (∃ x ∈ N.val, x = z) ↔ z ∈ N.val
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Ambient multiplication gives the iterated finite image. -/
theorem RelFieldOfNorms.absoluteLayer_mul (σ τ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    RelFieldOfNorms.absoluteLayer K M L (σ * τ) N =
      RelFieldOfNorms.absoluteLayer K M L σ (RelFieldOfNorms.absoluteLayer K M L τ N) := by
  apply Subtype.ext
  apply SetLike.ext
  intro z
  change (∃ x ∈ N.val, σ (τ x) = z) ↔
    ∃ y, (∃ x ∈ N.val, τ x = y) ∧ σ y = z
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨τ x, ⟨x, hx, rfl⟩, h⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, h⟩
    exact ⟨x, hx, h⟩

end Fields

section StageEquivNaturality

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A field isomorphism between finite indices gives their norm-field
isomorphism. -/
def RelFieldOfNorms.stageEquiv (N P : FiniteIntermediateField L M) (e : N.val ≃ₐ[K] P.val) :
    FieldOfNorms K N.val ≃+* FieldOfNorms K P.val := by
  exact FieldOfNorms.ringEquiv K (L := N.val) (M := P.val)
    e

/-- The indexed isomorphism is the norm-family transport. -/
@[simp]
theorem RelFieldOfNorms.stageEquiv_apply (N P : FiniteIntermediateField L M) (e : N.val ≃ₐ[K] P.val)
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageEquiv K L M N P e x = FieldOfNorms.map e x := rfl

/-- A commuting field square gives the finite base maps. -/
theorem RelFieldOfNorms.stageEquiv_base (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : FieldOfNorms K L) :
    FieldOfNorms.map e (RelFieldOfNorms.baseToStage K L M N x) =
      RelFieldOfNorms.baseToStage K L M P (FieldOfNorms.map a x) := by
  simpa only [RelFieldOfNorms.baseToStage, FieldOfNorms.finiteRingHom_apply] using
    FieldOfNorms.finiteMap_naturality K (M := L) (N := N.val) (M' := L) (N' := P.val)
      a e h x

/-- Commuting stage equivalences preserve the inclusion maps. -/
theorem RelFieldOfNorms.stageEquiv_transition (N P A B : FiniteIntermediateField L M)
    (hNP : N ≤ P) (hAB : A ≤ B)
    (eN : N.val ≃ₐ[K] A.val) (eP : P.val ≃ₐ[K] B.val)
    (h : ∀ z : N.val,
      (eP (IntermediateField.inclusion hNP z) : M) = (eN z : M))
    (x : FieldOfNorms K N.val) :
    FieldOfNorms.map eP
        (RelFieldOfNorms.transition K L M N P hNP x) =
      RelFieldOfNorms.transition K L M A B hAB
        (FieldOfNorms.map eN x) := by
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  let : Algebra A.val B.val := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
  let : IsScalarTower L A.val B.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K A.val B.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite A.val B.val := Module.Finite.right L A.val B.val
  let : Algebra.IsSeparable A.val B.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L A.val B.val
  simpa only [RelFieldOfNorms.transition, FieldOfNorms.finiteRingHom_apply] using
    FieldOfNorms.finiteMap_naturality K
      (M := N.val) (N := P.val) (M' := A.val) (N' := B.val)
      eN eP (fun z => Subtype.ext (h z)) x

end StageEquivNaturality

section NormFields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The ambient restriction gives the existing isomorphism of norm fields. -/
def RelFieldOfNorms.absoluteStageMap (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) :
    FieldOfNorms K N.val ≃+*
      FieldOfNorms K (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N).val := by
  exact RelFieldOfNorms.stageEquiv K L (SeparableClosure K) N
    (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
    (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N)

/-- The finite-stage action is the norm-family transport. -/
@[simp]
theorem RelFieldOfNorms.absoluteStageMap_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteStageMap K L σ N x =
      FieldOfNorms.map (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N) x :=
  RelFieldOfNorms.stageEquiv_apply K L (SeparableClosure K) N _ _ x

/-- Ambient stage transport extends the absolute base action. -/
theorem RelFieldOfNorms.absoluteStageMap_base
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K L) :
    RelFieldOfNorms.absoluteStageMap K L σ N
        (RelFieldOfNorms.baseToStage K L (SeparableClosure K) N x) =
      RelFieldOfNorms.baseToStage K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (FieldOfNorms.absoluteAut K L σ x) := by
  simpa only [RelFieldOfNorms.absoluteStageMap_apply, FieldOfNorms.absoluteAut_apply,
    FieldOfNorms.aut_apply] using
    RelFieldOfNorms.stageEquiv_base K L (SeparableClosure K) N
      (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
      (AlgEquiv.restrictNormalHom L σ)
      (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N)
      (fun a => Subtype.ext (AlgEquiv.restrictNormalHom_apply L σ a).symm) x

/-- Ambient stage transport commutes with every finite inclusion. -/
theorem RelFieldOfNorms.absoluteStageMap_transition
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N P : FiniteIntermediateField L (SeparableClosure K)) (hNP : N ≤ P) (x : FieldOfNorms K N.val)
        :
    RelFieldOfNorms.absoluteStageMap K L σ P
        (RelFieldOfNorms.transition K L (SeparableClosure K) N P hNP x) =
      RelFieldOfNorms.transition K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P)
        (RelFieldOfNorms.absoluteLayer_mono K (SeparableClosure K) L σ hNP)
        (RelFieldOfNorms.absoluteStageMap K L σ N x) := by
  simpa only [RelFieldOfNorms.absoluteStageMap_apply] using
    RelFieldOfNorms.stageEquiv_transition K L (SeparableClosure K) N P
      (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
      (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P)
      hNP (RelFieldOfNorms.absoluteLayer_mono K (SeparableClosure K) L σ hNP)
      (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N)
      (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ P)
      (fun _ => rfl) x

end NormFields

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The commuting square identifies the normalization exponents. -/
theorem RelFieldOfNorms.stageEquiv_exponent (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z)) :
    RelFieldOfNorms.stageExponent K L M P =
      RelFieldOfNorms.stageExponent K L M N := by
  apply RelFieldOfNorms.stageExponent_unique K L M N
  intro x
  change FieldOfNorms.valuation K N.val
      (RelFieldOfNorms.baseToStage K L M N x) = _
  calc
    _ = FieldOfNorms.valuation K P.val
        (FieldOfNorms.map e
          (RelFieldOfNorms.baseToStage K L M N x)) :=
      (FieldOfNorms.valuation_fieldOfNormsMap K
        e _).symm
    _ = FieldOfNorms.valuation K P.val
        (RelFieldOfNorms.baseToStage K L M P (FieldOfNorms.map a x)) :=
      congrArg (FieldOfNorms.valuation K P.val)
        (RelFieldOfNorms.stageEquiv_base K L M N P a e h x)
    _ = FieldOfNorms.valuation K L (FieldOfNorms.map a x) ^
        RelFieldOfNorms.stageExponent K L M P :=
      RelFieldOfNorms.stageExponent_spec K L M P (FieldOfNorms.map a x)
    _ = FieldOfNorms.valuation K L x ^ RelFieldOfNorms.stageExponent K L M P := by
      rw [FieldOfNorms.valuation_fieldOfNormsMap K a x]

/-- A finite-stage isomorphism preserves the same rational valuation. -/
theorem RelFieldOfNorms.stageEquiv_valuation (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageValuation K L M P (FieldOfNorms.map e x) =
      RelFieldOfNorms.stageValuation K L M N x := by
  rw [RelFieldOfNorms.stageValuation_apply, RelFieldOfNorms.stageValuation_apply,
    RelFieldOfNorms.stageEquiv_exponent K L M N P a e h,
    FieldOfNorms.valuation_fieldOfNormsMap K
      e x]

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The compatible finite-stage transports act on the same relative field of norms. -/
def RelFieldOfNorms.absoluteMap
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    RelFieldOfNorms K L (SeparableClosure K) →+*
      RelFieldOfNorms K L (SeparableClosure K) := by
  refine DirectLimit.Ring.lift
    (fun N : FiniteIntermediateField L (SeparableClosure K) => FieldOfNorms K N.val)
    (RelFieldOfNorms.transition K L (SeparableClosure K))
    (RelFieldOfNorms K L (SeparableClosure K))
    (fun N =>
      (RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)).comp
        (RelFieldOfNorms.absoluteStageMap K L σ N).toRingHom) ?_
  intro N P hNP x
  exact (congrArg
    (RelFieldOfNorms.of K L (SeparableClosure K)
      (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P))
    (RelFieldOfNorms.absoluteStageMap_transition K L σ N P hNP x)).trans
      (RelFieldOfNorms.of_transition K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P)
        (RelFieldOfNorms.absoluteLayer_mono K (SeparableClosure K) L σ hNP)
        (RelFieldOfNorms.absoluteStageMap K L σ N x))

/-- On each family, the union map is its ambient finite-image transport. -/
@[simp]
theorem RelFieldOfNorms.absoluteMap_of
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteMap K L σ
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) =
      RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (RelFieldOfNorms.absoluteStageMap K L σ N x) := by
  -- Stated with every argument of `lift_of` explicit: unifying the lemma against the folded
  -- `RelFieldOfNorms.absoluteMap` is what used to cost minutes here.
  have h := DirectLimit.Ring.lift_of
    (G := fun N : FiniteIntermediateField L (SeparableClosure K) => FieldOfNorms K N.val)
    (f := RelFieldOfNorms.transition K L (SeparableClosure K))
    (RelFieldOfNorms K L (SeparableClosure K))
    (fun N =>
      (RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)).comp
        (RelFieldOfNorms.absoluteStageMap K L σ N).toRingHom) (fun N P hNP x =>
    (congrArg
      (RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P))
      (RelFieldOfNorms.absoluteStageMap_transition K L σ N P hNP x)).trans
        (RelFieldOfNorms.of_transition K L (SeparableClosure K)
          (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
          (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ P)
          (RelFieldOfNorms.absoluteLayer_mono K (SeparableClosure K) L σ hNP)
          (RelFieldOfNorms.absoluteStageMap K L σ N x))) N x
  exact h

/-- The identity transport fixes each element of the same union. -/
@[simp]
theorem RelFieldOfNorms.absoluteMap_one_apply
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteMap K L 1 z = z := by
  obtain ⟨N, x, rfl⟩ :=
    RelFieldOfNorms.exists_stage K L (SeparableClosure K) z
  rw [RelFieldOfNorms.absoluteMap_of, RelFieldOfNorms.absoluteStageMap_apply]
  calc
    _ = RelFieldOfNorms.of K L (SeparableClosure K) N
        (FieldOfNorms.map (AlgEquiv.refl : N.val ≃ₐ[K] N.val) x) :=
      RelFieldOfNorms.of_transport_congr K L (SeparableClosure K)
        (D := N.val) (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L 1 N) N
        (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L 1 N)
        (AlgEquiv.refl : N.val ≃ₐ[K] N.val)
        (RelFieldOfNorms.absoluteLayer_one K (SeparableClosure K) L N) (fun _ => rfl) x
    _ = _ := by rw [FieldOfNorms.map_refl]

/-- On a family the ambient map is the norm-family transport. -/
@[simp]
theorem RelFieldOfNorms.absoluteMap_of_fieldOfNormsMap
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteMap K L σ
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) =
      RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (FieldOfNorms.map (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N) x) :=
  (RelFieldOfNorms.absoluteMap_of K L σ N x).trans
    (congrArg
      (RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N))
      (RelFieldOfNorms.absoluteStageMap_apply K L σ N x))

/-- Ambient multiplication is composition on each finite-stage family. -/
theorem RelFieldOfNorms.absoluteMap_mul_of
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteMap K L (σ * τ)
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) =
      RelFieldOfNorms.absoluteMap K L σ
        (RelFieldOfNorms.absoluteMap K L τ
          (RelFieldOfNorms.of K L (SeparableClosure K) N x)) := by
  let A := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L τ N
  let B := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ A
  let C := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L (σ * τ) N
  let a : N.val ≃ₐ[K] A.val :=
    RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L τ N
  let b : A.val ≃ₐ[K] B.val :=
    RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ A
  let c : N.val ≃ₐ[K] C.val :=
    RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L (σ * τ) N
  let j (D : FiniteIntermediateField L (SeparableClosure K)) :
      FieldOfNorms K D.val → RelFieldOfNorms K L (SeparableClosure K) :=
    RelFieldOfNorms.of K L (SeparableClosure K) D
  calc
    _ = j C (FieldOfNorms.map c x) :=
      RelFieldOfNorms.absoluteMap_of_fieldOfNormsMap K L (σ * τ) N x
    _ = j B (FieldOfNorms.map (a.trans b) x) :=
      RelFieldOfNorms.of_transport_congr K L (SeparableClosure K)
        (D := N.val) C B c (a.trans b)
        (RelFieldOfNorms.absoluteLayer_mul K (SeparableClosure K) L σ τ N) (fun _ => rfl) x
    _ = j B (FieldOfNorms.map b (FieldOfNorms.map a x)) :=
      congrArg (j B) (FieldOfNorms.map_trans a b x).symm
    _ = RelFieldOfNorms.absoluteMap K L σ
        (j A (FieldOfNorms.map a x)) :=
      (RelFieldOfNorms.absoluteMap_of_fieldOfNormsMap K L σ A
        (FieldOfNorms.map a x)).symm
    _ = _ := congrArg (RelFieldOfNorms.absoluteMap K L σ)
      (RelFieldOfNorms.absoluteMap_of_fieldOfNormsMap K L τ N x).symm

/-- Ambient multiplication is composition on every union element. -/
theorem RelFieldOfNorms.absoluteMap_mul_apply
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteMap K L (σ * τ) z =
      RelFieldOfNorms.absoluteMap K L σ
        (RelFieldOfNorms.absoluteMap K L τ z) := by
  obtain ⟨N, x, hx⟩ :=
    RelFieldOfNorms.exists_stage K L (SeparableClosure K) z
  exact (congrArg (RelFieldOfNorms.absoluteMap K L (σ * τ)) hx.symm).trans
    ((RelFieldOfNorms.absoluteMap_mul_of K L σ τ N x).trans
      (congrArg
        (fun y => RelFieldOfNorms.absoluteMap K L σ
          (RelFieldOfNorms.absoluteMap K L τ y)) hx))

/-- The ambient transports form an automorphism action on the same union. -/
def RelFieldOfNorms.absoluteAut :
    letI : Group (RingAut (RelFieldOfNorms K L (SeparableClosure K))) :=
        RingAut.instGroup _
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →*
      (RelFieldOfNorms K L (SeparableClosure K) ≃+*
        RelFieldOfNorms K L (SeparableClosure K)) :=
  letI : Group (RingAut (RelFieldOfNorms K L (SeparableClosure K))) :=
      RingAut.instGroup _
  let f (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      RelFieldOfNorms K L (SeparableClosure K) ≃+*
        RelFieldOfNorms K L (SeparableClosure K) :=
    RingEquiv.ofRingHom
      (RelFieldOfNorms.absoluteMap K L σ)
      (RelFieldOfNorms.absoluteMap K L σ⁻¹)
      (RingHom.ext (fun z =>
        (RelFieldOfNorms.absoluteMap_mul_apply K L σ σ⁻¹ z).symm.trans
          ((congrArg
            (fun δ => RelFieldOfNorms.absoluteMap K L δ z)
            (mul_inv_cancel σ)).trans
              (RelFieldOfNorms.absoluteMap_one_apply K L z))))
      (RingHom.ext (fun z =>
        (RelFieldOfNorms.absoluteMap_mul_apply K L σ⁻¹ σ z).symm.trans
          ((congrArg
            (fun δ => RelFieldOfNorms.absoluteMap K L δ z)
            (inv_mul_cancel σ)).trans
              (RelFieldOfNorms.absoluteMap_one_apply K L z))))
  { toFun := f
    map_one' := RingEquiv.ext
      (fun z => RelFieldOfNorms.absoluteMap_one_apply K L z)
    map_mul' := fun σ τ => RingEquiv.ext
      (fun z => RelFieldOfNorms.absoluteMap_mul_apply K L σ τ z) }

/-- Bundling as automorphisms retains the union map. -/
@[simp]
theorem RelFieldOfNorms.absoluteAut_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteAut K L σ z =
      RelFieldOfNorms.absoluteMap K L σ z := rfl

/-- Each finite-stage family is transported by the ambient automorphism. -/
@[simp]
theorem RelFieldOfNorms.absoluteAut_of
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteAut K L σ
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) =
      RelFieldOfNorms.of K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
        (FieldOfNorms.map (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N) x) :=
  (RelFieldOfNorms.absoluteAut_apply K L σ
    (RelFieldOfNorms.of K L (SeparableClosure K) N x)).trans
      (RelFieldOfNorms.absoluteMap_of_fieldOfNormsMap K L σ N x)

/-- The ambient union action extends the absolute action on the base norm field. -/
theorem RelFieldOfNorms.absoluteAut_base
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : FieldOfNorms K L) :
    RelFieldOfNorms.absoluteAut K L σ
        (RelFieldOfNorms.baseHom K L (SeparableClosure K) x) =
      RelFieldOfNorms.baseHom K L (SeparableClosure K)
        (FieldOfNorms.absoluteAut K L σ x) := by
  let N : FiniteIntermediateField L (SeparableClosure K) := FiniteIntermediateField.bottom
  let P := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N
  let i : FieldOfNorms K L → FieldOfNorms K N.val :=
    RelFieldOfNorms.baseToStage K L (SeparableClosure K) N
  let j (D : FiniteIntermediateField L (SeparableClosure K)) :
      FieldOfNorms K D.val → RelFieldOfNorms K L (SeparableClosure K) :=
    RelFieldOfNorms.of K L (SeparableClosure K) D
  have hx : j N (i x) =
      RelFieldOfNorms.baseHom K L (SeparableClosure K) x :=
    RelFieldOfNorms.of_base K L (SeparableClosure K) N x
  calc
    _ = RelFieldOfNorms.absoluteAut K L σ (j N (i x)) :=
      congrArg (RelFieldOfNorms.absoluteAut K L σ) hx.symm
    _ = j P (RelFieldOfNorms.absoluteStageMap K L σ N (i x)) :=
      (RelFieldOfNorms.absoluteAut_apply K L σ (j N (i x))).trans
        (RelFieldOfNorms.absoluteMap_of K L σ N (i x))
    _ = j P (RelFieldOfNorms.baseToStage K L (SeparableClosure K) P
        (FieldOfNorms.absoluteAut K L σ x)) :=
      congrArg (j P) (RelFieldOfNorms.absoluteStageMap_base K L σ N x)
    _ = _ := RelFieldOfNorms.of_base K L (SeparableClosure K) P
      (FieldOfNorms.absoluteAut K L σ x)

/-- The relative functor map agrees with ambient transport on every finite family. -/
theorem RelFieldOfNorms.absoluteAut_restrictScalars_of
    (τ :
      letI : Semiring (SeparableClosure K) :=
        @CommSemiring.toSemiring (SeparableClosure K)
        (@Semifield.toCommSemiring (SeparableClosure K)
          (@Field.toSemifield (SeparableClosure K)
            (separableClosure K (AlgebraicClosure K)).toField))
      SeparableClosure K ≃ₐ[L] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteAut K L (τ.restrictScalars K)
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) =
      RelFieldOfNorms.map K L (SeparableClosure K)
        (SeparableClosure K) τ.toAlgHom
        (RelFieldOfNorms.of K L (SeparableClosure K) N x) := by
  let P := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L (τ.restrictScalars K) N
  let Q := FiniteIntermediateField.map τ.toAlgHom N
  let e : N.val ≃ₐ[K] P.val :=
    RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L (τ.restrictScalars K) N
  let f : N.val ≃ₐ[K] Q.val :=
    (FiniteIntermediateField.equivMap τ.toAlgHom N).restrictScalars K
  let j (D : FiniteIntermediateField L (SeparableClosure K)) :
      FieldOfNorms K D.val → RelFieldOfNorms K L (SeparableClosure K) :=
    RelFieldOfNorms.of K L (SeparableClosure K) D
  have hPQ : P = Q := by
    apply Subtype.ext
    apply SetLike.ext
    intro z
    change (∃ a ∈ N.val, τ a = z) ↔ ∃ a ∈ N.val, τ a = z
    rfl
  calc
    _ = j P (FieldOfNorms.map e x) :=
      RelFieldOfNorms.absoluteAut_of K L (τ.restrictScalars K) N x
    _ = j Q (FieldOfNorms.map f x) :=
      RelFieldOfNorms.of_transport_congr K L (SeparableClosure K)
        (D := N.val) P Q e f hPQ (fun _ => rfl) x
    _ = _ :=
      ((RelFieldOfNorms.map_of K L (SeparableClosure K)
        (SeparableClosure K) τ.toAlgHom N x).trans
        (congrArg (j Q)
          (RelFieldOfNorms.stageMap_apply K L (SeparableClosure K)
            (SeparableClosure K) τ.toAlgHom N x))).symm

/-- On the relative absolute Galois subgroup, ambient transport is the functor map. -/
theorem RelFieldOfNorms.absoluteAut_restrictScalars
    (τ :
      letI : Semiring (SeparableClosure K) :=
        @CommSemiring.toSemiring (SeparableClosure K)
        (@Semifield.toCommSemiring (SeparableClosure K)
          (@Field.toSemifield (SeparableClosure K)
            (separableClosure K (AlgebraicClosure K)).toField))
      SeparableClosure K ≃ₐ[L] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteAut K L (τ.restrictScalars K) z =
      RelFieldOfNorms.map K L (SeparableClosure K)
        (SeparableClosure K) τ.toAlgHom z := by
  obtain ⟨N, x, hx⟩ :=
    RelFieldOfNorms.exists_stage K L (SeparableClosure K) z
  exact (congrArg
    (RelFieldOfNorms.absoluteAut K L (τ.restrictScalars K)) hx.symm).trans
      ((RelFieldOfNorms.absoluteAut_restrictScalars_of K L τ N x).trans
        (congrArg
          (RelFieldOfNorms.map K L (SeparableClosure K)
            (SeparableClosure K) τ.toAlgHom) hx))

/-- The absolute Galois action preserves the rational union valuation. -/
theorem RelFieldOfNorms.absoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.valuation K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteAut K L σ z) =
      RelFieldOfNorms.valuation K L (SeparableClosure K) z := by
  obtain ⟨N, x, hx⟩ :=
    RelFieldOfNorms.exists_stage K L (SeparableClosure K) z
  let P := RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N
  let e := RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N
  let v := RelFieldOfNorms.valuation K L (SeparableClosure K)
  have hstage :
      v (RelFieldOfNorms.absoluteAut K L σ
        (RelFieldOfNorms.of K L (SeparableClosure K) N x)) =
      v (RelFieldOfNorms.of K L (SeparableClosure K) N x) := by
    calc
      _ = v (RelFieldOfNorms.of K L (SeparableClosure K) P
          (FieldOfNorms.map e x)) :=
        congrArg v (RelFieldOfNorms.absoluteAut_of K L σ N x)
      _ = RelFieldOfNorms.stageValuation K L (SeparableClosure K) P
          (FieldOfNorms.map e x) :=
        RelFieldOfNorms.valuation_of K L (SeparableClosure K) P
          (FieldOfNorms.map e x)
      _ = RelFieldOfNorms.stageValuation K L (SeparableClosure K) N x :=
        RelFieldOfNorms.stageEquiv_valuation K L (SeparableClosure K) N P
          (AlgEquiv.restrictNormalHom L σ) e
          (fun a => Subtype.ext (AlgEquiv.restrictNormalHom_apply L σ a).symm) x
      _ = _ :=
        (RelFieldOfNorms.valuation_of K L (SeparableClosure K) N x).symm
  exact (congrArg (fun y => v (RelFieldOfNorms.absoluteAut K L σ y))
    hx.symm).trans (hstage.trans (congrArg v hx))

end FontaineWintenberger
