/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.AbsoluteBaseAction
public import FontaineWintenberger.FieldOfNorms.SeparableNormUnion

/-!
# The ambient action on the original relative field of norms

Normality of the actual base intermediate field makes ambient automorphisms
transport its finite overfields to actual finite overfields. The resulting
original norm-field maps act on the same directed union.

Reference: the finite-subextension action in Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [Normal K L]

/-- Normality makes every actual ambient image contain the same base field. -/
theorem RelFieldOfNorms.absoluteImage_contains (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    L ≤ (N.val.restrictScalars K).map σ.toAlgHom := by
  intro z hz
  refine ⟨(((σ.restrictNormal L).symm ⟨z, hz⟩ : L) : M), ?_, ?_⟩
  · exact N.val.algebraMap_mem _
  · change σ (((σ.restrictNormal L).symm ⟨z, hz⟩ : L) : M) = z
    simpa only [AlgEquiv.apply_symm_apply] using
      (AlgEquiv.restrictNormal_apply L σ ((σ.restrictNormal L).symm ⟨z, hz⟩)).symm

/-- The actual ambient image, retaining its underlying original subfield. -/
def RelFieldOfNorms.absoluteLayerField (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    IntermediateField L M :=
  IntermediateField.extendScalars (RelFieldOfNorms.absoluteImage_contains K M L σ N)

/-- Semilinear transport along the actual base automorphism preserves finite degree. -/
theorem RelFieldOfNorms.absoluteLayer_finite (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    Module.Finite L (RelFieldOfNorms.absoluteLayerField K M L σ N) := by
  let e : N.val ≃ₐ[K] (RelFieldOfNorms.absoluteLayerField K M L σ N) :=
    IntermediateField.equivMap (N.val.restrictScalars K) σ.toAlgHom
  apply Module.Finite.of_equiv_equiv (σ.restrictNormal L).toRingEquiv e.toRingEquiv
  apply RingHom.ext
  intro a
  exact Subtype.ext (AlgEquiv.restrictNormal_commutes σ L a)

/-- The actual finite image index over the same normal base. -/
def RelFieldOfNorms.absoluteLayer (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    FiniteIntermediateField L M :=
  ⟨RelFieldOfNorms.absoluteLayerField K M L σ N, RelFieldOfNorms.absoluteLayer_finite K M L σ N⟩

/-- Restrict the original ambient automorphism to its actual image field. -/
def RelFieldOfNorms.absoluteLayerEquiv (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) :
    N.val ≃ₐ[K] (RelFieldOfNorms.absoluteLayer K M L σ N).val :=
  IntermediateField.equivMap (N.val.restrictScalars K) σ.toAlgHom

/-- The restricted map is literally the original automorphism in the ambient field. -/
@[simp]
theorem coe_relFieldOfNormsAbsoluteLayerEquiv (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M)
    (x : N.val) :
    (RelFieldOfNorms.absoluteLayerEquiv K M L σ N x : M) = σ (x : M) := rfl

/-- Membership in the original image index is literal ambient image membership. -/
@[simp]
theorem mem_relFieldOfNormsAbsoluteLayer (σ : M ≃ₐ[K] M) (N : FiniteIntermediateField L M) (z : M) :
    z ∈ (RelFieldOfNorms.absoluteLayer K M L σ N).val ↔ ∃ x ∈ N.val, σ x = z := Iff.rfl

/-- Ambient transport preserves inclusions of the actual finite overfields. -/
theorem RelFieldOfNorms.absoluteLayer_mono (σ : M ≃ₐ[K] M) {N P : FiniteIntermediateField L M}
    (hNP : N ≤ P) :
    RelFieldOfNorms.absoluteLayer K M L σ N ≤ RelFieldOfNorms.absoluteLayer K M L σ P := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hNP hx, rfl⟩

/-- The actual identity ambient automorphism leaves every finite image index unchanged. -/
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

/-- Ambient multiplication gives the same original iterated finite image. -/
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

/-- A field isomorphism between actual finite indices gives their original norm-field
isomorphism. -/
def RelFieldOfNorms.stageEquiv (N P : FiniteIntermediateField L M) (e : N.val ≃ₐ[K] P.val) :
    FieldOfNorms K N.val ≃+* FieldOfNorms K P.val := by
  exact FieldOfNorms.ringEquiv K (L := N.val) (M := P.val)
    e

/-- The indexed isomorphism is the original norm-family transport. -/
@[simp]
theorem RelFieldOfNorms.stageEquiv_apply (N P : FiniteIntermediateField L M) (e : N.val ≃ₐ[K] P.val)
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageEquiv K L M N P e x = FieldOfNorms.map e x := rfl

/-- An original commuting field square gives the same original finite base maps. -/
theorem RelFieldOfNorms.stageEquiv_base (N P : FiniteIntermediateField L M)
    (a : L ≃ₐ[K] L) (e : N.val ≃ₐ[K] P.val)
    (h : ∀ z : L, e (algebraMap L N.val z) = algebraMap L P.val (a z))
    (x : FieldOfNorms K L) :
    FieldOfNorms.map e (RelFieldOfNorms.baseToStage K L M N x) =
      RelFieldOfNorms.baseToStage K L M P (FieldOfNorms.map a x) := by
  simpa only [RelFieldOfNorms.baseToStage, FieldOfNorms.finiteRingHom_apply] using
    FieldOfNorms.finiteMap_naturality K (M := L) (N := N.val) (M' := L) (N' := P.val)
      a e h x

/-- Commuting original stage equivalences preserve the original inclusion maps. -/
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

/-- The actual ambient restriction gives the existing isomorphism of original norm fields. -/
def RelFieldOfNorms.absoluteStageMap (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) :
    FieldOfNorms K N.val ≃+*
      FieldOfNorms K (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N).val := by
  exact RelFieldOfNorms.stageEquiv K L (SeparableClosure K) N
    (RelFieldOfNorms.absoluteLayer K (SeparableClosure K) L σ N)
    (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N)

/-- The finite-stage action is the literal original norm-family transport. -/
@[simp]
theorem RelFieldOfNorms.absoluteStageMap_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteIntermediateField L (SeparableClosure K)) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.absoluteStageMap K L σ N x =
      FieldOfNorms.map (RelFieldOfNorms.absoluteLayerEquiv K (SeparableClosure K) L σ N) x :=
  RelFieldOfNorms.stageEquiv_apply K L (SeparableClosure K) N _ _ x

/-- Actual ambient stage transport extends the original absolute base action. -/
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

/-- Actual ambient stage transport commutes with every original finite inclusion. -/
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
