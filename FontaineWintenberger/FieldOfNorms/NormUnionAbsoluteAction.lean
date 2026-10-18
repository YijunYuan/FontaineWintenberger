/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteStages
public import FontaineWintenberger.FieldOfNorms.NormUnionStageValuation

/-!
# The ambient action on the original relative field of norms

Actual ambient finite-image transports descend to the same relative field of norms.
They extend the original absolute base action and preserve its rational valuation.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The compatible original finite-stage transports act on the same relative field of norms. -/
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

/-- On each original family, the union map is its actual ambient finite-image transport. -/
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

/-- The original identity transport fixes each element of the same union. -/
@[simp]
theorem RelFieldOfNorms.absoluteMap_one_apply
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteMap K L 1 z = z := by
  obtain ⟨N, x, rfl⟩ :=
    RelFieldOfNorms._exists_stage K L (SeparableClosure K) z
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

/-- On an original family the ambient map is the original norm-family transport. -/
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

/-- Ambient multiplication is composition on each original finite-stage family. -/
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

/-- Original ambient multiplication is composition on every union element. -/
theorem RelFieldOfNorms.absoluteMap_mul_apply
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteMap K L (σ * τ) z =
      RelFieldOfNorms.absoluteMap K L σ
        (RelFieldOfNorms.absoluteMap K L τ z) := by
  obtain ⟨N, x, hx⟩ :=
    RelFieldOfNorms._exists_stage K L (SeparableClosure K) z
  exact (congrArg (RelFieldOfNorms.absoluteMap K L (σ * τ)) hx.symm).trans
    ((RelFieldOfNorms.absoluteMap_mul_of K L σ τ N x).trans
      (congrArg
        (fun y => RelFieldOfNorms.absoluteMap K L σ
          (RelFieldOfNorms.absoluteMap K L τ y)) hx))

/-- The original ambient transports form an automorphism action on the same union. -/
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

/-- Bundling as automorphisms retains the literal original union map. -/
@[simp]
theorem RelFieldOfNorms.absoluteAut_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.absoluteAut K L σ z =
      RelFieldOfNorms.absoluteMap K L σ z := rfl

/-- Each original finite-stage family is transported by the original ambient automorphism. -/
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

/-- The ambient union action extends the original absolute action on the base norm field. -/
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

/-- The original relative functor map agrees with ambient transport on every finite family. -/
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

/-- On the original relative absolute Galois subgroup, ambient transport is the functor map. -/
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
    RelFieldOfNorms._exists_stage K L (SeparableClosure K) z
  exact (congrArg
    (RelFieldOfNorms.absoluteAut K L (τ.restrictScalars K)) hx.symm).trans
      ((RelFieldOfNorms.absoluteAut_restrictScalars_of K L τ N x).trans
        (congrArg
          (RelFieldOfNorms.map K L (SeparableClosure K)
            (SeparableClosure K) τ.toAlgHom) hx))

/-- The actual absolute Galois action preserves the original rational union valuation. -/
theorem RelFieldOfNorms.absoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : RelFieldOfNorms K L (SeparableClosure K)) :
    RelFieldOfNorms.valuation K L (SeparableClosure K)
        (RelFieldOfNorms.absoluteAut K L σ z) =
      RelFieldOfNorms.valuation K L (SeparableClosure K) z := by
  obtain ⟨N, x, hx⟩ :=
    RelFieldOfNorms._exists_stage K L (SeparableClosure K) z
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
