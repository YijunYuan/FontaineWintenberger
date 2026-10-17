module

public import FontaineWintenberger.FieldOfNorms.NormUnionAbsoluteStages
public import FontaineWintenberger.FieldOfNorms.NormUnionStageValuation

/-!
# The ambient action on the original norm-field union

Actual ambient finite-image transports descend to the same canonical union.
They extend the original absolute base action and preserve its rational valuation.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- The compatible original finite-stage transports act on the same canonical union. -/
def separableNormUnionAbsoluteMap
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    letI := separableNormUnionField K L (SeparableClosure K) p hL hInfinite
    SeparableNormUnion K L (SeparableClosure K) p hL hInfinite →+*
      SeparableNormUnion K L (SeparableClosure K) p hL hInfinite := by
  letI (N : FiniteLayer L (SeparableClosure K)) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L (SeparableClosure K) p hL hInfinite N
  letI := separableNormUnionField K L (SeparableClosure K) p hL hInfinite
  letI (N : FiniteLayer L (SeparableClosure K)) : NonAssocSemiring (NormLimit K N.val) :=
    (separableNormUnionStageField K L (SeparableClosure K) p hL hInfinite N).toNonAssocSemiring
  letI : NonAssocSemiring
      (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
    (separableNormUnionField K L (SeparableClosure K) p hL hInfinite).toNonAssocSemiring
  refine DirectLimit.Ring.lift
    (fun N : FiniteLayer L (SeparableClosure K) => NormLimit K N.val)
    (separableNormUnionTransition K L (SeparableClosure K) p hL hInfinite)
    (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite)
    (fun N =>
      (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N)).comp
        (normUnionAbsoluteStageMap K L p hL hInfinite σ N).toRingHom) ?_
  intro N P hNP x
  exact (congrArg
    (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
      (normUnionAbsoluteLayer K (SeparableClosure K) L σ P))
    (normUnionAbsoluteStageMap_transition K L p hL hInfinite σ N P hNP x)).trans
      (separableNormUnionOf_transition K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N)
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ P)
        (normUnionAbsoluteLayer_mono K (SeparableClosure K) L σ hNP)
        (normUnionAbsoluteStageMap K L p hL hInfinite σ N x))

/-- On each original family, the union map is its actual ambient finite-image transport. -/
@[simp]
theorem separableNormUnionAbsoluteMap_of
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteLayer L (SeparableClosure K)) (x : NormLimit K N.val) :
    separableNormUnionAbsoluteMap K L p hL hInfinite σ
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) =
      separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N)
        (normUnionAbsoluteStageMap K L p hL hInfinite σ N x) := rfl

/-- The original identity transport fixes each element of the same union. -/
@[simp]
theorem separableNormUnionAbsoluteMap_one_apply
    (z : SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :
    separableNormUnionAbsoluteMap K L p hL hInfinite 1 z = z := by
  obtain ⟨N, x, rfl⟩ :=
    separableNormUnion_exists_stage K L (SeparableClosure K) p hL hInfinite z
  rw [separableNormUnionAbsoluteMap_of, normUnionAbsoluteStageMap_apply]
  calc
    _ = separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N
        (normLimitMap (AlgEquiv.refl : N.val ≃ₐ[K] N.val) x) :=
      separableNormUnionOf_transport_congr K L p hL hInfinite (SeparableClosure K)
        (D := N.val) (normUnionAbsoluteLayer K (SeparableClosure K) L 1 N) N
        (normUnionAbsoluteLayerEquiv K (SeparableClosure K) L 1 N)
        (AlgEquiv.refl : N.val ≃ₐ[K] N.val)
        (normUnionAbsoluteLayer_one K (SeparableClosure K) L N) (fun _ => rfl) x
    _ = _ := by rw [normLimitMap_refl]


/-- On an original family the ambient map is the original norm-family transport. -/
@[simp]
theorem separableNormUnionAbsoluteMap_of_normLimitMap
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteLayer L (SeparableClosure K)) (x : NormLimit K N.val) :
    separableNormUnionAbsoluteMap K L p hL hInfinite σ
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) =
      separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N)
        (normLimitMap (normUnionAbsoluteLayerEquiv K (SeparableClosure K) L σ N) x) :=
  (separableNormUnionAbsoluteMap_of K L p hL hInfinite σ N x).trans
    (congrArg
      (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N))
      (normUnionAbsoluteStageMap_apply K L p hL hInfinite σ N x))

/-- Ambient multiplication is composition on each original finite-stage family. -/
theorem separableNormUnionAbsoluteMap_mul_of
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteLayer L (SeparableClosure K)) (x : NormLimit K N.val) :
    separableNormUnionAbsoluteMap K L p hL hInfinite (σ * τ)
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) =
      separableNormUnionAbsoluteMap K L p hL hInfinite σ
        (separableNormUnionAbsoluteMap K L p hL hInfinite τ
          (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x)) := by
  let A := normUnionAbsoluteLayer K (SeparableClosure K) L τ N
  let B := normUnionAbsoluteLayer K (SeparableClosure K) L σ A
  let C := normUnionAbsoluteLayer K (SeparableClosure K) L (σ * τ) N
  let a : N.val ≃ₐ[K] A.val :=
    normUnionAbsoluteLayerEquiv K (SeparableClosure K) L τ N
  let b : A.val ≃ₐ[K] B.val :=
    normUnionAbsoluteLayerEquiv K (SeparableClosure K) L σ A
  let c : N.val ≃ₐ[K] C.val :=
    normUnionAbsoluteLayerEquiv K (SeparableClosure K) L (σ * τ) N
  let j (D : FiniteLayer L (SeparableClosure K)) :
      NormLimit K D.val → SeparableNormUnion K L (SeparableClosure K) p hL hInfinite :=
    separableNormUnionOf K L (SeparableClosure K) p hL hInfinite D
  calc
    _ = j C (normLimitMap c x) :=
      separableNormUnionAbsoluteMap_of_normLimitMap K L p hL hInfinite (σ * τ) N x
    _ = j B (normLimitMap (a.trans b) x) :=
      separableNormUnionOf_transport_congr K L p hL hInfinite (SeparableClosure K)
        (D := N.val) C B c (a.trans b)
        (normUnionAbsoluteLayer_mul K (SeparableClosure K) L σ τ N) (fun _ => rfl) x
    _ = j B (normLimitMap b (normLimitMap a x)) :=
      congrArg (j B) (normLimitMap_trans a b x).symm
    _ = separableNormUnionAbsoluteMap K L p hL hInfinite σ
        (j A (normLimitMap a x)) :=
      (separableNormUnionAbsoluteMap_of_normLimitMap K L p hL hInfinite σ A
        (normLimitMap a x)).symm
    _ = _ := congrArg (separableNormUnionAbsoluteMap K L p hL hInfinite σ)
      (separableNormUnionAbsoluteMap_of_normLimitMap K L p hL hInfinite τ N x).symm

/-- Original ambient multiplication is composition on every union element. -/
theorem separableNormUnionAbsoluteMap_mul_apply
    (σ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :
    separableNormUnionAbsoluteMap K L p hL hInfinite (σ * τ) z =
      separableNormUnionAbsoluteMap K L p hL hInfinite σ
        (separableNormUnionAbsoluteMap K L p hL hInfinite τ z) := by
  obtain ⟨N, x, hx⟩ :=
    separableNormUnion_exists_stage K L (SeparableClosure K) p hL hInfinite z
  exact (congrArg (separableNormUnionAbsoluteMap K L p hL hInfinite (σ * τ)) hx.symm).trans
    ((separableNormUnionAbsoluteMap_mul_of K L p hL hInfinite σ τ N x).trans
      (congrArg
        (fun y => separableNormUnionAbsoluteMap K L p hL hInfinite σ
          (separableNormUnionAbsoluteMap K L p hL hInfinite τ y)) hx))

/-- The original ambient transports form an automorphism action on the same union. -/
def separableNormUnionAbsoluteAut :
    letI unionField : Field (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
      separableNormUnionField K L (SeparableClosure K) p hL hInfinite
    letI unionRing : NonAssocSemiring (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
      unionField.toSemifield.toCommSemiring.toSemiring.toNonAssocSemiring
    letI : Mul (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) := unionRing.toMul
    letI : Add (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) := unionRing.toAdd
    letI : Group (RingAut (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite)) := RingAut.instGroup _
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →*
      (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite ≃+*
        SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
  letI unionField : Field (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
      separableNormUnionField K L (SeparableClosure K) p hL hInfinite
  letI unionRing : NonAssocSemiring (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :=
    unionField.toSemifield.toCommSemiring.toSemiring.toNonAssocSemiring
  letI : Mul (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) := unionRing.toMul
  letI : Add (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) := unionRing.toAdd
  letI : Group (RingAut (SeparableNormUnion K L (SeparableClosure K) p hL hInfinite)) := RingAut.instGroup _
  let f (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      SeparableNormUnion K L (SeparableClosure K) p hL hInfinite ≃+*
        SeparableNormUnion K L (SeparableClosure K) p hL hInfinite :=
    RingEquiv.ofRingHom
      (separableNormUnionAbsoluteMap K L p hL hInfinite σ)
      (separableNormUnionAbsoluteMap K L p hL hInfinite σ⁻¹)
      (RingHom.ext (fun z =>
        (separableNormUnionAbsoluteMap_mul_apply K L p hL hInfinite σ σ⁻¹ z).symm.trans
          ((congrArg
            (fun δ => separableNormUnionAbsoluteMap K L p hL hInfinite δ z)
            (mul_inv_cancel σ)).trans
              (separableNormUnionAbsoluteMap_one_apply K L p hL hInfinite z))))
      (RingHom.ext (fun z =>
        (separableNormUnionAbsoluteMap_mul_apply K L p hL hInfinite σ⁻¹ σ z).symm.trans
          ((congrArg
            (fun δ => separableNormUnionAbsoluteMap K L p hL hInfinite δ z)
            (inv_mul_cancel σ)).trans
              (separableNormUnionAbsoluteMap_one_apply K L p hL hInfinite z))))
  { toFun := f
    map_one' := RingEquiv.ext
      (fun z => separableNormUnionAbsoluteMap_one_apply K L p hL hInfinite z)
    map_mul' := fun σ τ => RingEquiv.ext
      (fun z => separableNormUnionAbsoluteMap_mul_apply K L p hL hInfinite σ τ z) }

/-- Bundling as automorphisms retains the literal original union map. -/
@[simp]
theorem separableNormUnionAbsoluteAut_apply
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :
    separableNormUnionAbsoluteAut K L p hL hInfinite σ z =
      separableNormUnionAbsoluteMap K L p hL hInfinite σ z := rfl

/-- Each original finite-stage family is transported by the original ambient automorphism. -/
@[simp]
theorem separableNormUnionAbsoluteAut_of
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (N : FiniteLayer L (SeparableClosure K)) (x : NormLimit K N.val) :
    separableNormUnionAbsoluteAut K L p hL hInfinite σ
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) =
      separableNormUnionOf K L (SeparableClosure K) p hL hInfinite
        (normUnionAbsoluteLayer K (SeparableClosure K) L σ N)
        (normLimitMap (normUnionAbsoluteLayerEquiv K (SeparableClosure K) L σ N) x) :=
  (separableNormUnionAbsoluteAut_apply K L p hL hInfinite σ
    (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x)).trans
      (separableNormUnionAbsoluteMap_of_normLimitMap K L p hL hInfinite σ N x)

/-- The ambient union action extends the original absolute action on the base norm field. -/
theorem separableNormUnionAbsoluteAut_base
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : NormLimit K L) :
    separableNormUnionAbsoluteAut K L p hL hInfinite σ
        (separableNormUnionBaseHom K L (SeparableClosure K) p hL hInfinite x) =
      separableNormUnionBaseHom K L (SeparableClosure K) p hL hInfinite
        (normLimitAbsoluteAut K L p hL hInfinite σ x) := by
  let N : FiniteLayer L (SeparableClosure K) := FiniteLayer.bottom
  let P := normUnionAbsoluteLayer K (SeparableClosure K) L σ N
  let i : NormLimit K L → NormLimit K N.val :=
    separableNormUnionBaseToStage K L (SeparableClosure K) p hL hInfinite N
  let j (D : FiniteLayer L (SeparableClosure K)) :
      NormLimit K D.val → SeparableNormUnion K L (SeparableClosure K) p hL hInfinite :=
    separableNormUnionOf K L (SeparableClosure K) p hL hInfinite D
  have hx : j N (i x) =
      separableNormUnionBaseHom K L (SeparableClosure K) p hL hInfinite x :=
    separableNormUnionOf_base K L (SeparableClosure K) p hL hInfinite N x
  calc
    _ = separableNormUnionAbsoluteAut K L p hL hInfinite σ (j N (i x)) :=
      congrArg (separableNormUnionAbsoluteAut K L p hL hInfinite σ) hx.symm
    _ = j P (normUnionAbsoluteStageMap K L p hL hInfinite σ N (i x)) :=
      (separableNormUnionAbsoluteAut_apply K L p hL hInfinite σ (j N (i x))).trans
        (separableNormUnionAbsoluteMap_of K L p hL hInfinite σ N (i x))
    _ = j P (separableNormUnionBaseToStage K L (SeparableClosure K) p hL hInfinite P
        (normLimitAbsoluteAut K L p hL hInfinite σ x)) :=
      congrArg (j P) (normUnionAbsoluteStageMap_base K L p hL hInfinite σ N x)
    _ = _ := separableNormUnionOf_base K L (SeparableClosure K) p hL hInfinite P
      (normLimitAbsoluteAut K L p hL hInfinite σ x)

/-- The original relative functor map agrees with ambient transport on every finite family. -/
theorem separableNormUnionAbsoluteAut_restrictScalars_of
    (τ :
      letI : Semiring (SeparableClosure K) :=
        @CommSemiring.toSemiring (SeparableClosure K)
        (@Semifield.toCommSemiring (SeparableClosure K)
          (@Field.toSemifield (SeparableClosure K)
            (separableClosure K (AlgebraicClosure K)).toField))
      SeparableClosure K ≃ₐ[L] SeparableClosure K)
    (N : FiniteLayer L (SeparableClosure K)) (x : NormLimit K N.val) :
    separableNormUnionAbsoluteAut K L p hL hInfinite (τ.restrictScalars K)
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) =
      separableNormUnionMap K L (SeparableClosure K) p hL hInfinite
        (SeparableClosure K) τ.toAlgHom
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) := by
  let P := normUnionAbsoluteLayer K (SeparableClosure K) L (τ.restrictScalars K) N
  let Q := FiniteLayer.map τ.toAlgHom N
  let e : N.val ≃ₐ[K] P.val :=
    normUnionAbsoluteLayerEquiv K (SeparableClosure K) L (τ.restrictScalars K) N
  let f : N.val ≃ₐ[K] Q.val :=
    (FiniteLayer.equivMap τ.toAlgHom N).restrictScalars K
  let j (D : FiniteLayer L (SeparableClosure K)) :
      NormLimit K D.val → SeparableNormUnion K L (SeparableClosure K) p hL hInfinite :=
    separableNormUnionOf K L (SeparableClosure K) p hL hInfinite D
  have hPQ : P = Q := by
    apply Subtype.ext
    apply SetLike.ext
    intro z
    change (∃ a ∈ N.val, τ a = z) ↔ ∃ a ∈ N.val, τ a = z
    rfl
  calc
    _ = j P (normLimitMap e x) :=
      separableNormUnionAbsoluteAut_of K L p hL hInfinite (τ.restrictScalars K) N x
    _ = j Q (normLimitMap f x) :=
      separableNormUnionOf_transport_congr K L p hL hInfinite (SeparableClosure K)
        (D := N.val) P Q e f hPQ (fun _ => rfl) x
    _ = _ :=
      ((separableNormUnionMap_of K L (SeparableClosure K) p hL hInfinite
        (SeparableClosure K) τ.toAlgHom N x).trans
        (congrArg (j Q)
          (separableNormUnionStageMap_apply K L (SeparableClosure K) p hL hInfinite
            (SeparableClosure K) τ.toAlgHom N x))).symm

/-- On the original relative absolute Galois subgroup, ambient transport is the functor map. -/
theorem separableNormUnionAbsoluteAut_restrictScalars
    (τ :
      letI : Semiring (SeparableClosure K) :=
        @CommSemiring.toSemiring (SeparableClosure K)
        (@Semifield.toCommSemiring (SeparableClosure K)
          (@Field.toSemifield (SeparableClosure K)
            (separableClosure K (AlgebraicClosure K)).toField))
      SeparableClosure K ≃ₐ[L] SeparableClosure K)
    (z : SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :
    separableNormUnionAbsoluteAut K L p hL hInfinite (τ.restrictScalars K) z =
      separableNormUnionMap K L (SeparableClosure K) p hL hInfinite
        (SeparableClosure K) τ.toAlgHom z := by
  obtain ⟨N, x, hx⟩ :=
    separableNormUnion_exists_stage K L (SeparableClosure K) p hL hInfinite z
  exact (congrArg
    (separableNormUnionAbsoluteAut K L p hL hInfinite (τ.restrictScalars K)) hx.symm).trans
      ((separableNormUnionAbsoluteAut_restrictScalars_of K L p hL hInfinite τ N x).trans
        (congrArg
          (separableNormUnionMap K L (SeparableClosure K) p hL hInfinite
            (SeparableClosure K) τ.toAlgHom) hx))

/-- The actual absolute Galois action preserves the original rational union valuation. -/
theorem separableNormUnionAbsoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (z : SeparableNormUnion K L (SeparableClosure K) p hL hInfinite) :
    separableNormUnionValuation K L (SeparableClosure K) p hL hInfinite
        (separableNormUnionAbsoluteAut K L p hL hInfinite σ z) =
      separableNormUnionValuation K L (SeparableClosure K) p hL hInfinite z := by
  obtain ⟨N, x, hx⟩ :=
    separableNormUnion_exists_stage K L (SeparableClosure K) p hL hInfinite z
  let P := normUnionAbsoluteLayer K (SeparableClosure K) L σ N
  let e := normUnionAbsoluteLayerEquiv K (SeparableClosure K) L σ N
  let v := separableNormUnionValuation K L (SeparableClosure K) p hL hInfinite
  have hstage :
      v (separableNormUnionAbsoluteAut K L p hL hInfinite σ
        (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x)) =
      v (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite N x) := by
    calc
      _ = v (separableNormUnionOf K L (SeparableClosure K) p hL hInfinite P
          (normLimitMap e x)) :=
        congrArg v (separableNormUnionAbsoluteAut_of K L p hL hInfinite σ N x)
      _ = separableNormUnionStageValuation K L (SeparableClosure K) p hL hInfinite P
          (normLimitMap e x) :=
        separableNormUnionValuation_of K L (SeparableClosure K) p hL hInfinite P
          (normLimitMap e x)
      _ = separableNormUnionStageValuation K L (SeparableClosure K) p hL hInfinite N x :=
        normUnionStageEquiv_valuation K L (SeparableClosure K) p hL hInfinite N P
          (AlgEquiv.restrictNormalHom L σ) e
          (fun a => Subtype.ext (AlgEquiv.restrictNormalHom_apply L σ a).symm) x
      _ = _ :=
        (separableNormUnionValuation_of K L (SeparableClosure K) p hL hInfinite N x).symm
  exact (congrArg (fun y => v (separableNormUnionAbsoluteAut K L p hL hInfinite σ y))
    hx.symm).trans (hstage.trans (congrArg v hx))

end FontaineWintenberger
