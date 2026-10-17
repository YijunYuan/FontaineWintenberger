/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.FiniteFullFaithful
public import FontaineWintenberger.FieldOfNorms.FiniteLayerGlue
public import FontaineWintenberger.FieldOfNorms.SeparableNormUnion

/-!
# Finite-stage factorization and gluing of original norm-field Hom maps

Finite basis images lie in one actual target stage. Canonical range
factorization then gives an actual finite-stage algebra homomorphism;
finite full faithfulness supplies and glues the original field embeddings.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- Containment of the images of a genuine finite basis gives canonical
factorization through the original embedded target field. -/
theorem exists_algHom_factor_of_basis_mem_range
    {F A B C : Type*} [Field F] [Field A] [Field B] [Field C]
    [Algebra F A] [Algebra F B] [Algebra F C] [FiniteDimensional F A]
    (φ : A →ₐ[F] C) (ι : B →ₐ[F] C)
    (hmem : ∀ i : Fin (Module.finrank F A),
      φ (Module.finBasis F A i) ∈ ι.fieldRange) :
    ∃ ψ : A →ₐ[F] B, ι.comp ψ = φ := by
  have hfull (a : A) : φ a ∈ ι.fieldRange := by
    rw [← (Module.finBasis F A).sum_repr a, map_sum]
    apply ι.fieldRange.toSubalgebra.sum_mem
    intro i _
    rw [map_smul]
    exact ι.fieldRange.toSubalgebra.smul_mem (hmem i) ((Module.finBasis F A).repr a i)
  let φ' : A →ₐ[F] ι.fieldRange := φ.codRestrict ι.fieldRange.toSubalgebra hfull
  let ψ := ι.equivFieldRange.symm.toAlgHom.comp φ'
  refine ⟨ψ, AlgHom.ext (fun a => ?_)⟩
  exact congrArg Subtype.val (ι.equivFieldRange.apply_symm_apply (φ' a))

section NormUnion

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- A finite algebraic Hom into the actual norm-field union factors through
one actual finite original stage. -/
theorem separableNormUnion_exists_algHom_factor :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    ∀ {A : Type*} [Field A] [Algebra (NormLimit K L) A]
      [FiniteDimensional (NormLimit K L) A]
      (f : A →ₐ[NormLimit K L] SeparableNormUnion K L M p hL hInfinite),
      ∃ N : FiniteLayer L M,
        letI := separableNormUnionStageField K L M p hL hInfinite N
        letI := separableNormUnionStageAlgebra K L M p hL hInfinite N
        ∃ g : A →ₐ[NormLimit K L] NormLimit K N.val,
          (separableNormUnionOfAlgHom K L M p hL hInfinite N).comp g = f := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  intro A _ _ _ f
  obtain ⟨N, x, hx⟩ := separableNormUnion_exists_finiteStage K L M p hL hInfinite
    (fun i => f (Module.finBasis (NormLimit K L) A i))
  let := separableNormUnionStageField K L M p hL hInfinite N
  let := separableNormUnionStageAlgebra K L M p hL hInfinite N
  refine ⟨N, exists_algHom_factor_of_basis_mem_range f
    (separableNormUnionOfAlgHom K L M p hL hInfinite N) (fun i => ?_)⟩
  exact ⟨x i, hx i⟩

variable (M₁ : Type*) [Field M₁] [Algebra K M₁] [Algebra L M₁]
    [IsScalarTower K L M₁] [Algebra.IsSeparable L M₁]

/-- Every Hom from an actual finite source norm field to the union comes from
an original field embedding into an actual finite target layer. -/
theorem separableNormUnion_exists_finite_preimage (Q : FiniteLayer L M₁) :
    letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionStageField K L M₁ p hL hInfinite Q
    letI := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    ∀ f : NormLimit K Q.val →ₐ[NormLimit K L] SeparableNormUnion K L M p hL hInfinite,
      ∃ R : FiniteLayer L M,
        letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
        letI := separableNormUnionStageField K L M p hL hInfinite R
        letI := separableNormUnionStageAlgebra K L M p hL hInfinite R
        ∃ φ : Q.val →ₐ[L] R.val,
          (separableNormUnionOfAlgHom K L M p hL hInfinite R).comp
            (finiteNormLimitAlgHom K L Q.val R.val p hL
              (separableNormUnionStage_isAPF K L M₁ hL Q)
              (separableNormUnionStage_isAPF K L M hL R) hInfinite
              (separableNormUnionStage_infinite K L M₁ hInfinite Q)
              (separableNormUnionStage_infinite K L M hInfinite R) φ) = f := by
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionStageField K L M₁ p hL hInfinite Q
  let := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  let : FiniteDimensional (NormLimit K L) (NormLimit K Q.val) :=
    finiteDimensional_finiteNormLimit K L Q.val p hL
      (separableNormUnionStage_isAPF K L M₁ hL Q) hInfinite
      (separableNormUnionStage_infinite K L M₁ hInfinite Q)
  intro f
  obtain ⟨R, g, hg⟩ := separableNormUnion_exists_algHom_factor K L M p hL hInfinite f
  let : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
  let := separableNormUnionStageField K L M p hL hInfinite R
  let := separableNormUnionStageAlgebra K L M p hL hInfinite R
  let e := finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite
  refine ⟨R, e.symm g, ?_⟩
  exact (congrArg (fun j =>
    (separableNormUnionOfAlgHom K L M p hL hInfinite R).comp j)
    (e.apply_symm_apply g)).trans hg

/-- Enlarging the actual target layer leaves the induced map into the same
norm-field union unchanged. -/
theorem separableNormUnionOf_finiteHom_inclusion (Q : FiniteLayer L M₁)
    (R P : FiniteLayer L M) (hRP : R ≤ P) (φ : Q.val →ₐ[L] R.val)
    (x : NormLimit K Q.val) :
    letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
    letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
    letI : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
    separableNormUnionOf K L M p hL hInfinite P
        (finiteNormLimitHomEquiv K L Q.val P.val p hL hInfinite
          ((IntermediateField.inclusion hRP).comp φ) x) =
      separableNormUnionOf K L M p hL hInfinite R
        (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite φ x) := by
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let (N : FiniteLayer L M) : Algebra.IsSeparable K N.val :=
    Algebra.IsSeparable.trans K L N.val
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionStageField K L M₁ p hL hInfinite Q
  let := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  let (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p hL hInfinite N
  let (N : FiniteLayer L M) : Algebra (NormLimit K L) (NormLimit K N.val) :=
    separableNormUnionStageAlgebra K L M p hL hInfinite N
  let y := finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite φ x
  have hc := congrArg (fun f => f x)
    (finiteNormLimitAlgHom_comp K L Q.val R.val P.val p hL
      (separableNormUnionStage_isAPF K L M₁ hL Q)
      (separableNormUnionStage_isAPF K L M hL R)
      (separableNormUnionStage_isAPF K L M hL P) hInfinite
      (separableNormUnionStage_infinite K L M₁ hInfinite Q)
      (separableNormUnionStage_infinite K L M hInfinite R)
      (separableNormUnionStage_infinite K L M hInfinite P) φ
      (IntermediateField.inclusion hRP))
  have hi : finiteNormLimitHomEquiv K L R.val P.val p hL hInfinite
      (IntermediateField.inclusion hRP) y =
      separableNormUnionTransition K L M p hL hInfinite R P hRP y := by
    let : Algebra R.val P.val := (IntermediateField.inclusion hRP).toRingHom.toAlgebra
    let : IsScalarTower L R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower K R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    exact finiteNormLimitAlgHom_algebraMap K L R.val P.val p hL
      (separableNormUnionStage_isAPF K L M hL R)
      (separableNormUnionStage_isAPF K L M hL P) hInfinite
      (separableNormUnionStage_infinite K L M hInfinite R)
      (separableNormUnionStage_infinite K L M hInfinite P) y
  exact (congrArg (separableNormUnionOf K L M p hL hInfinite P) hc).trans
    ((congrArg (separableNormUnionOf K L M p hL hInfinite P) hi).trans
      (separableNormUnionOf_transition K L M p hL hInfinite R P hRP y))

/-- Equality of maps into the actual union reflects equality of the original
finite-source embeddings, even when their target stages differ. -/
theorem separableNormUnion_finiteHom_faithful (Q : FiniteLayer L M₁)
    (R S : FiniteLayer L M) (φ : Q.val →ₐ[L] R.val) (ψ : Q.val →ₐ[L] S.val) :
    letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
    letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
    letI : Algebra.IsSeparable K S.val := Algebra.IsSeparable.trans K L S.val
    (∀ x : NormLimit K Q.val,
      separableNormUnionOf K L M p hL hInfinite R
          (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite φ x) =
        separableNormUnionOf K L M p hL hInfinite S
          (finiteNormLimitHomEquiv K L Q.val S.val p hL hInfinite ψ x)) →
      ∀ a : Q.val, (φ a : M) = (ψ a : M) := by
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let (N : FiniteLayer L M) : Algebra.IsSeparable K N.val :=
    Algebra.IsSeparable.trans K L N.val
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionStageField K L M₁ p hL hInfinite Q
  let := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  let (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p hL hInfinite N
  let (N : FiniteLayer L M) : Algebra (NormLimit K L) (NormLimit K N.val) :=
    separableNormUnionStageAlgebra K L M p hL hInfinite N
  let := separableNormUnionField K L M p hL hInfinite
  intro h a
  let P : FiniteLayer L M := FiniteLayer.sup R S
  have he : (IntermediateField.inclusion (show R ≤ P from FiniteLayer.le_sup_left R S)).comp φ =
      (IntermediateField.inclusion (show S ≤ P from FiniteLayer.le_sup_right R S)).comp ψ := by
    apply (finiteNormLimitHomEquiv K L Q.val P.val p hL hInfinite).injective
    apply AlgHom.ext
    intro x
    apply separableNormUnionOf_injective K L M p hL hInfinite P
    exact (separableNormUnionOf_finiteHom_inclusion K L M p hL hInfinite M₁
      Q R P (FiniteLayer.le_sup_left R S) φ x).trans ((h x).trans
        (separableNormUnionOf_finiteHom_inclusion K L M p hL hInfinite M₁
          Q S P (FiniteLayer.le_sup_right R S) ψ x).symm)
  exact congrArg (fun z : P.val => (z : M)) (AlgHom.congr_fun he a)

/-- Restricting an original finite embedding to a smaller source stage gives
the same finite Hom evaluated after the original transition map. -/
theorem separableNormUnion_finiteHom_source_inclusion (Q T : FiniteLayer L M₁)
    (hQT : Q ≤ T) (R : FiniteLayer L M) (ψ : T.val →ₐ[L] R.val)
    (x : NormLimit K Q.val) :
    letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
    letI : Algebra.IsSeparable K T.val := Algebra.IsSeparable.trans K L T.val
    letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
    finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite
        (ψ.comp (IntermediateField.inclusion hQT)) x =
      finiteNormLimitHomEquiv K L T.val R.val p hL hInfinite ψ
        (separableNormUnionTransition K L M₁ p hL hInfinite Q T hQT x) := by
  let (N : FiniteLayer L M₁) : Algebra.IsSeparable K N.val :=
    Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
  let := normLimitField K L p hL hInfinite
  let (N : FiniteLayer L M₁) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M₁ p hL hInfinite N
  let (N : FiniteLayer L M₁) : Algebra (NormLimit K L) (NormLimit K N.val) :=
    separableNormUnionStageAlgebra K L M₁ p hL hInfinite N
  let := separableNormUnionStageField K L M p hL hInfinite R
  let := separableNormUnionStageAlgebra K L M p hL hInfinite R
  have hc := congrArg (fun f => f x)
    (finiteNormLimitAlgHom_comp K L Q.val T.val R.val p hL
      (separableNormUnionStage_isAPF K L M₁ hL Q)
      (separableNormUnionStage_isAPF K L M₁ hL T)
      (separableNormUnionStage_isAPF K L M hL R) hInfinite
      (separableNormUnionStage_infinite K L M₁ hInfinite Q)
      (separableNormUnionStage_infinite K L M₁ hInfinite T)
      (separableNormUnionStage_infinite K L M hInfinite R)
      (IntermediateField.inclusion hQT) ψ)
  have hi : finiteNormLimitHomEquiv K L Q.val T.val p hL hInfinite
      (IntermediateField.inclusion hQT) x =
      separableNormUnionTransition K L M₁ p hL hInfinite Q T hQT x := by
    let : Algebra Q.val T.val := (IntermediateField.inclusion hQT).toRingHom.toAlgebra
    let : IsScalarTower L Q.val T.val := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower K Q.val T.val := IsScalarTower.of_algebraMap_eq' rfl
    exact finiteNormLimitAlgHom_algebraMap K L Q.val T.val p hL
      (separableNormUnionStage_isAPF K L M₁ hL Q)
      (separableNormUnionStage_isAPF K L M₁ hL T) hInfinite
      (separableNormUnionStage_infinite K L M₁ hInfinite Q)
      (separableNormUnionStage_infinite K L M₁ hInfinite T) x
  exact hc.trans (congrArg
    (finiteNormLimitHomEquiv K L T.val R.val p hL hInfinite ψ) hi)

/-- A Hom of the actual norm-field unions determines an original algebra
embedding whose finite restrictions realize all its finite-stage maps. -/
theorem separableNormUnion_exists_originalHom :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionField K L M₁ p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M₁ p hL hInfinite
    ∀ f : SeparableNormUnion K L M₁ p hL hInfinite →ₐ[NormLimit K L]
        SeparableNormUnion K L M p hL hInfinite,
      ∃ t : M₁ →ₐ[L] M, ∀ Q : FiniteLayer L M₁,
        letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
        letI := separableNormUnionStageField K L M₁ p hL hInfinite Q
        letI := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
        ∃ R : FiniteLayer L M,
          letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
          letI := separableNormUnionStageField K L M p hL hInfinite R
          letI := separableNormUnionStageAlgebra K L M p hL hInfinite R
          ∃ φ : Q.val →ₐ[L] R.val,
            (∀ a : Q.val, (φ a : M) = t a) ∧
              (separableNormUnionOfAlgHom K L M p hL hInfinite R).comp
                (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite φ) =
                f.comp (separableNormUnionOfAlgHom K L M₁ p hL hInfinite Q) := by
  classical
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionField K L M₁ p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M₁ p hL hInfinite
  let (Q : FiniteLayer L M₁) : Algebra.IsSeparable K Q.val :=
    Algebra.IsSeparable.trans K L Q.val
  let (Q : FiniteLayer L M₁) : Field (NormLimit K Q.val) :=
    separableNormUnionStageField K L M₁ p hL hInfinite Q
  let (Q : FiniteLayer L M₁) : Algebra (NormLimit K L) (NormLimit K Q.val) :=
    separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  let (R : FiniteLayer L M) : Algebra.IsSeparable K R.val :=
    Algebra.IsSeparable.trans K L R.val
  let (R : FiniteLayer L M) : Field (NormLimit K R.val) :=
    separableNormUnionStageField K L M p hL hInfinite R
  let (R : FiniteLayer L M) : Algebra (NormLimit K L) (NormLimit K R.val) :=
    separableNormUnionStageAlgebra K L M p hL hInfinite R
  intro f
  choose R φ hφ using fun Q : FiniteLayer L M₁ =>
    separableNormUnion_exists_finite_preimage K L M p hL hInfinite M₁ Q
      (f.comp (separableNormUnionOfAlgHom K L M₁ p hL hInfinite Q))
  let family (Q : FiniteLayer L M₁) : Q.val →ₐ[L] M := (R Q).val.val.comp (φ Q)
  have hc (Q T : FiniteLayer L M₁) (hQT : Q ≤ T) :
      family Q = (family T).comp (IntermediateField.inclusion hQT) := by
    apply AlgHom.ext
    intro a
    refine separableNormUnion_finiteHom_faithful K L M p hL hInfinite M₁
      Q (R Q) (R T) (φ Q) ((φ T).comp (IntermediateField.inclusion hQT)) ?_ a
    intro x
    have hQ := AlgHom.congr_fun (hφ Q) x
    have hT := AlgHom.congr_fun (hφ T)
      (separableNormUnionTransition K L M₁ p hL hInfinite Q T hQT x)
    exact hQ.trans ((congrArg f
      (separableNormUnionOf_transition K L M₁ p hL hInfinite Q T hQT x).symm).trans
        (hT.symm.trans (congrArg (separableNormUnionOf K L M p hL hInfinite (R T))
          (separableNormUnion_finiteHom_source_inclusion K L M p hL hInfinite M₁
            Q T hQT (R T) (φ T) x).symm)))
  let t := FiniteLayer.liftAlgHom family hc
  refine ⟨t, fun Q => ⟨R Q, φ Q, ⟨?_, hφ Q⟩⟩⟩
  intro a
  exact (FiniteLayer.liftAlgHom_apply family hc Q a).symm

/-- A genuine original finite-stage factorization computes the induced union
map by the same finite Hom, independently of the chosen containing stage. -/
theorem separableNormUnionAlgMap_of_factor (t : M₁ →ₐ[L] M)
    (Q : FiniteLayer L M₁) (R : FiniteLayer L M) (φ : Q.val →ₐ[L] R.val)
    (h : ∀ a : Q.val, (φ a : M) = t a) (x : NormLimit K Q.val) :
    letI : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
    letI : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
    separableNormUnionAlgMap K L M₁ p hL hInfinite M t
        (separableNormUnionOf K L M₁ p hL hInfinite Q x) =
      separableNormUnionOf K L M p hL hInfinite R
        (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite φ x) := by
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let (N : FiniteLayer L M) : Algebra.IsSeparable K N.val :=
    Algebra.IsSeparable.trans K L N.val
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionStageField K L M₁ p hL hInfinite Q
  let := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  let (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p hL hInfinite N
  let (N : FiniteLayer L M) : Algebra (NormLimit K L) (NormLimit K N.val) :=
    separableNormUnionStageAlgebra K L M p hL hInfinite N
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionField K L M₁ p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M₁ p hL hInfinite
  let J : FiniteLayer L M := FiniteLayer.map t Q
  let e : Q.val ≃ₐ[L] J.val := FiniteLayer.equivMap t Q
  have hJR : J ≤ R := by
    intro z hz
    let a := e.symm ⟨z, hz⟩
    have ha : (e a : M) = z := congrArg (fun w : J.val => (w : M))
      (e.apply_symm_apply ⟨z, hz⟩)
    have hzφ : (φ a : M) = z := (h a).trans ha
    exact hzφ ▸ (φ a).property
  have hc : (IntermediateField.inclusion hJR).comp e.toAlgHom = φ := by
    apply AlgHom.ext
    intro a
    exact Subtype.ext (h a).symm
  have he : finiteNormLimitHomEquiv K L Q.val J.val p hL hInfinite e.toAlgHom x =
      normLimitMap (e.restrictScalars K) x := by
    exact finiteNormLimitEmbeddingMap_algEquiv K (e.restrictScalars K) x
  calc
    _ = separableNormUnionOf K L M p hL hInfinite J
        (normLimitMap (e.restrictScalars K) x) :=
      (separableNormUnionMap_of K L M₁ p hL hInfinite M t Q x).trans
        (congrArg (separableNormUnionOf K L M p hL hInfinite J)
          (separableNormUnionStageMap_apply K L M₁ p hL hInfinite M t Q x))
    _ = separableNormUnionOf K L M p hL hInfinite J
        (finiteNormLimitHomEquiv K L Q.val J.val p hL hInfinite e.toAlgHom x) :=
      congrArg (separableNormUnionOf K L M p hL hInfinite J) he.symm
    _ = separableNormUnionOf K L M p hL hInfinite R
        (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite
          ((IntermediateField.inclusion hJR).comp e.toAlgHom) x) :=
      (separableNormUnionOf_finiteHom_inclusion K L M p hL hInfinite M₁
        Q J R hJR e.toAlgHom x).symm
    _ = _ := congrArg (fun j => separableNormUnionOf K L M p hL hInfinite R
      (finiteNormLimitHomEquiv K L Q.val R.val p hL hInfinite j x)) hc

/-- Every algebra Hom of the actual unions is induced by an original embedding. -/
theorem separableNormUnionAlgMap_surjective :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionField K L M₁ p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M₁ p hL hInfinite
    Function.Surjective (separableNormUnionAlgMap K L M₁ p hL hInfinite M) := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionField K L M₁ p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M₁ p hL hInfinite
  intro f
  obtain ⟨t, ht⟩ := separableNormUnion_exists_originalHom K L M p hL hInfinite M₁ f
  refine ⟨t, AlgHom.ext (fun z => ?_)⟩
  obtain ⟨Q, x, rfl⟩ := separableNormUnion_exists_stage K L M₁ p hL hInfinite z
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let := separableNormUnionStageField K L M₁ p hL hInfinite Q
  let := separableNormUnionStageAlgebra K L M₁ p hL hInfinite Q
  obtain ⟨R, φ, hφ, hf⟩ := ht Q
  let : Algebra.IsSeparable K R.val := Algebra.IsSeparable.trans K L R.val
  let := separableNormUnionStageField K L M p hL hInfinite R
  let := separableNormUnionStageAlgebra K L M p hL hInfinite R
  exact (separableNormUnionAlgMap_of_factor K L M p hL hInfinite M₁
    t Q R φ hφ x).trans (AlgHom.congr_fun hf x)

/-- The actual union functor distinguishes every original algebra embedding. -/
theorem separableNormUnionAlgMap_injective :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionField K L M₁ p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M₁ p hL hInfinite
    Function.Injective (separableNormUnionAlgMap K L M₁ p hL hInfinite M) := by
  let := normLimitField K L p hL hInfinite
  let := separableNormUnionField K L M p hL hInfinite
  let := separableNormUnionField K L M₁ p hL hInfinite
  let := separableNormUnionAlgebra K L M p hL hInfinite
  let := separableNormUnionAlgebra K L M₁ p hL hInfinite
  intro t u h
  apply AlgHom.ext
  intro a
  obtain ⟨Q, ha⟩ := FiniteLayer.exists_mem (L := L) a
  let R := FiniteLayer.map t Q
  let S := FiniteLayer.map u Q
  refine separableNormUnion_finiteHom_faithful K L M p hL hInfinite M₁
    Q R S (FiniteLayer.equivMap t Q).toAlgHom
      (FiniteLayer.equivMap u Q).toAlgHom ?_ ⟨a, ha⟩
  intro x
  exact (separableNormUnionAlgMap_of_factor K L M p hL hInfinite M₁ t Q R
    (FiniteLayer.equivMap t Q).toAlgHom (fun _ => rfl) x).symm.trans
      ((AlgHom.congr_fun h (separableNormUnionOf K L M₁ p hL hInfinite Q x)).trans
        (separableNormUnionAlgMap_of_factor K L M p hL hInfinite M₁ u Q S
          (FiniteLayer.equivMap u Q).toAlgHom (fun _ => rfl) x))

/-- Full faithfulness for arbitrary original separable algebraic extensions. -/
theorem separableNormUnionAlgMap_bijective :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionField K L M₁ p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L M₁ p hL hInfinite
    Function.Bijective (separableNormUnionAlgMap K L M₁ p hL hInfinite M) := by
  exact ⟨separableNormUnionAlgMap_injective K L M p hL hInfinite M₁,
    separableNormUnionAlgMap_surjective K L M p hL hInfinite M₁⟩

end NormUnion

section FullFaithful

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L M N : Type*) [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- The canonical full Hom equivalence is the actual original union functor. -/
def separableNormUnionHomEquiv :
    letI := normLimitField K L p hL hInfinite
    letI := separableNormUnionField K L M p hL hInfinite
    letI := separableNormUnionField K L N p hL hInfinite
    letI := separableNormUnionAlgebra K L M p hL hInfinite
    letI := separableNormUnionAlgebra K L N p hL hInfinite
    (M →ₐ[L] N) ≃ (SeparableNormUnion K L M p hL hInfinite →ₐ[NormLimit K L]
      SeparableNormUnion K L N p hL hInfinite) := by
  letI := normLimitField K L p hL hInfinite
  letI := separableNormUnionField K L M p hL hInfinite
  letI := separableNormUnionField K L N p hL hInfinite
  letI := separableNormUnionAlgebra K L M p hL hInfinite
  letI := separableNormUnionAlgebra K L N p hL hInfinite
  exact Equiv.ofBijective (separableNormUnionAlgMap K L M p hL hInfinite N)
    (separableNormUnionAlgMap_bijective K L N p hL hInfinite M)

end FullFaithful

end FontaineWintenberger
