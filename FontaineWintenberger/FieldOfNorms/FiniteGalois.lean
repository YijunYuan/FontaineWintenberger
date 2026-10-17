/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.GaloisGoodFields
public import FontaineWintenberger.FieldOfNorms.FiniteEmbedding
public import FontaineWintenberger.FieldOfNorms.FaithfulAction
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Finite Galois extensions of the original norm fields

Fixed original norm families descend through actual stable good fields and
original finite norms. The same original faithful action then supplies the
finite Galois extension and its degree by finite Artin theory.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section OriginalFamilies

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Module.Finite M N] [IsGalois M N]

/-- Actual stable good finite fields are a cofinal subsystem of the original target. -/
theorem galoisStableGoodFiniteLayers_cofinal [Algebra.IsAlgebraic K N]
    (E : FiniteLayer K N) :
    ∃ D : FiniteLayer K N,
      (IsGoodFiniteLayer K M D ∧ ∀ σ : N ≃ₐ[M] N,
        D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧ E ≤ D := by
  obtain ⟨D, hED, hg, hs, _⟩ := exists_galois_stable_goodFiniteLayer_ge K M N E
  exact ⟨D, ⟨hg, hs⟩, hED⟩

/-- A fixed original family has a unique original pullback coordinate at
every original stable finite field. -/
theorem existsUnique_galoisNormCoordinate (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    ∃! a : finiteLayerPullback K M D,
      finiteLayerPullbackTo K M D a = normLimitEval K N D β := by
  have hfixed : ∀ σ : N ≃ₐ[M] N,
      σ (normLimitEval K N D β : N) = (normLimitEval K N D β : N) := by
    intro σ
    have hi : FiniteLayer.map (σ.restrictScalars K).symm.toAlgHom D = D :=
      Subtype.ext (hD σ.symm)
    have h := coe_normLimitEval_normLimitMap (σ.restrictScalars K) β D
    rw [hβ σ, hi] at h
    exact h.symm
  obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := M) (normLimitEval K N D β : N)).mpr hfixed
  have hmD : algebraMap M N m ∈ D.val := hm.symm ▸ (normLimitEval K N D β).property
  let a : finiteLayerPullback K M D := ⟨m, hmD⟩
  have ha : finiteLayerPullbackTo K M D a = normLimitEval K N D β := Subtype.ext hm
  exact ⟨a, ha, fun b hb => (finiteLayerPullbackTo K M D).injective (hb.trans ha.symm)⟩

/-- The unique preimage lies in the original source pullback field. -/
def galoisNormCoordinate (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    finiteLayerPullback K M D :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose

/-- Original inclusion of the actual preimage recovers exactly the original coordinate. -/
theorem galoisNormCoordinate_spec (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (D : FiniteLayer K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    finiteLayerPullbackTo K M D (galoisNormCoordinate K M N β hβ D hD) =
      normLimitEval K N D β :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose_spec.1

/-- Actual good-pair norm base change proves compatibility of the actual
descended coordinates on every nested stable good pair. -/
theorem galoisNormCoordinate_norm (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (D F : FiniteLayer K N) (hDF : D ≤ F)
    (hgD : IsGoodFiniteLayer K M D) (hgF : IsGoodFiniteLayer K M F)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (hsF : ∀ σ : N ≃ₐ[M] N, F.val.map (σ.restrictScalars K).toAlgHom = F.val) :
    FiniteLayer.norm (finiteLayerPullbackLayer K M D) (finiteLayerPullbackLayer K M F)
      (finiteLayerPullback_mono K M hDF) (galoisNormCoordinate K M N β hβ F hsF) =
        galoisNormCoordinate K M N β hβ D hsD := by
  apply (finiteLayerPullbackTo K M D).injective
  exact (goodFinitePair_norm K M D F hDF hgD hgF _).symm.trans
    ((congrArg (FiniteLayer.norm D F hDF) (galoisNormCoordinate_spec K M N β hβ F hsF)).trans
      ((normLimitEval_norm K N D F hDF β).trans
        (galoisNormCoordinate_spec K M N β hβ D hsD).symm))

variable [Algebra.IsAlgebraic K N]

/-- A chosen actual stable good target field dominates each original finite
source field through its original pullback. -/
def galoisGoodSourceUpper (C : FiniteLayer K M) : FiniteLayer K N :=
  (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteLayer.map (IsScalarTower.toAlgHom K M N) C)).choose

theorem galoisGoodSourceUpper_spec (C : FiniteLayer K M) :
    IsGoodFiniteLayer K M (galoisGoodSourceUpper K M N C) ∧
      (∀ σ : N ≃ₐ[M] N, (galoisGoodSourceUpper K M N C).val.map
        (σ.restrictScalars K).toAlgHom = (galoisGoodSourceUpper K M N C).val) ∧
      C ≤ finiteLayerPullbackLayer K M (galoisGoodSourceUpper K M N C) := by
  have h := (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteLayer.map (IsScalarTower.toAlgHom K M N) C)).choose_spec
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  intro m hm
  exact h.1 ⟨m, hm, rfl⟩

/-- The original norm of the descended coordinate defines a coordinate at
every original finite source field, before any compatibility is assumed. -/
def galoisSourceCoordinate (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (C : FiniteLayer K M) : C.val :=
  FiniteLayer.norm C (finiteLayerPullbackLayer K M (galoisGoodSourceUpper K M N C))
    (galoisGoodSourceUpper_spec K M N C).2.2
    (galoisNormCoordinate K M N β hβ (galoisGoodSourceUpper K M N C)
      (galoisGoodSourceUpper_spec K M N C).2.1)

/-- Common actual stable good upper fields and original norm transitivity
prove independence of the chosen upper field. -/
theorem galoisSourceCoordinate_eq_norm (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (C : FiniteLayer K M) (D : FiniteLayer K N) (hgD : IsGoodFiniteLayer K M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (hCD : C ≤ finiteLayerPullbackLayer K M D) :
    galoisSourceCoordinate K M N β hβ C =
      FiniteLayer.norm C (finiteLayerPullbackLayer K M D) hCD
        (galoisNormCoordinate K M N β hβ D hsD) := by
  let U := galoisGoodSourceUpper K M N C
  have hU := galoisGoodSourceUpper_spec K M N C
  obtain ⟨F, hUF, hDF, hgF, hsF⟩ :=
    exists_galois_stable_goodFiniteLayer_ge_pair K M N U D
  let CU := finiteLayerPullbackLayer K M U
  let CD := finiteLayerPullbackLayer K M D
  let CF := finiteLayerPullbackLayer K M F
  let aF := galoisNormCoordinate K M N β hβ F hsF
  have hUp : CU ≤ CF := finiteLayerPullback_mono K M hUF
  have hDp : CD ≤ CF := finiteLayerPullback_mono K M hDF
  have hvU := galoisNormCoordinate_norm K M N β hβ U F hUF hU.1 hgF hU.2.1 hsF
  have hvD := galoisNormCoordinate_norm K M N β hβ D F hDF hgD hgF hsD hsF
  change FiniteLayer.norm C CU hU.2.2 (galoisNormCoordinate K M N β hβ U hU.2.1) = _
  exact (congrArg (FiniteLayer.norm C CU hU.2.2) hvU.symm).trans
    ((FiniteLayer.norm_norm C CU CF hU.2.2 hUp aF).trans
      ((FiniteLayer.norm_norm C CD CF hCD hDp aF).symm.trans
        (congrArg (FiniteLayer.norm C CD hCD) hvD)))

/-- Compatibility at every original source inclusion is proved from the
actual coordinate independence and actual finite norm transitivity. -/
theorem galoisSourceCoordinate_norm (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (C C' : FiniteLayer K M) (hCC' : C ≤ C') :
    FiniteLayer.norm C C' hCC' (galoisSourceCoordinate K M N β hβ C') =
      galoisSourceCoordinate K M N β hβ C := by
  let D := galoisGoodSourceUpper K M N C'
  have hD := galoisGoodSourceUpper_spec K M N C'
  have hCD : C ≤ finiteLayerPullbackLayer K M D := hCC'.trans hD.2.2
  exact (FiniteLayer.norm_norm C C' (finiteLayerPullbackLayer K M D)
    hCC' hD.2.2 (galoisNormCoordinate K M N β hβ D hD.2.1)).trans
      (galoisSourceCoordinate_eq_norm K M N β hβ C D hD.1 hD.2.1 hCD).symm

/-- Reconstruction produces an element of the same original source norm
limit, using compatibility just proved for all original finite fields. -/
def galoisNormDescent (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β) : NormLimit K M :=
  (existsUnique_normLimit_of_compatible K M (galoisSourceCoordinate K M N β hβ)
    (galoisSourceCoordinate_norm K M N β hβ)).choose

theorem normLimitEval_galoisNormDescent (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (C : FiniteLayer K M) :
    normLimitEval K M C (galoisNormDescent K M N β hβ) =
      galoisSourceCoordinate K M N β hβ C :=
  (existsUnique_normLimit_of_compatible K M (galoisSourceCoordinate K M N β hβ)
    (galoisSourceCoordinate_norm K M N β hβ)).choose_spec.1 C

/-- At every actual stable good field, descent retains its unique actual
pullback coordinate exactly. -/
theorem normLimitEval_galoisNormDescent_pullback (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β)
    (D : FiniteLayer K N) (hgD : IsGoodFiniteLayer K M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    normLimitEval K M (finiteLayerPullbackLayer K M D) (galoisNormDescent K M N β hβ) =
      galoisNormCoordinate K M N β hβ D hsD := by
  exact (normLimitEval_galoisNormDescent K M N β hβ _).trans
    ((galoisSourceCoordinate_eq_norm K M N β hβ _ D hgD hsD le_rfl).trans
      (FiniteLayer.norm_self _ _))

variable [Algebra.IsAlgebraic K M]

/-- Every element in the actual source image is fixed by the actual original
relative automorphism action, proved on cofinal stable good coordinates. -/
theorem normLimitMap_finiteNormLimitMap_relative (σ : N ≃ₐ[M] N) (α : NormLimit K M) :
    normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N α) =
      finiteNormLimitMap K M N α := by
  apply NormLimit.ext_cofinal K N
    (fun D => IsGoodFiniteLayer K M D ∧ ∀ τ : N ≃ₐ[M] N,
      D.val.map (τ.restrictScalars K).toAlgHom = D.val)
    (galoisStableGoodFiniteLayers_cofinal K M N)
  intro D ⟨hgD, hsD⟩
  apply Subtype.val_injective
  have hi : FiniteLayer.map (σ.restrictScalars K).symm.toAlgHom D = D :=
    Subtype.ext (hsD σ.symm)
  have h := coe_normLimitEval_normLimitMap (σ.restrictScalars K)
    (finiteNormLimitMap K M N α) D
  rw [hi] at h
  exact h.trans ((congrArg σ (coe_normLimitEval_finiteNormLimitMap K M N D hgD α)).trans
    ((σ.commutes _).trans (coe_normLimitEval_finiteNormLimitMap K M N D hgD α).symm))

/-- The actual reconstructed original family maps back to the given fixed
family, by the literal good-coordinate formula and original cofinality. -/
theorem finiteNormLimitMap_galoisNormDescent (β : NormLimit K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β) :
    finiteNormLimitMap K M N (galoisNormDescent K M N β hβ) = β := by
  apply NormLimit.ext_cofinal K N
    (fun D => IsGoodFiniteLayer K M D ∧ ∀ σ : N ≃ₐ[M] N,
      D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (galoisStableGoodFiniteLayers_cofinal K M N)
  intro D ⟨hgD, hsD⟩
  exact (normLimitEval_finiteNormLimitMap K M N D hgD _).trans
    ((congrArg (finiteLayerPullbackTo K M D)
      (normLimitEval_galoisNormDescent_pullback K M N β hβ D hgD hsD)).trans
        (galoisNormCoordinate_spec K M N β hβ D hsD))

/-- The original fixed families are precisely the image of the actual
finite-inclusion map; all descent and compatibility obligations are proved. -/
theorem mem_range_finiteNormLimitMap_iff_fixed (β : NormLimit K N) :
    β ∈ Set.range (finiteNormLimitMap K M N) ↔
      ∀ σ : N ≃ₐ[M] N, normLimitMap (σ.restrictScalars K) β = β := by
  constructor
  · rintro ⟨α, rfl⟩ σ
    exact normLimitMap_finiteNormLimitMap_relative K M N σ α
  · intro hβ
    exact ⟨galoisNormDescent K M N β hβ, finiteNormLimitMap_galoisNormDescent K M N β hβ⟩

end OriginalFamilies

section ValuedFields

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K N]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The relative action is the actual original norm-field action after
the original restriction of scalars. -/
def finiteNormLimitGaloisAction (hN : IsAPF K N) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K N p hN hInfiniteN
    (N ≃ₐ[M] N) →* (NormLimit K N ≃+* NormLimit K N) := by
  let := normLimitField K N p hN hInfiniteN
  exact (normLimitAut K p hN hInfiniteN).comp (AlgEquiv.restrictScalarsHom K)

@[simp]
theorem finiteNormLimitGaloisAction_apply (hN : IsAPF K N)
    (hInfiniteN : ¬ Module.Finite K N) (σ : N ≃ₐ[M] N) (β : NormLimit K N) :
    letI := normLimitField K N p hN hInfiniteN
    finiteNormLimitGaloisAction K M N p hN hInfiniteN σ β =
      normLimitMap (σ.restrictScalars K) β := rfl

/-- Faithfulness is produced by the proved original action and the actual
injective restriction of scalars; it is not an additional hypothesis. -/
theorem finiteNormLimitGaloisAction_injective (hN : IsAPF K N)
    (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K N p hN hInfiniteN
    Function.Injective (finiteNormLimitGaloisAction K M N p hN hInfiniteN) := by
  let := normLimitField K N p hN hInfiniteN
  exact (normLimitAut_injective K N p hN hInfiniteN).comp
    (AlgEquiv.restrictScalars_injective K)

/-- The canonical action on the same original target field. -/
@[instance_reducible]
def finiteNormLimitGaloisMulSemiringAction (hN : IsAPF K N)
    (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K N p hN hInfiniteN
    MulSemiringAction (N ≃ₐ[M] N) (NormLimit K N) := by
  let := normLimitField K N p hN hInfiniteN
  exact MulSemiringAction.compHom (NormLimit K N)
    (finiteNormLimitGaloisAction K M N p hN hInfiniteN)

variable [Algebra.IsSeparable K M] [Module.Finite M N] [IsGalois M N]

/-- The actual fixed field of the actual relative action is the literal
image of the checked original field homomorphism. -/
theorem fixedPoints_finiteNormLimitGaloisAction (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
    (FixedPoints.subfield (N ≃ₐ[M] N) (NormLimit K N) : Set (NormLimit K N)) =
      Set.range (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  exact Set.ext (fun β => (mem_range_finiteNormLimitMap_iff_fixed K M N β).symm)

/-- The official finite Galois-group structure is proved from genuine
faithfulness, the original scalar action and the proved fixed-family descent. -/
theorem finiteNormLimit_isGaloisGroup (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    letI := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
    IsGaloisGroup (N ≃ₐ[M] N) (NormLimit K M) (NormLimit K N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  constructor
  · constructor
    intro σ τ h
    apply finiteNormLimitGaloisAction_injective K M N p hN hInfiniteN
    exact RingEquiv.ext h
  · constructor
    intro σ α β
    change normLimitMap (σ.restrictScalars K) (finiteNormLimitMap K M N α * β) =
      finiteNormLimitMap K M N α * normLimitMap (σ.restrictScalars K) β
    rw [normLimitMap_mul, normLimitMap_finiteNormLimitMap_relative K M N σ α]
  · constructor
    intro β hβ
    exact (mem_range_finiteNormLimitMap_iff_fixed K M N β).mpr hβ

/-- Finite Artin theory proves finiteness over the actual embedded source,
without assuming finiteness of the norm-field extension. -/
theorem finiteDimensional_finiteNormLimit_of_isGalois (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    FiniteDimensional (NormLimit K M) (NormLimit K N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  let := finiteNormLimit_isGaloisGroup K M N p hM hN hInfiniteM hInfiniteN
  exact IsGaloisGroup.finiteDimensional (N ≃ₐ[M] N) (NormLimit K M) (NormLimit K N)

/-- The original target norm field is Galois over the actual embedded source. -/
theorem isGalois_finiteNormLimit (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    IsGalois (NormLimit K M) (NormLimit K N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  let := finiteNormLimit_isGaloisGroup K M N p hM hN hInfiniteM hInfiniteN
  exact IsGaloisGroup.isGalois (N ≃ₐ[M] N) (NormLimit K M) (NormLimit K N)

/-- The actual finite Galois norm-field extension retains the full original degree. -/
theorem finrank_finiteNormLimit_of_isGalois (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    Module.finrank (NormLimit K M) (NormLimit K N) = Module.finrank M N := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  let := finiteNormLimit_isGaloisGroup K M N p hM hN hInfiniteM hInfiniteN
  exact (IsGaloisGroup.card_eq_finrank (N ≃ₐ[M] N) (NormLimit K M) (NormLimit K N)).symm.trans
    (IsGalois.card_aut_eq_finrank M N)

/-- The actual original relative action identifies the actual two Galois groups. -/
def finiteNormLimitGaloisEquiv (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    (N ≃ₐ[M] N) ≃* (NormLimit K N ≃ₐ[NormLimit K M] NormLimit K N) := by
  let := normLimitField K M p hM hInfiniteM
  let := normLimitField K N p hN hInfiniteN
  let := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
  let := finiteNormLimitGaloisMulSemiringAction K M N p hN hInfiniteN
  let := finiteNormLimit_isGaloisGroup K M N p hM hN hInfiniteM hInfiniteN
  exact IsGaloisGroup.mulEquivAlgEquiv (N ≃ₐ[M] N) (NormLimit K M) (NormLimit K N)

@[simp]
theorem finiteNormLimitGaloisEquiv_apply (hM : IsAPF K M) (hN : IsAPF K N)
    (hInfiniteM : ¬ Module.Finite K M) (hInfiniteN : ¬ Module.Finite K N)
    (σ : N ≃ₐ[M] N) (β : NormLimit K N) :
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitField K N p hN hInfiniteN
    letI := (finiteNormLimitRingHom K M N p hM hN hInfiniteM hInfiniteN).toAlgebra
    finiteNormLimitGaloisEquiv K M N p hM hN hInfiniteM hInfiniteN σ β =
      normLimitMap (σ.restrictScalars K) β := rfl

end ValuedFields

end FontaineWintenberger
