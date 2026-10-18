/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
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
    (E : FiniteIntermediateField K N) :
    ∃ D : FiniteIntermediateField K N,
      (IsGoodFiniteLayer K M D ∧ ∀ σ : N ≃ₐ[M] N,
        D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧ E ≤ D := by
  obtain ⟨D, hED, hg, hs, _⟩ := exists_galois_stable_goodFiniteLayer_ge K M N E
  exact ⟨D, ⟨hg, hs⟩, hED⟩

/-- A fixed original family has a unique original pullback coordinate at
every original stable finite field. -/
theorem existsUnique_galoisNormCoordinate (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    ∃! a : FiniteIntermediateField.pullback K M D,
      FiniteIntermediateField.pullbackTo K M D a = FieldOfNorms.coord K N D β := by
  have hfixed : ∀ σ : N ≃ₐ[M] N,
      σ (FieldOfNorms.coord K N D β : N) = (FieldOfNorms.coord K N D β : N) := by
    intro σ
    have hi : FiniteIntermediateField.map (σ.restrictScalars K).symm.toAlgHom D = D :=
      Subtype.ext (hD σ.symm)
    have h := coe_fieldOfNormsEval_fieldOfNormsMap (σ.restrictScalars K) β D
    rw [hβ σ, hi] at h
    exact h.symm
  obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := M) (FieldOfNorms.coord K N D β : N)).mpr hfixed
  have hmD : algebraMap M N m ∈ D.val := hm.symm ▸ (FieldOfNorms.coord K N D β).property
  let a : FiniteIntermediateField.pullback K M D := ⟨m, hmD⟩
  have ha : FiniteIntermediateField.pullbackTo K M D a = FieldOfNorms.coord K N D β := Subtype.ext
      hm
  exact ⟨a, ha, fun b hb => (FiniteIntermediateField.pullbackTo K M D).injective (hb.trans ha.symm)⟩

/-- The unique preimage lies in the original source pullback field. -/
def galoisNormCoordinate (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FiniteIntermediateField.pullback K M D :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose

/-- Original inclusion of the actual preimage recovers exactly the original coordinate. -/
theorem galoisNormCoordinate_spec (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FiniteIntermediateField.pullbackTo K M D (galoisNormCoordinate K M N β hβ D hD) =
      FieldOfNorms.coord K N D β :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose_spec.1

/-- Actual good-pair norm base change proves compatibility of the actual
descended coordinates on every nested stable good pair. -/
theorem galoisNormCoordinate_norm (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D F : FiniteIntermediateField K N) (hDF : D ≤ F)
    (hgD : IsGoodFiniteLayer K M D) (hgF : IsGoodFiniteLayer K M F)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (hsF : ∀ σ : N ≃ₐ[M] N, F.val.map (σ.restrictScalars K).toAlgHom = F.val) :
    FiniteIntermediateField.norm (FiniteIntermediateField.pullbackLayer K M D)
        (FiniteIntermediateField.pullbackLayer K M F)
      (FiniteIntermediateField.pullback_mono K M hDF) (galoisNormCoordinate K M N β hβ F hsF) =
        galoisNormCoordinate K M N β hβ D hsD := by
  apply (FiniteIntermediateField.pullbackTo K M D).injective
  exact (goodFinitePair_norm K M D F hDF hgD hgF _).symm.trans
    ((congrArg (FiniteIntermediateField.norm D F hDF) (galoisNormCoordinate_spec K M N β hβ F
        hsF)).trans
      ((FieldOfNorms.coord_norm K N D F hDF β).trans
        (galoisNormCoordinate_spec K M N β hβ D hsD).symm))

variable [Algebra.IsAlgebraic K N]

/-- A chosen actual stable good target field dominates each original finite
source field through its original pullback. -/
def galoisGoodSourceUpper (C : FiniteIntermediateField K M) : FiniteIntermediateField K N :=
  (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteIntermediateField.map (IsScalarTower.toAlgHom K M N) C)).choose

theorem galoisGoodSourceUpper_spec (C : FiniteIntermediateField K M) :
    IsGoodFiniteLayer K M (galoisGoodSourceUpper K M N C) ∧
      (∀ σ : N ≃ₐ[M] N, (galoisGoodSourceUpper K M N C).val.map
        (σ.restrictScalars K).toAlgHom = (galoisGoodSourceUpper K M N C).val) ∧
      C ≤ FiniteIntermediateField.pullbackLayer K M (galoisGoodSourceUpper K M N C) := by
  have h := (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteIntermediateField.map (IsScalarTower.toAlgHom K M N) C)).choose_spec
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  intro m hm
  exact h.1 ⟨m, hm, rfl⟩

/-- The original norm of the descended coordinate defines a coordinate at
every original finite source field, before any compatibility is assumed. -/
def galoisSourceCoordinate (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) : C.val :=
  FiniteIntermediateField.norm C (FiniteIntermediateField.pullbackLayer K M (galoisGoodSourceUpper
      K M N C))
    (galoisGoodSourceUpper_spec K M N C).2.2
    (galoisNormCoordinate K M N β hβ (galoisGoodSourceUpper K M N C)
      (galoisGoodSourceUpper_spec K M N C).2.1)

/-- Common actual stable good upper fields and original norm transitivity
prove independence of the chosen upper field. -/
theorem galoisSourceCoordinate_eq_norm (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) (D : FiniteIntermediateField K N) (hgD : IsGoodFiniteLayer K
        M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (hCD : C ≤ FiniteIntermediateField.pullbackLayer K M D) :
    galoisSourceCoordinate K M N β hβ C =
      FiniteIntermediateField.norm C (FiniteIntermediateField.pullbackLayer K M D) hCD
        (galoisNormCoordinate K M N β hβ D hsD) := by
  let U := galoisGoodSourceUpper K M N C
  have hU := galoisGoodSourceUpper_spec K M N C
  obtain ⟨F, hUF, hDF, hgF, hsF⟩ :=
    exists_galois_stable_goodFiniteLayer_ge_pair K M N U D
  let CU := FiniteIntermediateField.pullbackLayer K M U
  let CD := FiniteIntermediateField.pullbackLayer K M D
  let CF := FiniteIntermediateField.pullbackLayer K M F
  let aF := galoisNormCoordinate K M N β hβ F hsF
  have hUp : CU ≤ CF := FiniteIntermediateField.pullback_mono K M hUF
  have hDp : CD ≤ CF := FiniteIntermediateField.pullback_mono K M hDF
  have hvU := galoisNormCoordinate_norm K M N β hβ U F hUF hU.1 hgF hU.2.1 hsF
  have hvD := galoisNormCoordinate_norm K M N β hβ D F hDF hgD hgF hsD hsF
  change FiniteIntermediateField.norm C CU hU.2.2 (galoisNormCoordinate K M N β hβ U hU.2.1) = _
  exact (congrArg (FiniteIntermediateField.norm C CU hU.2.2) hvU.symm).trans
    ((FiniteIntermediateField.norm_norm C CU CF hU.2.2 hUp aF).trans
      ((FiniteIntermediateField.norm_norm C CD CF hCD hDp aF).symm.trans
        (congrArg (FiniteIntermediateField.norm C CD hCD) hvD)))

/-- Compatibility at every original source inclusion is proved from the
actual coordinate independence and actual finite norm transitivity. -/
theorem galoisSourceCoordinate_norm (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C C' : FiniteIntermediateField K M) (hCC' : C ≤ C') :
    FiniteIntermediateField.norm C C' hCC' (galoisSourceCoordinate K M N β hβ C') =
      galoisSourceCoordinate K M N β hβ C := by
  let D := galoisGoodSourceUpper K M N C'
  have hD := galoisGoodSourceUpper_spec K M N C'
  have hCD : C ≤ FiniteIntermediateField.pullbackLayer K M D := hCC'.trans hD.2.2
  exact (FiniteIntermediateField.norm_norm C C' (FiniteIntermediateField.pullbackLayer K M D)
    hCC' hD.2.2 (galoisNormCoordinate K M N β hβ D hD.2.1)).trans
      (galoisSourceCoordinate_eq_norm K M N β hβ C D hD.1 hD.2.1 hCD).symm

/-- Reconstruction produces an element of the same original source norm
limit, using compatibility just proved for all original finite fields. -/
def galoisNormDescent (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β) : FieldOfNorms K M :=
  (existsUnique_fieldOfNorms_of_compatible K M (galoisSourceCoordinate K M N β hβ)
    (galoisSourceCoordinate_norm K M N β hβ)).choose

theorem FieldOfNorms.coord_galoisNormDescent (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M C (galoisNormDescent K M N β hβ) =
      galoisSourceCoordinate K M N β hβ C :=
  (existsUnique_fieldOfNorms_of_compatible K M (galoisSourceCoordinate K M N β hβ)
    (galoisSourceCoordinate_norm K M N β hβ)).choose_spec.1 C

/-- At every actual stable good field, descent retains its unique actual
pullback coordinate exactly. -/
theorem FieldOfNorms.coord_galoisNormDescent_pullback (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N) (hgD : IsGoodFiniteLayer K M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) (galoisNormDescent K M N β
        hβ) =
      galoisNormCoordinate K M N β hβ D hsD := by
  exact (FieldOfNorms.coord_galoisNormDescent K M N β hβ _).trans
    ((galoisSourceCoordinate_eq_norm K M N β hβ _ D hgD hsD le_rfl).trans
      (FiniteIntermediateField.norm_self _ _))

variable [Algebra.IsAlgebraic K M]

/-- Every element in the actual source image is fixed by the actual original
relative automorphism action, proved on cofinal stable good coordinates. -/
theorem FieldOfNorms.map_finiteFieldOfNormsMap_relative (σ : N ≃ₐ[M] N) (α : FieldOfNorms K M) :
    FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N α) =
      FieldOfNorms.finiteMap K M N α := by
  apply FieldOfNorms.ext_cofinal K N
    (fun D => IsGoodFiniteLayer K M D ∧ ∀ τ : N ≃ₐ[M] N,
      D.val.map (τ.restrictScalars K).toAlgHom = D.val)
    (galoisStableGoodFiniteLayers_cofinal K M N)
  intro D ⟨hgD, hsD⟩
  apply Subtype.val_injective
  have hi : FiniteIntermediateField.map (σ.restrictScalars K).symm.toAlgHom D = D :=
    Subtype.ext (hsD σ.symm)
  have h := coe_fieldOfNormsEval_fieldOfNormsMap (σ.restrictScalars K)
    (FieldOfNorms.finiteMap K M N α) D
  rw [hi] at h
  exact h.trans ((congrArg σ (coe_fieldOfNormsEval_finiteFieldOfNormsMap K M N D hgD α)).trans
    ((σ.commutes _).trans (coe_fieldOfNormsEval_finiteFieldOfNormsMap K M N D hgD α).symm))

/-- The actual reconstructed original family maps back to the given fixed
family, by the literal good-coordinate formula and original cofinality. -/
theorem FieldOfNorms.finiteMap_galoisNormDescent (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β) :
    FieldOfNorms.finiteMap K M N (galoisNormDescent K M N β hβ) = β := by
  apply FieldOfNorms.ext_cofinal K N
    (fun D => IsGoodFiniteLayer K M D ∧ ∀ σ : N ≃ₐ[M] N,
      D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (galoisStableGoodFiniteLayers_cofinal K M N)
  intro D ⟨hgD, hsD⟩
  exact (FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hgD _).trans
    ((congrArg (FiniteIntermediateField.pullbackTo K M D)
      (FieldOfNorms.coord_galoisNormDescent_pullback K M N β hβ D hgD hsD)).trans
        (galoisNormCoordinate_spec K M N β hβ D hsD))

/-- The original fixed families are precisely the image of the actual
finite-inclusion map; all descent and compatibility obligations are proved. -/
theorem mem_range_finiteFieldOfNormsMap_iff_fixed (β : FieldOfNorms K N) :
    β ∈ Set.range (FieldOfNorms.finiteMap K M N) ↔
      ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β := by
  constructor
  · rintro ⟨α, rfl⟩ σ
    exact FieldOfNorms.map_finiteFieldOfNormsMap_relative K M N σ α
  · intro hβ
    exact ⟨galoisNormDescent K M N β hβ, FieldOfNorms.finiteMap_galoisNormDescent K M N β hβ⟩

end OriginalFamilies

section ValuedFields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K N]

/-- The relative action is the actual original norm-field action after
the original restriction of scalars. -/
def FieldOfNorms.finiteGaloisAction [IsAPF K N] [Fact (¬ Module.Finite K N)] :
    (N ≃ₐ[M] N) →* (FieldOfNorms K N ≃+* FieldOfNorms K N) := by
  exact (FieldOfNorms.aut K N).comp (AlgEquiv.restrictScalarsHom K)

@[simp]
theorem FieldOfNorms.finiteGaloisAction_apply [IsAPF K N]
    [Fact (¬ Module.Finite K N)] (σ : N ≃ₐ[M] N) (β : FieldOfNorms K N) :
    FieldOfNorms.finiteGaloisAction K M N σ β =
      FieldOfNorms.map (σ.restrictScalars K) β := rfl

/-- Faithfulness is produced by the proved original action and the actual
injective restriction of scalars; it is not an additional hypothesis. -/
theorem FieldOfNorms.finiteGaloisAction_injective [IsAPF K N]
    [Fact (¬ Module.Finite K N)] :
    Function.Injective (FieldOfNorms.finiteGaloisAction K M N) := by
  exact (FieldOfNorms.aut_injective K N).comp
    (AlgEquiv.restrictScalars_injective K)

/-- The canonical action on the same original target field. -/
@[instance_reducible]
def FieldOfNorms.finiteGaloisMulSemiringAction [IsAPF K N]
    [Fact (¬ Module.Finite K N)] :
    MulSemiringAction (N ≃ₐ[M] N) (FieldOfNorms K N) := by
  exact MulSemiringAction.compHom (FieldOfNorms K N)
    (FieldOfNorms.finiteGaloisAction K M N)

variable [Algebra.IsSeparable K M] [Module.Finite M N] [IsGalois M N]

/-- The actual fixed field of the actual relative action is the literal
image of the checked original field homomorphism. -/
theorem fixedPoints_finiteFieldOfNormsGaloisAction [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := FieldOfNorms.finiteGaloisMulSemiringAction K M N
    (FixedPoints.subfield (N ≃ₐ[M] N) (FieldOfNorms K N) : Set (FieldOfNorms K N)) =
      Set.range (FieldOfNorms.finiteRingHom K M N) := by
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  exact Set.ext (fun β => (mem_range_finiteFieldOfNormsMap_iff_fixed K M N β).symm)

/-- The official finite Galois-group structure is proved from genuine
faithfulness, the original scalar action and the proved fixed-family descent. -/
theorem FieldOfNorms.finite_isGaloisGroup [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    letI := FieldOfNorms.finiteGaloisMulSemiringAction K M N
    IsGaloisGroup (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  constructor
  · constructor
    intro σ τ h
    apply FieldOfNorms.finiteGaloisAction_injective K M N
    exact RingEquiv.ext h
  · constructor
    intro σ α β
    change FieldOfNorms.map (σ.restrictScalars K) (FieldOfNorms.finiteMap K M N α * β) =
      FieldOfNorms.finiteMap K M N α * FieldOfNorms.map (σ.restrictScalars K) β
    rw [FieldOfNorms.map_mul, FieldOfNorms.map_finiteFieldOfNormsMap_relative K M N σ α]
  · constructor
    intro β hβ
    exact (mem_range_finiteFieldOfNormsMap_iff_fixed K M N β).mpr hβ

/-- Finite Artin theory proves finiteness over the actual embedded source,
without assuming finiteness of the norm-field extension. -/
theorem finiteDimensional_finiteFieldOfNorms_of_isGalois [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact IsGaloisGroup.finiteDimensional (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)

/-- The original target norm field is Galois over the actual embedded source. -/
theorem isGalois_finiteFieldOfNorms [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    IsGalois (FieldOfNorms K M) (FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact IsGaloisGroup.isGalois (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)

/-- The actual finite Galois norm-field extension retains the full original degree. -/
theorem finrank_finiteFieldOfNorms_of_isGalois [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    Module.finrank (FieldOfNorms K M) (FieldOfNorms K N) = Module.finrank M N := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact (IsGaloisGroup.card_eq_finrank (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)).symm.trans
    (IsGalois.card_aut_eq_finrank M N)

/-- The actual original relative action identifies the actual two Galois groups. -/
def FieldOfNorms.finiteGaloisEquiv [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    (N ≃ₐ[M] N) ≃* (FieldOfNorms K N ≃ₐ[FieldOfNorms K M] FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact IsGaloisGroup.mulEquivAlgEquiv (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)

@[simp]
theorem FieldOfNorms.finiteGaloisEquiv_apply [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    (σ : N ≃ₐ[M] N) (β : FieldOfNorms K N) :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    FieldOfNorms.finiteGaloisEquiv K M N σ β =
      FieldOfNorms.map (σ.restrictScalars K) β := rfl

end ValuedFields

end FontaineWintenberger
