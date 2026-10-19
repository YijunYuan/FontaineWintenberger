/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.FieldTheory.NormalClosure
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import FontaineWintenberger.FieldOfNorms.Structure.ResidueEmbedding
public import FontaineWintenberger.FieldOfNorms.Basic.Valuation
public import FontaineWintenberger.Ramification.Embedding.Basic
public import FontaineWintenberger.FieldOfNorms.Layers.GaloisGood
public import FontaineWintenberger.FieldOfNorms.Functor.RingHom
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Galois actions on the field of norms

## Faithfulness of the norm-field action

Norm-family coordinates on finite stable fields separate
automorphisms through constants and an uniformizer. Normality
of the ambient extension is not needed.

## Finite Galois extensions of the norm fields

Fixed norm families descend through stable good fields and
finite norms. The faithful action then supplies the
finite Galois extension and its degree by finite Artin theory.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Coordinates

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- At a stable finite intermediate field, fixed norm families have fixed
    coordinates. -/
theorem FieldOfNorms.coord_fixed_of_fieldOfNormsMap_fixed (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : FieldOfNorms K L, FieldOfNorms.map σ x = x)
    (E : FiniteIntermediateField K L) (hE : FiniteIntermediateField.map σ.toAlgHom E = E)
    (x : FieldOfNorms K L) :
    σ (FieldOfNorms.coord K L E x : L) = (FieldOfNorms.coord K L E x : L) := by
  have hEinv : FiniteIntermediateField.map σ.symm.toAlgHom E = E := by
    have h := (FiniteIntermediateField.mapOrderIso σ).left_inv E
    change FiniteIntermediateField.map σ.symm.toAlgHom (FiniteIntermediateField.map σ.toAlgHom E) =
        E at h
    rwa [hE] at h
  have h := coe_fieldOfNormsEval_fieldOfNormsMap σ x E
  rw [hσ x, hEinv] at h
  exact h.symm

end Coordinates

section Valued

open IsDiscreteValuationRing IsLocalRing

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every coordinate of the norm-family uniformizer is integral. -/
def FieldOfNorms.uniformizerCoordinateInteger [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (E : FiniteIntermediateField K L) : spectralIntegerRing K E.val :=
  ⟨FieldOfNorms.coord K L E (FieldOfNorms.uniformizer K L),
    FieldOfNorms.coord_mem_of_valuation_le_one K L _ (by
      rw [FieldOfNorms.valuation_fieldOfNormsUniformizer]
      change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
      exact WithZero.exp_le_exp.mpr (by omega)) E⟩

/-- Above the maximal unramified field the coordinate is an uniformizer. -/
theorem FieldOfNorms.uniformizerCoordinateInteger_irreducible [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (E : FiniteIntermediateField K L)
    (hE : apfMaximalUnramified K L ≤ E) :
    Irreducible (FieldOfNorms.uniformizerCoordinateInteger K L E) := by
  let z := FieldOfNorms.uniformizerCoordinateInteger K L E
  let R := spectralIntegerRing K E.val
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation E.val (z : E.val) =
      WithZero.exp (-1 : ℤ) :=
    (FieldOfNorms.valuation_eq_coordinate_of_maximalUnramified_le K L E hE _).symm.trans
      (FieldOfNorms.valuation_fieldOfNormsUniformizer K L)
  have hzval : addVal R z = 1 := by
    change (IsDiscreteValuationRing.maximalIdeal R).valuation E.val
      (algebraMap R E.val z) = WithZero.exp (-1 : ℤ) at hv
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal] at hv
    induction h : addVal R z using ENat.recTopCoe with
    | top =>
      rw [h] at hv
      change (0 : WithZero (Multiplicative ℤ))⁻¹ = WithZero.exp (-1 : ℤ) at hv
      rw [inv_zero] at hv
      exact False.elim (WithZero.exp_ne_zero hv.symm)
    | coe n =>
      rw [h] at hv
      change WithZero.exp (-(n : ℤ)) = WithZero.exp (-1 : ℤ) at hv
      have hn : (n : ℤ) = 1 := neg_injective (WithZero.exp_injective hv)
      have hn' : n = 1 := by exact_mod_cast hn
      simp only [hn', Nat.cast_one]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  exact ((addVal_eq_iff_associated z π).mp
    (hzval.trans (addVal_uniformizer hπ).symm)).irreducible_iff.mpr hπ

/-- The constants force the restriction to a stable field
to act trivially on its entire residue field. -/
theorem FiniteIntermediateField.residue_eq_of_fieldOfNormsMap_fixed [IsAPF K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : FieldOfNorms K L, FieldOfNorms.map σ x = x)
    (E : FiniteIntermediateField K L) (hE : FiniteIntermediateField.map σ.toAlgHom E = E)
    (hK₁ : apfMaximalTame K L ≤ E) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L)) :
    spectralResidueInclusion K s.toAlgHom =
      spectralResidueInclusion K (AlgHom.id K E.val) := by
  ext a
  obtain ⟨c, hc⟩ := (residueCoordinateEquiv K L E hK₁).surjective a
  rw [← hc, residueCoordinateEquiv_apply]
  change IsLocalRing.residue _ (spectralIntegerInclusion K s.toAlgHom
      (residueIntegralCoordinate K L E hK₁ c)) =
    IsLocalRing.residue _ (residueIntegralCoordinate K L E hK₁ c)
  congr 1
  apply Subtype.ext
  apply Subtype.val_injective
  change (s (residueIntegralCoordinate K L E hK₁ c : E.val) : L) =
    ((residueIntegralCoordinate K L E hK₁ c : E.val) : L)
  rw [hs]
  have h := FieldOfNorms.coord_fixed_of_fieldOfNormsMap_fixed σ hσ E hE
    (residueConstants K L c)
  rw [FieldOfNorms.coord_residueConstants K L E hK₁] at h
  exact h

/-- Fixing the norm families makes the restriction on every
stable field above the maximal tame part the identity. -/
theorem FiniteIntermediateField.aut_eq_of_fieldOfNormsMap_fixed [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : FieldOfNorms K L, FieldOfNorms.map σ x = x)
    (E : FiniteIntermediateField K L) (hE : FiniteIntermediateField.map σ.toAlgHom E = E)
    (hK₁ : apfMaximalTame K L ≤ E) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L)) : s = AlgEquiv.refl := by
  have hres := FiniteIntermediateField.residue_eq_of_fieldOfNormsMap_fixed K L σ hσ E hE hK₁ s hs
  let π := FieldOfNorms.uniformizerCoordinateInteger K L E
  have hπ : Irreducible π := FieldOfNorms.uniformizerCoordinateInteger_irreducible K L
    E ((apfMaximalUnramified_le_maximalTame K L).trans hK₁)
  have hfix : spectralIntegerInclusion K s.toAlgHom π =
      spectralIntegerInclusion K (AlgHom.id K E.val) π := by
    apply Subtype.ext
    apply Subtype.val_injective
    change (s (π : E.val) : L) = ((π : E.val) : L)
    rw [hs]
    exact FieldOfNorms.coord_fixed_of_fieldOfNormsMap_fixed σ hσ E hE
      (FieldOfNorms.uniformizer K L)
  have ht : embeddingIntegralOrder K s.toAlgHom (AlgHom.id K E.val) = ⊤ := by
    rw [embeddingIntegralOrder_eq_uniformizer K _ _ hres hπ, hfix, sub_self, addVal_zero]
  have he := (embeddingIntegralOrder_eq_top_iff K _ _).mp ht
  apply AlgEquiv.ext
  intro a
  exact AlgHom.congr_fun he a

/-- Norm families distinguish all automorphisms, without
normality of the infinite separable APF extension. -/
theorem FieldOfNorms.map_eq_self_iff [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    (∀ x : FieldOfNorms K L, FieldOfNorms.map σ x = x) ↔ σ = 1 := by
  constructor
  · intro hσ
    apply AlgEquiv.ext
    intro a
    let D₀ : FiniteIntermediateField K L := ⟨IntermediateField.adjoin K {a}, inferInstance⟩
    let D := FiniteIntermediateField.sup D₀ (apfMaximalTame K L)
    let E : FiniteIntermediateField K L := ⟨IntermediateField.normalClosure K D.val L,
        inferInstance⟩
    have hDE : D ≤ E := IntermediateField.le_normalClosure D.val
    have hE : FiniteIntermediateField.map σ.toAlgHom E = E :=
      Subtype.ext (IntermediateField.map_normalClosure_eq D.val σ)
    let s := IntermediateField.normalClosureRestrict D.val σ
    have hs : ∀ b : E.val, (s b : L) = σ (b : L) :=
      fun b => IntermediateField.coe_normalClosureRestrict D.val σ b
    have hsid := FiniteIntermediateField.aut_eq_of_fieldOfNormsMap_fixed K L σ hσ E hE
      ((FiniteIntermediateField.le_sup_right D₀ _).trans hDE) s hs
    have ha₀ : a ∈ D₀.val := IntermediateField.subset_adjoin K {a} (by simp)
    have ha : a ∈ E.val := hDE (FiniteIntermediateField.le_sup_left D₀ _ ha₀)
    have h := congrArg (fun t : E.val ≃ₐ[K] E.val => (t ⟨a, ha⟩ : L)) hsid
    rw [hs] at h
    exact h
  · rintro rfl
    intro x
    exact FieldOfNorms.map_refl x

/-- The automorphism homomorphism on the norm field is injective. -/
theorem FieldOfNorms.aut_injective [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Function.Injective (FieldOfNorms.aut K L) := by
  intro σ τ hστ
  have hker : FieldOfNorms.aut K L (τ⁻¹ * σ) = 1 := by
    rw [_root_.map_mul, map_inv, hστ, inv_mul_cancel]
  have hs : τ⁻¹ * σ = 1 := (FieldOfNorms.map_eq_self_iff K L _).mp (by
    intro x
    change FieldOfNorms.aut K L (τ⁻¹ * σ) x = x
    rw [hker]
    rfl)
  exact (inv_mul_eq_one.mp hs).symm

end Valued

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

section Families

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    [Module.Finite M N] [IsGalois M N]

/-- Stable good finite fields are a cofinal subsystem of the target. -/
theorem galoisStableGoodFiniteLayers_cofinal [Algebra.IsAlgebraic K N]
    (E : FiniteIntermediateField K N) :
    ∃ D : FiniteIntermediateField K N,
      (IsGoodFiniteLayer K M D ∧ ∀ σ : N ≃ₐ[M] N,
        D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧ E ≤ D := by
  obtain ⟨D, hED, hg, hs, _⟩ := exists_galois_stable_goodFiniteLayer_ge K M N E
  exact ⟨D, ⟨hg, hs⟩, hED⟩

/-- A fixed family has an unique pullback coordinate at
every stable finite field. -/
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

/-- The unique preimage lies in the pullback field. -/
def galoisNormCoordinate (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FiniteIntermediateField.pullback K M D :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose

/-- Inclusion of the preimage recovers exactly the coordinate. -/
theorem galoisNormCoordinate_spec (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FiniteIntermediateField.pullbackTo K M D (galoisNormCoordinate K M N β hβ D hD) =
      FieldOfNorms.coord K N D β :=
  (existsUnique_galoisNormCoordinate K M N β hβ D hD).choose_spec.1

/-- Good-pair norm base change proves compatibility of the
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

/-- A chosen stable good target field dominates each finite
field through its pullback. -/
def galoisGoodUpper (C : FiniteIntermediateField K M) : FiniteIntermediateField K N :=
  (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteIntermediateField.map (IsScalarTower.toAlgHom K M N) C)).choose

theorem galoisGoodUpper_spec (C : FiniteIntermediateField K M) :
    IsGoodFiniteLayer K M (galoisGoodUpper K M N C) ∧
      (∀ σ : N ≃ₐ[M] N, (galoisGoodUpper K M N C).val.map
        (σ.restrictScalars K).toAlgHom = (galoisGoodUpper K M N C).val) ∧
      C ≤ FiniteIntermediateField.pullbackLayer K M (galoisGoodUpper K M N C) := by
  have h := (exists_galois_stable_goodFiniteLayer_ge K M N
    (FiniteIntermediateField.map (IsScalarTower.toAlgHom K M N) C)).choose_spec
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  intro m hm
  exact h.1 ⟨m, hm, rfl⟩

/-- The norm of the descended coordinate defines a coordinate at
every finite field, before any compatibility is assumed. -/
def galoisCoordinate (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) : C.val :=
  FiniteIntermediateField.norm C (FiniteIntermediateField.pullbackLayer K M (galoisGoodUpper
      K M N C))
    (galoisGoodUpper_spec K M N C).2.2
    (galoisNormCoordinate K M N β hβ (galoisGoodUpper K M N C)
      (galoisGoodUpper_spec K M N C).2.1)

/-- Common stable good upper fields and norm transitivity
prove independence of the chosen upper field. -/
theorem galoisCoordinate_eq_norm (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) (D : FiniteIntermediateField K N) (hgD : IsGoodFiniteLayer K
        M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (hCD : C ≤ FiniteIntermediateField.pullbackLayer K M D) :
    galoisCoordinate K M N β hβ C =
      FiniteIntermediateField.norm C (FiniteIntermediateField.pullbackLayer K M D) hCD
        (galoisNormCoordinate K M N β hβ D hsD) := by
  let U := galoisGoodUpper K M N C
  have hU := galoisGoodUpper_spec K M N C
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

/-- Compatibility at every inclusion is proved from the
coordinate independence and finite norm transitivity. -/
theorem galoisCoordinate_norm (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C C' : FiniteIntermediateField K M) (hCC' : C ≤ C') :
    FiniteIntermediateField.norm C C' hCC' (galoisCoordinate K M N β hβ C') =
      galoisCoordinate K M N β hβ C := by
  let D := galoisGoodUpper K M N C'
  have hD := galoisGoodUpper_spec K M N C'
  have hCD : C ≤ FiniteIntermediateField.pullbackLayer K M D := hCC'.trans hD.2.2
  exact (FiniteIntermediateField.norm_norm C C' (FiniteIntermediateField.pullbackLayer K M D)
    hCC' hD.2.2 (galoisNormCoordinate K M N β hβ D hD.2.1)).trans
      (galoisCoordinate_eq_norm K M N β hβ C D hD.1 hD.2.1 hCD).symm

/-- Reconstruction produces an element of the norm
limit, using compatibility just proved for all finite fields. -/
def galoisNormDescent (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β) : FieldOfNorms K M :=
  (existsUnique_fieldOfNorms_of_compatible K M (galoisCoordinate K M N β hβ)
    (galoisCoordinate_norm K M N β hβ)).choose

theorem FieldOfNorms.coord_galoisNormDescent (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (C : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M C (galoisNormDescent K M N β hβ) =
      galoisCoordinate K M N β hβ C :=
  (existsUnique_fieldOfNorms_of_compatible K M (galoisCoordinate K M N β hβ)
    (galoisCoordinate_norm K M N β hβ)).choose_spec.1 C

/-- At every stable good field, descent retains its unique
pullback coordinate exactly. -/
theorem FieldOfNorms.coord_galoisNormDescent_pullback (β : FieldOfNorms K N)
    (hβ : ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β)
    (D : FiniteIntermediateField K N) (hgD : IsGoodFiniteLayer K M D)
    (hsD : ∀ σ : N ≃ₐ[M] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) (galoisNormDescent K M N β
        hβ) =
      galoisNormCoordinate K M N β hβ D hsD := by
  exact (FieldOfNorms.coord_galoisNormDescent K M N β hβ _).trans
    ((galoisCoordinate_eq_norm K M N β hβ _ D hgD hsD le_rfl).trans
      (FiniteIntermediateField.norm_self _ _))

variable [Algebra.IsAlgebraic K M]

/-- Every element in the image is fixed by the
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

/-- The reconstructed family maps back to the given fixed
family, by the good-coordinate formula and cofinality. -/
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

/-- The fixed families are precisely the image of the
finite-inclusion map; all descent and compatibility obligations are proved. -/
theorem mem_range_finiteFieldOfNormsMap_iff_fixed (β : FieldOfNorms K N) :
    β ∈ Set.range (FieldOfNorms.finiteMap K M N) ↔
      ∀ σ : N ≃ₐ[M] N, FieldOfNorms.map (σ.restrictScalars K) β = β := by
  constructor
  · rintro ⟨α, rfl⟩ σ
    exact FieldOfNorms.map_finiteFieldOfNormsMap_relative K M N σ α
  · intro hβ
    exact ⟨galoisNormDescent K M N β hβ, FieldOfNorms.finiteMap_galoisNormDescent K M N β hβ⟩

end Families

section ValuedFields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K N]

/-- The relative action is the norm-field action after
the restriction of scalars. -/
def FieldOfNorms.finiteGaloisAction [IsAPF K N] [Fact (¬ Module.Finite K N)] :
    (N ≃ₐ[M] N) →* (FieldOfNorms K N ≃+* FieldOfNorms K N) := by
  exact (FieldOfNorms.aut K N).comp (AlgEquiv.restrictScalarsHom K)

@[simp]
theorem FieldOfNorms.finiteGaloisAction_apply [IsAPF K N]
    [Fact (¬ Module.Finite K N)] (σ : N ≃ₐ[M] N) (β : FieldOfNorms K N) :
    FieldOfNorms.finiteGaloisAction K M N σ β =
      FieldOfNorms.map (σ.restrictScalars K) β := rfl

/-- Faithfulness is produced by the proved action and the
injective restriction of scalars; it is not an additional hypothesis. -/
theorem FieldOfNorms.finiteGaloisAction_injective [IsAPF K N]
    [Fact (¬ Module.Finite K N)] :
    Function.Injective (FieldOfNorms.finiteGaloisAction K M N) := by
  exact (FieldOfNorms.aut_injective K N).comp
    (AlgEquiv.restrictScalars_injective K)

/-- The canonical action on the target field. -/
@[instance_reducible]
def FieldOfNorms.finiteGaloisMulSemiringAction [IsAPF K N]
    [Fact (¬ Module.Finite K N)] :
    MulSemiringAction (N ≃ₐ[M] N) (FieldOfNorms K N) := by
  exact MulSemiringAction.compHom (FieldOfNorms K N)
    (FieldOfNorms.finiteGaloisAction K M N)

variable [Algebra.IsSeparable K M] [Module.Finite M N] [IsGalois M N]

/-- The fixed field of the relative action is the
image of the checked field homomorphism. -/
theorem fixedPoints_finiteFieldOfNormsGaloisAction [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := FieldOfNorms.finiteGaloisMulSemiringAction K M N
    (FixedPoints.subfield (N ≃ₐ[M] N) (FieldOfNorms K N) : Set (FieldOfNorms K N)) =
      Set.range (FieldOfNorms.finiteRingHom K M N) := by
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  exact Set.ext (fun β => (mem_range_finiteFieldOfNormsMap_iff_fixed K M N β).symm)

/-- The official finite Galois-group structure is proved from
faithfulness, the scalar action and the proved fixed-family descent. -/
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

/-- Finite Artin theory proves finiteness over the embedded source,
without assuming finiteness of the norm-field extension. -/
theorem finiteDimensional_finiteFieldOfNorms_of_isGalois [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    FiniteDimensional (FieldOfNorms K M) (FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact IsGaloisGroup.finiteDimensional (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)

/-- The target norm field is Galois over the embedded source. -/
theorem isGalois_finiteFieldOfNorms [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    IsGalois (FieldOfNorms K M) (FieldOfNorms K N) := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact IsGaloisGroup.isGalois (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)

/-- The finite Galois norm-field extension retains the full degree. -/
theorem finrank_finiteFieldOfNorms_of_isGalois [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI := (FieldOfNorms.finiteRingHom K M N).toAlgebra
    Module.finrank (FieldOfNorms K M) (FieldOfNorms K N) = Module.finrank M N := by
  let := (FieldOfNorms.finiteRingHom K M N).toAlgebra
  let := FieldOfNorms.finiteGaloisMulSemiringAction K M N
  let := FieldOfNorms.finite_isGaloisGroup K M N
  exact (IsGaloisGroup.card_eq_finrank (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)).symm.trans
    (IsGalois.card_aut_eq_finrank M N)

/-- The relative action identifies the two Galois groups. -/
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
