/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Algebra.StableFiniteLayers
public import FontaineWintenberger.FieldOfNorms.Isomorphism
public import FontaineWintenberger.FieldOfNorms.Constants
public import FontaineWintenberger.FieldOfNorms.Normalization
public import FontaineWintenberger.Ramification.Embedding

/-!
# Faithfulness of the original norm-field action

Original norm-family coordinates on actual finite stable fields separate
automorphisms through source constants and an actual uniformizer. Normality
of the original ambient extension is not needed.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Coordinates

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- At an original stable finite layer, fixed norm families have fixed original coordinates. -/
theorem normLimitEval_fixed_of_normLimitMap_fixed (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : NormLimit K L, normLimitMap σ x = x)
    (E : FiniteLayer K L) (hE : FiniteLayer.map σ.toAlgHom E = E)
    (x : NormLimit K L) :
    σ (normLimitEval K L E x : L) = (normLimitEval K L E x : L) := by
  have hEinv : FiniteLayer.map σ.symm.toAlgHom E = E := by
    have h := (FiniteLayer.mapOrderIso σ).left_inv E
    change FiniteLayer.map σ.symm.toAlgHom (FiniteLayer.map σ.toAlgHom E) = E at h
    rwa [hE] at h
  have h := coe_normLimitEval_normLimitMap σ x E
  rw [hσ x, hEinv] at h
  exact h.symm

end Coordinates

section Valued

open IsDiscreteValuationRing IsLocalRing

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every original coordinate of the genuine norm-family uniformizer is integral. -/
def normLimitUniformizerCoordinateInteger [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (E : FiniteLayer K L) : spectralIntegerRing K E.val :=
  ⟨normLimitEval K L E (normLimitUniformizer K L),
    normLimitEval_mem_of_valuation_le_one K L _ (by
      rw [normLimitValuation_normLimitUniformizer]
      change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
      exact WithZero.exp_le_exp.mpr (by omega)) E⟩

/-- Above the actual maximal unramified field the same original coordinate is a uniformizer. -/
theorem normLimitUniformizerCoordinateInteger_irreducible [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (E : FiniteLayer K L)
    (hE : apfMaximalUnramified K L ≤ E) :
    Irreducible (normLimitUniformizerCoordinateInteger K L E) := by
  let z := normLimitUniformizerCoordinateInteger K L E
  let R := spectralIntegerRing K E.val
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation E.val (z : E.val) =
      WithZero.exp (-1 : ℤ) :=
    (normLimitValuation_eq_coordinate_of_maximalUnramified_le K L E hE _).symm.trans
      (normLimitValuation_normLimitUniformizer K L)
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

/-- The actual source constants force the restriction to a stable original field
to act trivially on its entire residue field. -/
theorem finiteLayer_residue_eq_of_normLimitMap_fixed [IsAPF K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ x : NormLimit K L, normLimitMap σ x = x)
    (E : FiniteLayer K L) (hE : FiniteLayer.map σ.toAlgHom E = E)
    (hK₁ : apfMaximalTame K L ≤ E) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L)) :
    spectralResidueInclusion K s.toAlgHom =
      spectralResidueInclusion K (AlgHom.id K E.val) := by
  ext a
  obtain ⟨c, hc⟩ := (sourceResidueCoordinateEquiv K L E hK₁).surjective a
  rw [← hc, sourceResidueCoordinateEquiv_apply]
  change IsLocalRing.residue _ (spectralIntegerInclusion K s.toAlgHom
      (sourceResidueIntegralCoordinate K L E hK₁ c)) =
    IsLocalRing.residue _ (sourceResidueIntegralCoordinate K L E hK₁ c)
  congr 1
  apply Subtype.ext
  apply Subtype.val_injective
  change (s (sourceResidueIntegralCoordinate K L E hK₁ c : E.val) : L) =
    ((sourceResidueIntegralCoordinate K L E hK₁ c : E.val) : L)
  rw [hs]
  have h := normLimitEval_fixed_of_normLimitMap_fixed σ hσ E hE
    (sourceResidueConstants K L c)
  rw [normLimitEval_sourceResidueConstants K L E hK₁] at h
  exact h

/-- Fixing the original norm families makes the actual restriction on every
stable field above the maximal tame part the identity. -/
theorem finiteLayer_aut_eq_of_normLimitMap_fixed [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : NormLimit K L, normLimitMap σ x = x)
    (E : FiniteLayer K L) (hE : FiniteLayer.map σ.toAlgHom E = E)
    (hK₁ : apfMaximalTame K L ≤ E) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L)) : s = AlgEquiv.refl := by
  have hres := finiteLayer_residue_eq_of_normLimitMap_fixed K L σ hσ E hE hK₁ s hs
  let π := normLimitUniformizerCoordinateInteger K L E
  have hπ : Irreducible π := normLimitUniformizerCoordinateInteger_irreducible K L
    E ((apfMaximalUnramified_le_maximalTame K L).trans hK₁)
  have hfix : spectralIntegerInclusion K s.toAlgHom π =
      spectralIntegerInclusion K (AlgHom.id K E.val) π := by
    apply Subtype.ext
    apply Subtype.val_injective
    change (s (π : E.val) : L) = ((π : E.val) : L)
    rw [hs]
    exact normLimitEval_fixed_of_normLimitMap_fixed σ hσ E hE
      (normLimitUniformizer K L)
  have ht : embeddingIntegralOrder K s.toAlgHom (AlgHom.id K E.val) = ⊤ := by
    rw [embeddingIntegralOrder_eq_uniformizer K _ _ hres hπ, hfix, sub_self, addVal_zero]
  have he := (embeddingIntegralOrder_eq_top_iff K _ _).mp ht
  apply AlgEquiv.ext
  intro a
  exact AlgHom.congr_fun he a

/-- Original norm families distinguish all original automorphisms, without
normality of the infinite separable APF extension. -/
theorem normLimitMap_eq_self_iff [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    (∀ x : NormLimit K L, normLimitMap σ x = x) ↔ σ = 1 := by
  constructor
  · intro hσ
    apply AlgEquiv.ext
    intro a
    let D₀ : FiniteLayer K L := ⟨IntermediateField.adjoin K {a}, inferInstance⟩
    let D := FiniteLayer.sup D₀ (apfMaximalTame K L)
    let E : FiniteLayer K L := ⟨IntermediateField.normalClosure K D.val L, inferInstance⟩
    have hDE : D ≤ E := IntermediateField.le_normalClosure D.val
    have hE : FiniteLayer.map σ.toAlgHom E = E :=
      Subtype.ext (IntermediateField.map_normalClosure_eq D.val σ)
    let s := IntermediateField.normalClosureRestrict D.val σ
    have hs : ∀ b : E.val, (s b : L) = σ (b : L) :=
      fun b => IntermediateField.coe_normalClosureRestrict D.val σ b
    have hsid := finiteLayer_aut_eq_of_normLimitMap_fixed K L σ hσ E hE
      ((FiniteLayer.le_sup_right D₀ _).trans hDE) s hs
    have ha₀ : a ∈ D₀.val := IntermediateField.subset_adjoin K {a} (by simp)
    have ha : a ∈ E.val := hDE (FiniteLayer.le_sup_left D₀ _ ha₀)
    have h := congrArg (fun t : E.val ≃ₐ[K] E.val => (t ⟨a, ha⟩ : L)) hsid
    rw [hs] at h
    exact h
  · rintro rfl
    intro x
    exact normLimitMap_refl x

/-- The actual automorphism homomorphism on the original norm field is injective. -/
theorem normLimitAut_injective [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Function.Injective (normLimitAut K L) := by
  intro σ τ hστ
  have hker : normLimitAut K L (τ⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, hστ, inv_mul_cancel]
  have hs : τ⁻¹ * σ = 1 := (normLimitMap_eq_self_iff K L _).mp (by
    intro x
    change normLimitAut K L (τ⁻¹ * σ) x = x
    rw [hker]
    rfl)
  exact (inv_mul_eq_one.mp hs).symm

end Valued

end FontaineWintenberger
