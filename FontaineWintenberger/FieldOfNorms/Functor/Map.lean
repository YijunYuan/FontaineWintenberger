/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Basic.Ring
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.Ramification.Upper.Transport
public import FontaineWintenberger.Ramification.Embedding.Basic
public import FontaineWintenberger.Mathlib.Analysis.UniformContinuity
public import FontaineWintenberger.FieldOfNorms.Layers.NormPairs
public import FontaineWintenberger.FieldOfNorms.Basic.Defs
public import FontaineWintenberger.FieldOfNorms.Layers.GoodTowers
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Functoriality of the field of norms

## Isomorphisms of the norm fields

Field isomorphisms reindex the finite norm families.
Their norm-sum limits and stable valuations are preserved.

## Finite inclusions on the multiplicative fields of norms

Canonical pullbacks and good-field norm base change construct the
covariant map on the same norm families. No APF or valued-field structure is
needed for this multiplicative construction.

## Functor laws for finite maps on the norm families

Identity and composition are tested on cofinal good
finite fields. All comparisons retain the inclusions.

## Equivariance of the finite norm-family maps

Commuting isomorphisms transport the pullback fields and canonical
multiplication maps. Standard semilinear tensor equivalences preserve
goodness, providing the coordinate comparisons in the covariant functor laws.

## Naturality of the finite norm-family maps

The finite-embedding maps agree with the isomorphism maps.
Commuting isomorphisms and inclusions give their functor laws on
the norm families.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

section Transport

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
/-- The transported coordinates satisfy the finite norm equations. -/
theorem FieldOfNorms.mapFun_compatible (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E F : FiniteIntermediateField K M) (hEF : E ≤ F) :
    FiniteIntermediateField.norm E F hEF
        ((FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F) x)) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  rw [FiniteIntermediateField.equivMap_norm, AlgEquiv.apply_symm_apply,
    FieldOfNorms.coord_norm, AlgEquiv.apply_symm_apply]

/-- The reindexing of norm families along a `K`-isomorphism `e : L ≃ₐ[K] M`, as a bare function.
It is multiplicative without any APF hypothesis; `FieldOfNorms.mapEquiv` packages it as a ring
isomorphism once the additive structure is available. -/
def FieldOfNorms.mapFun (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) : FieldOfNorms K M :=
  (existsUnique_fieldOfNorms_of_compatible K M
    (fun E => (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
      (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x))
    (FieldOfNorms.mapFun_compatible e x)).choose

theorem FieldOfNorms.coord_mapFun (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M E (FieldOfNorms.mapFun e x) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) :=
  (existsUnique_fieldOfNorms_of_compatible K M _
    (FieldOfNorms.mapFun_compatible e x)).choose_spec.1 E

theorem FieldOfNorms.coe_coord_mapFun (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    (FieldOfNorms.coord K M E (FieldOfNorms.mapFun e x) : M) =
      e (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x : L) := by
  apply e.symm.injective
  rw [AlgEquiv.symm_apply_apply, FieldOfNorms.coord_mapFun]
  exact congrArg (fun z : (FiniteIntermediateField.map e.symm.toAlgHom E).val => (z : L))
    ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).apply_symm_apply _)

theorem FieldOfNorms.mapFun_zero (e : L ≃ₐ[K] M) :
    FieldOfNorms.mapFun e (0 : FieldOfNorms K L) = 0 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_mapFun]
  simp

theorem FieldOfNorms.mapFun_one (e : L ≃ₐ[K] M) :
    FieldOfNorms.mapFun e (1 : FieldOfNorms K L) = 1 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_mapFun]
  simp

theorem FieldOfNorms.mapFun_mul (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.mapFun e (x * y) = FieldOfNorms.mapFun e x * FieldOfNorms.mapFun e y := by
  apply FieldOfNorms.ext K M
  intro E
  simp only [_root_.map_mul, FieldOfNorms.coord_mapFun]

theorem FieldOfNorms.mapFun_symm_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.mapFun e.symm (FieldOfNorms.mapFun e x) = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [FieldOfNorms.coe_coord_mapFun, FieldOfNorms.coe_coord_mapFun]
  simp only [AlgEquiv.symm_apply_apply]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    ((FiniteIntermediateField.mapOrderIso e).left_inv E)

theorem FieldOfNorms.mapFun_apply_symm (e : L ≃ₐ[K] M) (x : FieldOfNorms K M) :
    FieldOfNorms.mapFun e (FieldOfNorms.mapFun e.symm x) = x :=
  FieldOfNorms.mapFun_symm_apply e.symm x

theorem FieldOfNorms.mapFun_refl (x : FieldOfNorms K L) :
    FieldOfNorms.mapFun (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [FieldOfNorms.coe_coord_mapFun]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    (FiniteIntermediateField.map_id E)

theorem FieldOfNorms.mapFun_trans (e : L ≃ₐ[K] M) (f : M ≃ₐ[K] N) (x : FieldOfNorms K L) :
    FieldOfNorms.mapFun f (FieldOfNorms.mapFun e x) = FieldOfNorms.mapFun (e.trans f) x := by
  apply FieldOfNorms.ext K N
  intro E
  apply Subtype.val_injective
  rw [FieldOfNorms.coe_coord_mapFun, FieldOfNorms.coe_coord_mapFun,
    FieldOfNorms.coe_coord_mapFun]
  exact congrArg (fun D : FiniteIntermediateField K L => f (e (FieldOfNorms.coord K L D x : L)))
    (FiniteIntermediateField.map_map f.symm.toAlgHom e.symm.toAlgHom E)

theorem FieldOfNorms.normSumNet_mapFun (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) (F : Set.Ici E) :
    normSumNet K M E (FieldOfNorms.mapFun e x) (FieldOfNorms.mapFun e y) F =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (normSumNet K L (FiniteIntermediateField.map e.symm.toAlgHom E) x y
          (FiniteIntermediateField.mapIci e.symm.toAlgHom E F)) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  have hEF : E ≤ F.val := F.property
  have hm := FiniteIntermediateField.map_mono e.symm.toAlgHom hEF
  change (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      (FiniteIntermediateField.norm E F.val hEF
        (FieldOfNorms.coord K M F.val (FieldOfNorms.mapFun e x) +
          FieldOfNorms.coord K M F.val (FieldOfNorms.mapFun e y))) =
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FiniteIntermediateField.norm _ _ hm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) x +
            FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) y)))
  rw [FiniteIntermediateField.equivMap_norm, map_add, FieldOfNorms.coord_mapFun,
    FieldOfNorms.coord_mapFun, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

end Transport

section Equiv

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- Finite field isomorphisms preserve the normalized
DVR valuations, on integral and nonintegral elements alike. -/
theorem spectral_normalizedValuation_algEquiv [FiniteDimensional K L]
    [FiniteDimensional K M] (e : L ≃ₐ[K] M) (x : L) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M (e x) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L x := by
  have hi (a : spectralIntegerRing K L) :
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M
          (e (a : L)) =
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L
          (a : L) := by
    rw [← coe_spectralIntegerRingEquiv K e a]
    change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M
        (algebraMap (spectralIntegerRing K M) M (spectralIntegerRingEquiv K e a)) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L
        (algebraMap (spectralIntegerRing K L) L a)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal,
      IsDiscreteValuationRing.intValuation_maximalIdeal, spectralIntegerRingEquiv_addVal]
  rcases (spectralIntegerRing K L).mem_or_inv_mem x with hx | hx
  · exact hi ⟨x, hx⟩
  · have h := hi ⟨x⁻¹, hx⟩
    simpa only [map_inv₀, inv_inj] using h

theorem FieldOfNorms.valuation_mapFun [IsAPF K L] [IsAPF K M]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K M (FieldOfNorms.mapFun e x) = FieldOfNorms.valuation K L x := by
  obtain ⟨D, hD⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  obtain ⟨E, hE⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K M
  let F := FiniteIntermediateField.sup E (FiniteIntermediateField.map e.toAlgHom D)
  let P := FiniteIntermediateField.map e.symm.toAlgHom F
  have hDP : D ≤ P := by
    calc
      D = FiniteIntermediateField.map e.symm.toAlgHom (FiniteIntermediateField.map e.toAlgHom D) :=
        ((FiniteIntermediateField.mapOrderIso e).left_inv D).symm
      _ ≤ P := FiniteIntermediateField.map_mono e.symm.toAlgHom
          (FiniteIntermediateField.le_sup_right E _)
  rw [hE F (FiniteIntermediateField.le_sup_left E _) (FieldOfNorms.mapFun e x), hD P hDP x]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation
      F.val (FieldOfNorms.coord K M F (FieldOfNorms.mapFun e x)) =
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K P.val)).valuation P.val
      (FieldOfNorms.coord K L P x)
  rw [FieldOfNorms.coord_mapFun]
  exact spectral_normalizedValuation_algEquiv K
    (FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm (FieldOfNorms.coord K L P x)

theorem FieldOfNorms.mapFun_add
    [IsAPF K L] [IsAPF K M] (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.mapFun e (FieldOfNorms.add K L x y) =
      FieldOfNorms.add K M (FieldOfNorms.mapFun e x) (FieldOfNorms.mapFun e y) := by
  apply FieldOfNorms.eq_add_of_tendsto K M (FieldOfNorms.mapFun e x) (FieldOfNorms.mapFun e y)
  intro E
  let D := FiniteIntermediateField.map e.symm.toAlgHom E
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K E.val
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm :=
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  rw [FieldOfNorms.coord_mapFun]
  have ht := hc.continuousAt.tendsto.comp
    ((FieldOfNorms.tendsto_normSumNet_add K L x y D).comp
      (FiniteIntermediateField.tendsto_mapIci e.symm E))
  convert ht using 1
  funext F
  exact FieldOfNorms.normSumNet_mapFun e x y E F

variable [IsAPF K L] [IsAPF K M] [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
variable {K}

/-- The ring isomorphism `X_K(L) ≃+* X_K(M)` induced by a `K`-isomorphism `e : L ≃ₐ[K] M`: the
coordinate at a finite intermediate field `E` of `M` is `e` applied to the coordinate at
`e⁻¹(E)`. -/
def FieldOfNorms.mapEquiv (e : L ≃ₐ[K] M) : FieldOfNorms K L ≃+* FieldOfNorms K M where
  toFun := FieldOfNorms.mapFun e
  invFun := FieldOfNorms.mapFun e.symm
  left_inv := FieldOfNorms.mapFun_symm_apply e
  right_inv := FieldOfNorms.mapFun_apply_symm e
  map_mul' := FieldOfNorms.mapFun_mul e
  map_add' := FieldOfNorms.mapFun_add K e

/-- The coordinate of a transported family, in the finite intermediate field. -/
theorem FieldOfNorms.coord_mapEquiv (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M E (FieldOfNorms.mapEquiv e x) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) :=
  FieldOfNorms.coord_mapFun e x E

/-- The coordinate of a transported family, in the ambient field. -/
@[simp]
theorem FieldOfNorms.coe_coord_mapEquiv (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    (FieldOfNorms.coord K M E (FieldOfNorms.mapEquiv e x) : M) =
      e (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x : L) :=
  FieldOfNorms.coe_coord_mapFun e x E

@[simp]
theorem FieldOfNorms.mapEquiv_symm (e : L ≃ₐ[K] M) :
    (FieldOfNorms.mapEquiv e).symm = FieldOfNorms.mapEquiv e.symm := rfl

@[simp]
theorem FieldOfNorms.mapEquiv_symm_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.mapEquiv e.symm (FieldOfNorms.mapEquiv e x) = x :=
  FieldOfNorms.mapFun_symm_apply e x

@[simp]
theorem FieldOfNorms.mapEquiv_apply_symm (e : L ≃ₐ[K] M) (x : FieldOfNorms K M) :
    FieldOfNorms.mapEquiv e (FieldOfNorms.mapEquiv e.symm x) = x :=
  FieldOfNorms.mapFun_apply_symm e x

@[simp]
theorem FieldOfNorms.mapEquiv_refl (x : FieldOfNorms K L) :
    FieldOfNorms.mapEquiv (AlgEquiv.refl : L ≃ₐ[K] L) x = x :=
  FieldOfNorms.mapFun_refl x

theorem FieldOfNorms.mapEquiv_trans {N : Type*} [Field N] [Algebra K N] [Algebra.IsSeparable K N]
    [IsAPF K N] [Fact (¬ Module.Finite K N)] (e : L ≃ₐ[K] M) (f : M ≃ₐ[K] N)
    (x : FieldOfNorms K L) :
    FieldOfNorms.mapEquiv f (FieldOfNorms.mapEquiv e x) = FieldOfNorms.mapEquiv (e.trans f) x :=
  FieldOfNorms.mapFun_trans e f x

/-- The transport preserves the normalized valuation. -/
theorem FieldOfNorms.valuation_mapEquiv (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K M (FieldOfNorms.mapEquiv e x) = FieldOfNorms.valuation K L x :=
  FieldOfNorms.valuation_mapFun K e x

/-- The transport is uniformly continuous for the valuation uniformities. -/
theorem FieldOfNorms.uniformContinuous_mapEquiv (e : L ≃ₐ[K] M) :
    UniformContinuous (FieldOfNorms.mapEquiv e) := by
  apply valuedRingEquiv_uniformContinuous
  intro x
  exact FieldOfNorms.valuation_mapEquiv e x

variable (K L) in
/-- The action of `Aut(L/K)` on `X_K(L)` by ring automorphisms. -/
def FieldOfNorms.aut : (L ≃ₐ[K] L) →* (FieldOfNorms K L ≃+* FieldOfNorms K L) where
  toFun := FieldOfNorms.mapEquiv
  map_one' := RingEquiv.ext fun x => FieldOfNorms.mapEquiv_refl x
  map_mul' e f := RingEquiv.ext fun x => (FieldOfNorms.mapEquiv_trans f e x).symm

@[simp]
theorem FieldOfNorms.aut_apply (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.aut K L e x = FieldOfNorms.mapEquiv e x := rfl

variable (K) in
theorem FieldOfNorms.aut_valuation (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.aut K L e x) = FieldOfNorms.valuation K L x :=
  FieldOfNorms.valuation_mapEquiv e x

end Equiv

section Layers

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The coordinate of a norm family of `M` at the pullback `D ∩ M` of a finite intermediate field
`D` of `N`, pushed into `D`. -/
def FieldOfNorms.pullbackCoord (D : FiniteIntermediateField K N) : FieldOfNorms K M →*₀ D.val :=
  (FiniteIntermediateField.pullbackTo K M D).toRingHom.toMonoidWithZeroHom.comp
    (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D))

/-- On every good pair these coordinates satisfy the
finite target norm equation. -/
theorem FieldOfNorms.pullbackCoord_norm (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (x : FieldOfNorms K M) :
    FiniteIntermediateField.norm D D' h (FieldOfNorms.pullbackCoord K M N D' x) =
      FieldOfNorms.pullbackCoord K M N D x := by
  exact (goodFinitePair_norm K M D D' h hD hD'
    (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D') x)).trans
      (congrArg (FiniteIntermediateField.pullbackTo K M D)
        (FieldOfNorms.coord_norm K M (FiniteIntermediateField.pullbackLayer K M D)
          (FiniteIntermediateField.pullbackLayer K M D') (FiniteIntermediateField.pullback_mono K M
              h) x))

/-- For the identity inclusion the canonical pullback is the same
finite index. -/
theorem FiniteIntermediateField.pullbackLayer_self (D : FiniteIntermediateField K M) :
    FiniteIntermediateField.pullbackLayer K M D = D := by
  apply Subtype.ext
  ext x
  rfl

/-- The pullback coordinate for the identity is the
coordinate itself. -/
@[simp]
theorem FieldOfNorms.pullbackCoord_self (D : FiniteIntermediateField K M) (x : FieldOfNorms K M)
    :
    FieldOfNorms.pullbackCoord K M M D x = FieldOfNorms.coord K M D x := by
  apply Subtype.ext
  change (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M) =
    (FieldOfNorms.coord K M D x : M)
  rw [FiniteIntermediateField.pullbackLayer_self]

variable [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The good finite fields form a cofinal index set. -/
theorem goodFiniteLayers_cofinal (E : FiniteIntermediateField K N) :
    ∃ D, IsGoodFiniteLayer K M D ∧ E ≤ D := by
  obtain ⟨D, hED, hD⟩ := exists_goodFiniteLayer_ge K M E
  exact ⟨D, hD, hED⟩

/-- The multiplicative inclusion `X_K(M) →*₀ X_K(N)` of a finite separable extension `N/M`,
defined without APF hypotheses; `FieldOfNorms.inclusion` packages it as a ring homomorphism. -/
def FieldOfNorms.inclusion₀ : FieldOfNorms K M →*₀ FieldOfNorms K N where
  toFun x := FieldOfNorms.ofCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun D _ => FieldOfNorms.pullbackCoord K M N D x)
    (fun D D' hD hD' h => FieldOfNorms.pullbackCoord_norm K M N D D' h hD hD' x)
  map_zero' := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [FieldOfNorms.coord_ofCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (_root_.map_zero (FieldOfNorms.pullbackCoord K M N D)).trans (_root_.map_zero _).symm
  map_one' := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [FieldOfNorms.coord_ofCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (_root_.map_one (FieldOfNorms.pullbackCoord K M N D)).trans (_root_.map_one _).symm
  map_mul' x y := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    simp only [_root_.map_mul,
      FieldOfNorms.coord_ofCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]

theorem FieldOfNorms.coord_inclusionFun (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N D (FieldOfNorms.inclusion₀ K M N x) =
      FieldOfNorms.pullbackCoord K M N D x :=
  FieldOfNorms.coord_ofCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun E _ => FieldOfNorms.pullbackCoord K M N E x)
    (fun E F hE hF h => FieldOfNorms.pullbackCoord_norm K M N E F h hE hF x) D hD

/-- Good target fields can simultaneously dominate a target field and the
image of any prescribed finite field. -/
theorem exists_goodFiniteLayer_ge_pullback (D : FiniteIntermediateField K N)
    (C : FiniteIntermediateField K M) :
    ∃ F : FiniteIntermediateField K N, D ≤ F ∧ IsGoodFiniteLayer K M F ∧
      C ≤ FiniteIntermediateField.pullbackLayer K M F := by
  let i := IsScalarTower.toAlgHom K M N
  obtain ⟨F, hF, hg⟩ := exists_goodFiniteLayer_ge K M (FiniteIntermediateField.sup D
      (FiniteIntermediateField.map i C))
  refine ⟨F, (FiniteIntermediateField.le_sup_left D _).trans hF, hg, ?_⟩
  intro x hx
  exact hF (FiniteIntermediateField.le_sup_right D _ ⟨x, hx, rfl⟩)

theorem FieldOfNorms.normSumNet_inclusionFun (D F : FiniteIntermediateField K N) (hDF : D ≤ F)
    (hD : IsGoodFiniteLayer K M D) (hF : IsGoodFiniteLayer K M F)
    (x y : FieldOfNorms K M) :
    normSumNet K N D (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y)
        ⟨F, hDF⟩ =
      FiniteIntermediateField.pullbackTo K M D
        (normSumNet K M (FiniteIntermediateField.pullbackLayer K M D) x y
          ⟨FiniteIntermediateField.pullbackLayer K M F, FiniteIntermediateField.pullback_mono K M
              hDF⟩) := by
  change FiniteIntermediateField.norm D F hDF
      (FieldOfNorms.coord K N F (FieldOfNorms.inclusion₀ K M N x) +
        FieldOfNorms.coord K N F (FieldOfNorms.inclusion₀ K M N y)) = _
  rw [FieldOfNorms.coord_inclusionFun K M N F hF,
    FieldOfNorms.coord_inclusionFun K M N F hF]
  exact (congrArg (FiniteIntermediateField.norm D F hDF)
    (map_add (FiniteIntermediateField.pullbackTo K M F)
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) x)
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) y)).symm).trans
    (goodFinitePair_norm K M D F hDF hD hF
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) x +
        FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M F) y))

end Layers

section Inclusion

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

/-- The finite-field embedding scales normalized valuations by its
positive local ramification index, for every field element. -/
theorem spectral_normalizedValuation_algHom {E F : Type*} [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E] [FiniteDimensional K F]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K F] (i : E →ₐ[K] F) (x : E) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F)).valuation F (i x) =
      ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E)).valuation E x) ^
        embeddingRamificationIdx K i := by
  let R := spectralIntegerRing K E
  let S := spectralIntegerRing K F
  let : Algebra E F := i.toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun r => (i.commutes r).symm)
  let : Algebra R S := (spectralIntegerInclusion K i).toRingHom.toAlgebra
  let : Algebra R F := (i.toRingHom.comp (algebraMap R E)).toAlgebra
  let : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro a b hab
    apply Subtype.ext
    exact i.injective (congrArg (fun z : S => (z : F)) hab))
  let : IsLocalHom (algebraMap R S) :=
    ⟨(spectralIntegerInclusion_isLocalHom K i).map_nonunit⟩
  exact normalizedValuation_algebraMap R S E F x

variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Module.Finite M N] [Algebra.IsSeparable M N]
    [IsAPF K M] [IsAPF K N]

theorem FieldOfNorms.coord_inclusionFun_add
    (D : FiniteIntermediateField K N) (hD : IsGoodFiniteLayer K M D) (x y : FieldOfNorms K M) :
    FieldOfNorms.coord K N D (FieldOfNorms.inclusion₀ K M N (FieldOfNorms.add K M x y)) =
      FieldOfNorms.coord K N D (FieldOfNorms.add K N
        (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y)) := by
  let C := FiniteIntermediateField.pullbackLayer K M D
  let S := {F : FiniteIntermediateField K N // D ≤ F ∧ IsGoodFiniteLayer K M F}
  let : Nonempty S := ⟨⟨D, le_rfl, hD⟩⟩
  let : IsDirectedOrder S := ⟨fun F G => by
    obtain ⟨H, hFH, hGH, hH⟩ := exists_goodFiniteLayer_ge_pair K M F.val G.val
    exact ⟨⟨H, F.property.1.trans hFH, hH⟩, hFH, hGH⟩⟩
  let u (F : S) : Set.Ici D := ⟨F.val, F.property.1⟩
  let v (F : S) : Set.Ici C :=
    ⟨FiniteIntermediateField.pullbackLayer K M F.val, FiniteIntermediateField.pullback_mono K M
        F.property.1⟩
  have hu : Tendsto u atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hF, hAF⟩ := goodFiniteLayers_cofinal K M N A.val
    exact ⟨⟨F, A.property.trans hAF, hF⟩, fun G hFG => hAF.trans hFG⟩
  have hv : Tendsto v atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro A
    obtain ⟨F, hDF, hF, hAF⟩ := exists_goodFiniteLayer_ge_pullback K M N D A.val
    exact ⟨⟨F, hDF, hF⟩, fun G hFG => hAF.trans (FiniteIntermediateField.pullback_mono K M hFG)⟩
  let := spectralNorm.nontriviallyNormedField K (FiniteIntermediateField.pullback K M D)
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K (FiniteIntermediateField.pullback K M D)
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteIntermediateField.pullbackTo K M D) :=
    (FiniteIntermediateField.pullbackTo K M D).toLinearMap.continuous_of_finiteDimensional
  have hsource := hc.continuousAt.tendsto.comp
    ((FieldOfNorms.tendsto_normSumNet_add K M x y C).comp hv)
  have htarget := (FieldOfNorms.tendsto_normSumNet_add K N
    (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y) D).comp hu
  have heq : (fun F : S => normSumNet K N D
      (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y) (u F)) =
      fun F : S => FiniteIntermediateField.pullbackTo K M D (normSumNet K M C x y (v F)) := by
    funext F
    exact FieldOfNorms.normSumNet_inclusionFun K M N D F.val F.property.1 hD F.property.2 x y
  change Tendsto (fun F : S => normSumNet K N D
    (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y) (u F)) _ _ at htarget
  rw [heq] at htarget
  exact (FieldOfNorms.coord_inclusionFun K M N D hD _).trans
    (tendsto_nhds_unique hsource htarget)

theorem FieldOfNorms.inclusion₀_add
    (x y : FieldOfNorms K M) :
    FieldOfNorms.inclusion₀ K M N (FieldOfNorms.add K M x y) =
      FieldOfNorms.add K N (FieldOfNorms.inclusion₀ K M N x) (FieldOfNorms.inclusion₀ K M N y) := by
  apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  exact FieldOfNorms.coord_inclusionFun_add K M N D hD x y

variable [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]

/-- The field homomorphism `X_K(M) →+* X_K(N)` induced by a finite separable extension `N/M`
inside the APF tower over `K`: at a good finite intermediate field `D` of `N` the coordinate is
the coordinate at `D ∩ M`. -/
def FieldOfNorms.inclusion : FieldOfNorms K M →+* FieldOfNorms K N :=
  { FieldOfNorms.inclusion₀ K M N with map_add' := FieldOfNorms.inclusion₀_add K M N }

/-- The coordinate of the image family at a good finite intermediate field. -/
@[simp]
theorem FieldOfNorms.coord_inclusion (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N D (FieldOfNorms.inclusion K M N x) =
      FieldOfNorms.pullbackCoord K M N D x :=
  FieldOfNorms.coord_inclusionFun K M N D hD x

/-- Any target coordinate is computed from any good upper finite
field by its norm. -/
theorem FieldOfNorms.coord_inclusion_of_le (E D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (hED : E ≤ D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N E (FieldOfNorms.inclusion K M N x) =
      FiniteIntermediateField.norm E D hED (FieldOfNorms.pullbackCoord K M N D x) := by
  rw [← FieldOfNorms.coord_norm K N E D hED, FieldOfNorms.coord_inclusion K M N D hD]

/-- The prescribed good coordinates determine the covariant map. -/
theorem FieldOfNorms.inclusion_unique (f : FieldOfNorms K M → FieldOfNorms K N)
    (hf : ∀ (D : FiniteIntermediateField K N), IsGoodFiniteLayer K M D →
      ∀ x, FieldOfNorms.coord K N D (f x) = FieldOfNorms.pullbackCoord K M N D x) :
    f = FieldOfNorms.inclusion K M N := by
  funext x
  apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  rw [hf D hD x, FieldOfNorms.coord_inclusion K M N D hD]

/-- The ambient-element formula at every good field. -/
theorem FieldOfNorms.coe_coord_inclusion (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    (FieldOfNorms.coord K N D (FieldOfNorms.inclusion K M N x) : N) =
      algebraMap M N (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M)
          := by
  rw [FieldOfNorms.coord_inclusion K M N D hD]
  rfl

/-- A good field on both stable tails computes one fixed positive
finite valuation exponent for every norm family, including zero. -/
theorem FieldOfNorms.exists_goodFiniteLayer_valuation_inclusion
    :
    ∃ D : FiniteIntermediateField K N, IsGoodFiniteLayer K M D ∧
      0 < embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) ∧
      ∀ x : FieldOfNorms K M,
        FieldOfNorms.valuation K N (FieldOfNorms.inclusion K M N x) =
          FieldOfNorms.valuation K M x ^
            embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) := by
  obtain ⟨C₀, hC₀⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K M
  obtain ⟨D₀, hD₀⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K N
  obtain ⟨D, hD₀D, hD, hC₀D⟩ := exists_goodFiniteLayer_ge_pullback K M N D₀ C₀
  let C := FiniteIntermediateField.pullbackLayer K M D
  refine ⟨D, hD, embeddingRamificationIdx_pos K (FiniteIntermediateField.pullbackTo K M D), fun x
      => ?_⟩
  calc
    FieldOfNorms.valuation K N (FieldOfNorms.inclusion K M N x) =
        FieldOfNorms.coordinateValuation K N D (FieldOfNorms.inclusion K M N x) :=
      hD₀ D hD₀D _
    _ = (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
        D.val (FiniteIntermediateField.pullbackTo K M D (FieldOfNorms.coord K M C x)) :=
      congrArg ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation
          D.val)
        (FieldOfNorms.coord_inclusion K M N D hD x)
    _ = FieldOfNorms.coordinateValuation K M C x ^
        embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) :=
      spectral_normalizedValuation_algHom K (FiniteIntermediateField.pullbackTo K M D)
        (FieldOfNorms.coord K M C x)
    _ = FieldOfNorms.valuation K M x ^
        embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D) :=
      congrArg (fun z => z ^ embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D))
        (hC₀ C hC₀D x).symm

/-- Positive integral scaling is produced from a finite
integer-ring inclusion, rather than supplied as an additional hypothesis. -/
theorem FieldOfNorms.exists_valuation_inclusion_eq_pow :
    ∃ e : ℕ, 0 < e ∧ ∀ x : FieldOfNorms K M,
      FieldOfNorms.valuation K N (FieldOfNorms.inclusion K M N x) =
        FieldOfNorms.valuation K M x ^ e := by
  obtain ⟨D, _, he, hv⟩ := FieldOfNorms.exists_goodFiniteLayer_valuation_inclusion K M N
  exact ⟨embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K M D), he, hv⟩

/-- The finite-inclusion map is uniformly continuous for the existing
valuation uniformities, by its proved positive integral scaling. -/
theorem FieldOfNorms.uniformContinuous_inclusion :
    UniformContinuous (FieldOfNorms.inclusion K M N) := by
  obtain ⟨e, he, hv⟩ := FieldOfNorms.exists_valuation_inclusion_eq_pow K M N
  have hbM := Valued.nhds_zero_hasBasis_integer_closedBall (FieldOfNorms K M)
    (FieldOfNorms.uniformizer K M)
    (FieldOfNorms.valuation_uniformizer K M)
  have hbN := Valued.nhds_zero_hasBasis_integer_closedBall (FieldOfNorms K N)
    (FieldOfNorms.uniformizer K N)
    (FieldOfNorms.valuation_uniformizer K N)
  change UniformContinuous (FieldOfNorms.inclusion K M N)
  apply uniformContinuous_of_continuousAt_zero
    (FieldOfNorms.inclusion K M N).toAddMonoidHom
  simp only [ContinuousAt, map_zero, hbM.tendsto_iff hbN, true_and, forall_const]
  intro n
  refine ⟨n, fun x hx => ?_⟩
  change FieldOfNorms.valuation K N (FieldOfNorms.inclusion K M N x) ≤
    WithZero.exp (-((n + 2 : ℕ) : ℤ))
  rw [hv x]
  have hpow : WithZero.exp (-((n + 2 : ℕ) : ℤ)) ^ e ≤
      WithZero.exp (-((n + 2 : ℕ) : ℤ)) := by
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
    have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
    simp only [nsmul_eq_mul]
    nlinarith
  exact (pow_le_pow_left₀ zero_le hx e).trans hpow

/-- Continuity uses the valuation topology on each norm field. -/
theorem FieldOfNorms.continuous_inclusion :
    Continuous (FieldOfNorms.inclusion K M N) := by
  exact (FieldOfNorms.uniformContinuous_inclusion K M N).continuous

end Inclusion

section FunctorLaws

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Algebra.IsSeparable K M] [IsAPF K M]
    [Fact (¬ Module.Finite K M)]

/-- The covariant finite-inclusion map preserves the identity. -/
@[simp]
theorem FieldOfNorms.inclusion_self (x : FieldOfNorms K M) : FieldOfNorms.inclusion K M M x = x :=
    by
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M M)
  intro D hD
  exact (FieldOfNorms.coord_inclusion K M M D hD x).trans
    (FieldOfNorms.pullbackCoord_self K M D x)

variable (N P : Type*) [Field N] [Field P] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P] [IsScalarTower M N P]
    [Algebra.IsSeparable K N] [Algebra.IsSeparable K P] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K N)] [Fact (¬ Module.Finite K P)]
    [Module.Finite M N] [Module.Finite N P] [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]

/-- Composition on the norm families, tested on the proved
cofinal simultaneous good stages of the finite separable tower. -/
theorem FieldOfNorms.inclusion_inclusion (x : FieldOfNorms K M) :
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    FieldOfNorms.inclusion K N P (FieldOfNorms.inclusion K M N x) = FieldOfNorms.inclusion K M P x
        := by
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let Q (D : FiniteIntermediateField K P) := IsGoodFiniteLayer K N D ∧ IsGoodFiniteLayer K M D ∧
    IsGoodFiniteLayer K M (FiniteIntermediateField.pullbackLayer K N D)
  have hQ (E : FiniteIntermediateField K P) : ∃ D, Q D ∧ E ≤ D := by
    obtain ⟨D, hED, hN, hM, hMN⟩ := exists_goodFiniteLayer_tower_ge K M N E
    exact ⟨D, ⟨hN, hM, hMN⟩, hED⟩
  apply FieldOfNorms.ext_cofinal K P Q hQ
  intro D ⟨hN, hM, hMN⟩
  rw [FieldOfNorms.coord_inclusion K N P D hN,
    FieldOfNorms.coord_inclusion K M P D hM]
  change FiniteIntermediateField.pullbackTo K N D
      (FieldOfNorms.coord K N (FiniteIntermediateField.pullbackLayer K N D) (FieldOfNorms.inclusion
          K M N x)) = _
  rw [FieldOfNorms.coord_inclusion K M N (FiniteIntermediateField.pullbackLayer K N D)
      hMN]
  apply Subtype.ext
  change algebraMap N P (algebraMap M N
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M
          (FiniteIntermediateField.pullbackLayer K N D)) x : M)) =
    algebraMap M P (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M)
  rw [← IsScalarTower.algebraMap_apply, FiniteIntermediateField.pullbackLayer_tower K M N D]

end FunctorLaws

section Embeddings

variable (K : Type*) {L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]

/-- The preimage index can equivalently be computed by pulling back
to the image and then through the range isomorphism. -/
theorem FiniteIntermediateField.pullback_fieldRange (τ : L →ₐ[K] M) (D : FiniteIntermediateField K
    M) :
    (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
      (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)).val = D.val.comap τ := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change τ (τ.equivFieldRange.symm a) ∈ D.val
    change (a : M) ∈ D.val at ha
    have he : τ (τ.equivFieldRange.symm a) = (a : M) :=
      congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply a)
    rw [he]
    exact ha
  · intro hx
    refine ⟨τ.equivFieldRange x, hx, ?_⟩
    exact τ.equivFieldRange.symm_apply_apply x

/-- The codomain is finite over the image of an isomorphism. -/
instance moduleFinite_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
    Module.Finite e.toAlgHom.fieldRange M := by
  apply Module.Finite.of_surjective (Algebra.linearMap e.toAlgHom.fieldRange M)
  intro m
  exact ⟨⟨m, e.symm m, e.apply_symm_apply m⟩, rfl⟩

/-- The image extension of an isomorphism is separable of degree one. -/
instance isSeparable_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
    Algebra.IsSeparable e.toAlgHom.fieldRange M := by
  constructor
  intro m
  exact isSeparable_algebraMap (⟨m, e.symm m, e.apply_symm_apply m⟩ : e.toAlgHom.fieldRange)

/-- Pulling back through the image factorization gives exactly the
inverse-isomorphism finite index. -/
theorem FiniteIntermediateField.pullback_algEquiv (e : L ≃ₐ[K] M) (D : FiniteIntermediateField K M)
    :
    FiniteIntermediateField.map e.toAlgHom.equivFieldRange.symm.toAlgHom
        (FiniteIntermediateField.pullbackLayer K e.toAlgHom.fieldRange D) =
      FiniteIntermediateField.map e.symm.toAlgHom D := by
  apply Subtype.ext
  rw [FiniteIntermediateField.pullback_fieldRange]
  ext x
  change e x ∈ D.val ↔ x ∈ D.val.map e.symm.toAlgHom
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change e (e.symm y) ∈ D.val
    change y ∈ D.val at hy
    rw [AlgEquiv.apply_symm_apply]
    exact hy

/-- The image finiteness transports to the embedding
as scalar map; it is proved rather than supplied for the new scalar structure. -/
theorem moduleFinite_fieldRange_scalars (τ : L →ₐ[K] M) [Module.Finite τ.fieldRange M] :
    letI := τ.toRingHom.toAlgebra
    Module.Finite L M := by
  let := τ.toRingHom.toAlgebra
  apply Module.Finite.of_equiv_equiv τ.equivFieldRange.symm.toRingEquiv (RingEquiv.refl M)
  ext r
  change τ (τ.equivFieldRange.symm r) = (r : M)
  exact congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply r)

/-- The image separability transports along the same
coefficient isomorphism and the identity on the ambient field. -/
theorem isSeparable_fieldRange_scalars (τ : L →ₐ[K] M)
    [Algebra.IsSeparable τ.fieldRange M] :
    letI := τ.toRingHom.toAlgebra
    Algebra.IsSeparable L M := by
  let := τ.toRingHom.toAlgebra
  apply Algebra.IsSeparable.of_equiv_equiv τ.equivFieldRange.symm.toRingEquiv (RingEquiv.refl M)
  ext r
  change τ (τ.equivFieldRange.symm r) = (r : M)
  exact congrArg Subtype.val (τ.equivFieldRange.apply_symm_apply r)

/-- Algebraicity of the and finiteness over its image
give algebraicity of the target. -/
theorem isAlgebraic_of_finite_fieldRange [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M) [Module.Finite τ.fieldRange M] : Algebra.IsAlgebraic K M := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact Algebra.IsAlgebraic.trans K τ.fieldRange M

section RangeScalars

variable (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N] [Algebra M N]
    [IsScalarTower K M N]

/-- Finiteness over the coefficient field gives finiteness over
its image, through the source-to-image isomorphism. -/
instance moduleFinite_algebraMap_fieldRange [Module.Finite M N] :
    Module.Finite (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Module.Finite.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

/-- Separability over the coefficient field gives separability over
the same image, with the inclusion square. -/
instance isSeparable_algebraMap_fieldRange [Algebra.IsSeparable M N] :
    Algebra.IsSeparable (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Algebra.IsSeparable.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

end RangeScalars

/-- The composite of the finite embeddings is finite over its
image; the scalar structures are the embedding maps. -/
instance moduleFinite_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Module.Finite τ.fieldRange M] [Module.Finite σ.fieldRange N] :
    Module.Finite (σ.comp τ).fieldRange N := by
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite M N := moduleFinite_fieldRange_scalars K σ
  let : Module.Finite L N := Module.Finite.trans M N
  exact moduleFinite_algebraMap_fieldRange K L N

/-- Separability of the image extensions is preserved by the same
composite embedding, without a new separability assumption. -/
instance isSeparable_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Algebra.IsSeparable τ.fieldRange M] [Algebra.IsSeparable σ.fieldRange N] :
    Algebra.IsSeparable (σ.comp τ).fieldRange N := by
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable M N := isSeparable_fieldRange_scalars K σ
  let : Algebra.IsSeparable L N := Algebra.IsSeparable.trans L M N
  exact isSeparable_algebraMap_fieldRange K L N

variable {K} in
/-- The range of an embedding of an infinite extension is infinite. -/
theorem not_finite_fieldRange (τ : L →ₐ[K] M) [Fact (¬ Module.Finite K L)] :
    ¬ Module.Finite K τ.fieldRange := by
  intro h
  let : Module.Finite K τ.fieldRange := h
  exact (Fact.out : ¬ Module.Finite K L) (Module.Finite.equiv τ.equivFieldRange.symm.toLinearEquiv)

end Embeddings

section Tensor

open scoped TensorProduct

variable (K : Type*) {M N M' N' : Type*}
    [Field K] [Field M] [Field N] [Field M'] [Field N']
    [Algebra K M] [Algebra K N] [Algebra K M'] [Algebra K N']
    [Algebra M N] [Algebra M' N'] [IsScalarTower K M N] [IsScalarTower K M' N']

/-- Pullback membership is preserved by a commuting square of
ambient and coefficient-field isomorphisms. -/
theorem FiniteIntermediateField.pullback_mem_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (x : M) :
    e x ∈ FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) ↔
      x ∈ FiniteIntermediateField.pullback K M D := by
  change algebraMap M' N' (e x) ∈ D.val.map f.toAlgHom ↔ algebraMap M N x ∈ D.val
  rw [← h x]
  exact D.val.map_mem_map f.toAlgHom

/-- The image of the pullback is the target pullback. -/
theorem FiniteIntermediateField.pullback_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    (FiniteIntermediateField.pullback K M D).map e.toAlgHom =
      FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (FiniteIntermediateField.pullback_mem_map_iff K e f h D y).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (FiniteIntermediateField.pullback_mem_map_iff K e f h D (e.symm x)).mp
    simpa only [AlgEquiv.apply_symm_apply] using hx

/-- The restriction of the coefficient-field isomorphism to the
pullbacks. -/
def FiniteIntermediateField.pullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.pullback K M D ≃ₐ[K]
      FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D) :=
  (IntermediateField.equivMap (FiniteIntermediateField.pullback K M D) e.toAlgHom).trans
    (IntermediateField.equivOfEq (FiniteIntermediateField.pullback_map K e f h D))

@[simp]
theorem coe_finiteIntermediateFieldPullbackEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (x : FiniteIntermediateField.pullback K M D) :
    (FiniteIntermediateField.pullbackEquiv K e f h D x : M') = e (x : M) := rfl

/-- The semilinear tensor transport, retained as an additive equivalence
so no scalar-structure choices are required by its consumers. -/
def FiniteIntermediateField.tensorAddEquiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    (M ⊗[FiniteIntermediateField.pullback K M D] D.val) ≃+
      (M' ⊗[FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)]
        (FiniteIntermediateField.map f.toAlgHom D).val) := by
  let ec := FiniteIntermediateField.pullbackEquiv K e f h D
  let : RingHomInvPair ec.toRingHom ec.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv ec.toRingEquiv
  let : RingHomInvPair ec.symm.toRingHom ec.toRingHom := RingHomInvPair.symm _ _
  let em : M ≃ₛₗ[ec.toRingHom] M' :=
    { e.toAddEquiv with
      map_smul' := by
        intro c m
        change e ((c : M) * m) = (ec c : M') * e m
        rw [map_mul]
        rfl }
  have hc (c : FiniteIntermediateField.pullback K M D) :
      FiniteIntermediateField.equivMap f.toAlgHom D
          (algebraMap (FiniteIntermediateField.pullback K M D) D.val c) =
        algebraMap (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom
            D))
          (FiniteIntermediateField.map f.toAlgHom D).val (ec c) := by
    apply Subtype.ext
    change f (algebraMap D.val N (algebraMap (FiniteIntermediateField.pullback K M D) D.val c)) =
      algebraMap (FiniteIntermediateField.map f.toAlgHom D).val N'
        (algebraMap (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom
            D))
          (FiniteIntermediateField.map f.toAlgHom D).val (ec c))
    rw [← IsScalarTower.algebraMap_apply (FiniteIntermediateField.pullback K M D) D.val N,
      IsScalarTower.algebraMap_apply (FiniteIntermediateField.pullback K M D) M N,
      ← IsScalarTower.algebraMap_apply
        (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D))
        (FiniteIntermediateField.map f.toAlgHom D).val N',
      IsScalarTower.algebraMap_apply
        (FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)) M' N']
    exact h (c : M)
  let ed : D.val ≃ₛₗ[ec.toRingHom] (FiniteIntermediateField.map f.toAlgHom D).val :=
    { (FiniteIntermediateField.equivMap f.toAlgHom D).toAddEquiv with
      map_smul' := by
        intro c d
        change FiniteIntermediateField.equivMap f.toAlgHom D (c • d) =
          ec c • FiniteIntermediateField.equivMap f.toAlgHom D d
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc] }
  exact (TensorProduct.congr em ed).toAddEquiv

/-- The tensor transport uses the two field isomorphisms
on every pure tensor. -/
@[simp]
theorem FiniteIntermediateField.tensorAddEquiv_tmul (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (m : M) (d : D.val) :
    FiniteIntermediateField.tensorAddEquiv K e f h D (m ⊗ₜ[FiniteIntermediateField.pullback K M D]
        d) =
      e m ⊗ₜ[FiniteIntermediateField.pullback K M' (FiniteIntermediateField.map f.toAlgHom D)]
        FiniteIntermediateField.equivMap f.toAlgHom D d := rfl

/-- The multiplication maps commute with the tensor transport. -/
theorem FiniteIntermediateField.tensorMap_equiv (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) (z : M ⊗[FiniteIntermediateField.pullback K M D] D.val) :
    FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (FiniteIntermediateField.tensorAddEquiv K e f h D z) = f (FiniteIntermediateField.tensorMap
            K M D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m d =>
    rw [FiniteIntermediateField.tensorAddEquiv_tmul]
    change e m • f (d : N) = f (m • (d : N))
    simp only [Algebra.smul_def, map_mul, h]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Bijectivity of the multiplication map is invariant under
the commuting field isomorphisms. -/
theorem isGoodFiniteLayer_map_iff (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    IsGoodFiniteLayer K M' (FiniteIntermediateField.map f.toAlgHom D) ↔ IsGoodFiniteLayer K M D :=
        by
  let U := FiniteIntermediateField.tensorAddEquiv K e f h D
  constructor
  · intro hD
    constructor
    · intro a b hab
      apply U.injective
      apply hD.1
      rw [FiniteIntermediateField.tensorMap_equiv, FiniteIntermediateField.tensorMap_equiv, hab]
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f y)
      refine ⟨U.symm a, ?_⟩
      apply f.injective
      rw [← FiniteIntermediateField.tensorMap_equiv K e f h D]
      change FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (U (U.symm a)) = f y
      rw [U.apply_symm_apply, ha]
  · intro hD
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := U.surjective a
      obtain ⟨b, rfl⟩ := U.surjective b
      apply congrArg U
      apply hD.1
      apply f.injective
      dsimp only [U] at hab
      simpa only [FiniteIntermediateField.tensorMap_equiv] using hab
    · intro y
      obtain ⟨a, ha⟩ := hD.2 (f.symm y)
      refine ⟨U a, ?_⟩
      change FiniteIntermediateField.tensorMap K M' (FiniteIntermediateField.map f.toAlgHom D)
        (FiniteIntermediateField.tensorAddEquiv K e f h D a) = y
      rw [FiniteIntermediateField.tensorMap_equiv, ha, f.apply_symm_apply]

/-- The pullback indices commute with the given isomorphisms. -/
theorem FiniteIntermediateField.pullbackLayer_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.map e.toAlgHom (FiniteIntermediateField.pullbackLayer K M D) =
      FiniteIntermediateField.pullbackLayer K M' (FiniteIntermediateField.map f.toAlgHom D) := by
  apply Subtype.ext
  exact FiniteIntermediateField.pullback_map K e f h D

end Tensor

section Map

variable {K : Type*} [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable {L M N : Type*} [Field L] [Field M] [Field N] [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M] [Algebra.IsSeparable K N]
    [IsAPF K L] [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]

instance IsAPF.fieldRange (τ : L →ₐ[K] M) : IsAPF K τ.fieldRange :=
  (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›

instance (τ : L →ₐ[K] M) : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩

/-- The field homomorphism `X_K(L) →+* X_K(M)` induced by a `K`-embedding `τ : L →ₐ[K] M` with
finite separable range: the inclusion of `X_K(τ(L))` into `X_K(M)` after the isomorphism
`X_K(L) ≃ X_K(τ(L))`. -/
def FieldOfNorms.map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M] :
    FieldOfNorms K L →+* FieldOfNorms K M :=
  (FieldOfNorms.inclusion K τ.fieldRange M).comp (FieldOfNorms.mapEquiv τ.equivFieldRange).toRingHom

/-- The range factorization gives precisely the prescribed good
coordinates on the norm families. -/
theorem FieldOfNorms.coord_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteIntermediateField K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : FieldOfNorms K
        L) :
    FieldOfNorms.coord K M D (FieldOfNorms.map τ x) =
      FieldOfNorms.pullbackCoord K τ.fieldRange M D
        (FieldOfNorms.mapEquiv τ.equivFieldRange x) := by
  exact FieldOfNorms.coord_inclusion K τ.fieldRange M D hD _

/-- In the ambient field, the prescribed coordinate is the
embedding applied to the preimage coordinate. -/
theorem FieldOfNorms.coe_coord_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteIntermediateField K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : FieldOfNorms K
        L) :
    (FieldOfNorms.coord K M D (FieldOfNorms.map τ x) : M) =
      τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
        (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L) := by
  rw [FieldOfNorms.coord_map τ D hD]
  change algebraMap τ.fieldRange M
      (FieldOfNorms.coord K τ.fieldRange (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)
        (FieldOfNorms.mapEquiv τ.equivFieldRange x) : τ.fieldRange) = _
  rw [FieldOfNorms.coe_coord_mapEquiv]
  rfl

/-- One good target field gives the positive finite ramification
exponent for every norm family, including zero. -/
theorem FieldOfNorms.exists_goodFiniteLayer_valuation_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    :
    ∃ D : FiniteIntermediateField K M, IsGoodFiniteLayer K τ.fieldRange D ∧
      0 < embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D) ∧
      ∀ x : FieldOfNorms K L,
        FieldOfNorms.valuation K M (FieldOfNorms.map τ x) =
          FieldOfNorms.valuation K L x ^
            embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D) := by
  obtain ⟨D, hD, he, hv⟩ :=
    FieldOfNorms.exists_goodFiniteLayer_valuation_inclusion K τ.fieldRange M
  refine ⟨D, hD, he, fun x => ?_⟩
  change FieldOfNorms.valuation K M
    (FieldOfNorms.inclusion K τ.fieldRange M (FieldOfNorms.mapEquiv τ.equivFieldRange x)) = _
  rw [hv, FieldOfNorms.valuation_mapEquiv τ.equivFieldRange]

/-- The map has a proved fixed positive integral valuation exponent. -/
theorem FieldOfNorms.exists_valuation_map_eq_pow (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    :
    ∃ e : ℕ, 0 < e ∧ ∀ x : FieldOfNorms K L,
      FieldOfNorms.valuation K M (FieldOfNorms.map τ x) =
        FieldOfNorms.valuation K L x ^ e := by
  obtain ⟨D, _, he, hv⟩ :=
    FieldOfNorms.exists_goodFiniteLayer_valuation_map τ
  exact ⟨embeddingRamificationIdx K (FiniteIntermediateField.pullbackTo K τ.fieldRange D), he, hv⟩

/-- The arbitrary embedding is uniformly continuous for the same
already constructed valuation uniformities on the norm fields. -/
theorem FieldOfNorms.uniformContinuous_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M] :
    UniformContinuous (FieldOfNorms.map τ) := by
  exact (FieldOfNorms.uniformContinuous_inclusion K τ.fieldRange M).comp
    (FieldOfNorms.uniformContinuous_mapEquiv τ.equivFieldRange)

/-- Continuity is for the valuation topologies on the fields. -/
theorem FieldOfNorms.continuous_map (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M] :
    Continuous (FieldOfNorms.map τ) := by
  exact (FieldOfNorms.uniformContinuous_map τ).continuous

/-- The same finite-embedding map on an isomorphism is the already
constructed isomorphism map, with no assumed comparison. -/
theorem FieldOfNorms.map_algEquiv
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.map e.toAlgHom x = FieldOfNorms.mapEquiv e x := by
  let : Algebra.IsAlgebraic K e.toAlgHom.fieldRange := e.toAlgHom.equivFieldRange.isAlgebraic
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K e.toAlgHom.fieldRange)
    (goodFiniteLayers_cofinal K e.toAlgHom.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [FieldOfNorms.coe_coord_map e.toAlgHom D hD,
    FieldOfNorms.coe_coord_mapEquiv, FiniteIntermediateField.pullback_algEquiv K e D]
  rfl

section Naturality

variable {M' N' : Type*} [Field M'] [Field N'] [Algebra K M'] [Algebra K N']
    [Algebra.IsSeparable K M'] [Algebra.IsSeparable K N'] [IsAPF K M'] [IsAPF K N']
    [Fact (¬ Module.Finite K M')] [Fact (¬ Module.Finite K N')]
    [Algebra M N] [Algebra M' N'] [IsScalarTower K M N] [IsScalarTower K M' N']
    [Module.Finite M N] [Module.Finite M' N'] [Algebra.IsSeparable M N] [Algebra.IsSeparable M' N']

/-- Commuting isomorphisms and finite inclusions give the same
map of norm families, by the proved cofinal good-coordinate formulas. -/
theorem FieldOfNorms.mapEquiv_inclusion (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (x : FieldOfNorms K M) :
    FieldOfNorms.mapEquiv f (FieldOfNorms.inclusion K M N x) =
      FieldOfNorms.inclusion K M' N' (FieldOfNorms.mapEquiv e x) := by
  have hs (m' : M') :
      f.symm (algebraMap M' N' m') = algebraMap M N (e.symm m') := by
    apply f.injective
    rw [f.apply_symm_apply, h, e.apply_symm_apply]
  apply FieldOfNorms.ext_cofinal K N' (IsGoodFiniteLayer K M')
    (goodFiniteLayers_cofinal K M' N')
  intro D hD
  have hDb : IsGoodFiniteLayer K M (FiniteIntermediateField.map f.symm.toAlgHom D) :=
    (isGoodFiniteLayer_map_iff K e.symm f.symm hs D).mpr hD
  apply Subtype.val_injective
  rw [FieldOfNorms.coe_coord_mapEquiv,
    FieldOfNorms.coe_coord_inclusion K M N _ hDb,
    FieldOfNorms.coe_coord_inclusion K M' N' D hD,
    FieldOfNorms.coe_coord_mapEquiv,
    h, FiniteIntermediateField.pullbackLayer_map K e.symm f.symm hs D]

end Naturality

section InclusionComparison

variable (M N) [Algebra M N] [IsScalarTower K M N] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The finite-embedding map of an algebra inclusion agrees
with the inclusion map; range naturality proves the bridge. -/
theorem FieldOfNorms.map_toAlgHom (x : FieldOfNorms K M) :
    FieldOfNorms.map (IsScalarTower.toAlgHom K M N) x =
      FieldOfNorms.inclusion K M N x := by
  let τ := IsScalarTower.toAlgHom K M N
  change FieldOfNorms.inclusion K τ.fieldRange N (FieldOfNorms.mapEquiv τ.equivFieldRange x) = _
  simpa only [FieldOfNorms.mapEquiv_refl] using
    (FieldOfNorms.mapEquiv_inclusion τ.equivFieldRange (AlgEquiv.refl : N ≃ₐ[K] N)
      (fun _ => rfl) x).symm

end InclusionComparison

/-- Naturality for the same arbitrary embedding maps, obtained
through their proved inclusion comparisons. -/
theorem FieldOfNorms.mapEquiv_map
    {L' M' : Type*} [Field L'] [Field M'] [Algebra K L'] [Algebra K M']
    [Algebra.IsSeparable K L'] [Algebra.IsSeparable K M'] [IsAPF K L'] [IsAPF K M']
    [Fact (¬ Module.Finite K L')] [Fact (¬ Module.Finite K M')]
    (τ : L →ₐ[K] M) (τ' : L' →ₐ[K] M')
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite τ'.fieldRange M'] [Algebra.IsSeparable τ'.fieldRange M']
    (e : L ≃ₐ[K] L') (f : M ≃ₐ[K] M')
    (h : ∀ l : L, f (τ l) = τ' (e l)) (x : FieldOfNorms K L) :
    FieldOfNorms.mapEquiv f (FieldOfNorms.map τ x) =
      FieldOfNorms.map τ' (FieldOfNorms.mapEquiv e x) := by
  let := τ.toRingHom.toAlgebra
  let := τ'.toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower K L' M' := IsScalarTower.of_algebraMap_eq (fun k => (τ'.commutes k).symm)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite L' M' := moduleFinite_fieldRange_scalars K τ'
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable L' M' := isSeparable_fieldRange_scalars K τ'
  calc
    FieldOfNorms.mapEquiv f (FieldOfNorms.map τ x) =
        FieldOfNorms.mapEquiv f (FieldOfNorms.inclusion K L M x) :=
      congrArg (FieldOfNorms.mapEquiv f) (FieldOfNorms.map_toAlgHom L M x)
    _ = FieldOfNorms.inclusion K L' M' (FieldOfNorms.mapEquiv e x) :=
      FieldOfNorms.mapEquiv_inclusion e f h x
    _ = FieldOfNorms.map τ' (FieldOfNorms.mapEquiv e x) :=
      (FieldOfNorms.map_toAlgHom L' M' (FieldOfNorms.mapEquiv e x)).symm

/-- Equal embeddings induce equal norm-family maps,
including their proved finite-image instance transports. -/
theorem FieldOfNorms.map_congr
    {τ σ : L →ₐ[K] M}
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange M] [Algebra.IsSeparable σ.fieldRange M]
    (h : τ = σ) (x : FieldOfNorms K L) :
    FieldOfNorms.map τ x = FieldOfNorms.map σ x := by
  subst σ
  rfl

/-- The arbitrary-embedding map preserves the identity. -/
theorem FieldOfNorms.map_id
    (x : FieldOfNorms K L) :
    letI : Module.Finite (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    letI : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    FieldOfNorms.map (AlgHom.id K L) x = x := by
  let : Module.Finite (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
  exact (FieldOfNorms.map_congr h x).symm.trans
    ((FieldOfNorms.map_algEquiv (AlgEquiv.refl : L ≃ₐ[K] L) x).trans
      (FieldOfNorms.mapEquiv_refl x))

/-- Arbitrary finite separable embeddings compose on the norm
families. The scalar bridges reduce to the simultaneous-good-stage
composition theorem for the inclusions. -/
theorem FieldOfNorms.map_map
    (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange N] [Algebra.IsSeparable σ.fieldRange N]
    (x : FieldOfNorms K L) :
    FieldOfNorms.map σ (FieldOfNorms.map τ x) =
      FieldOfNorms.map (σ.comp τ) x := by
  let := τ.toRingHom.toAlgebra
  let := σ.toRingHom.toAlgebra
  let := (σ.comp τ).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => (σ.commutes k).symm)
  let : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq (fun k => ((σ.comp τ).commutes k).symm)
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite M N := moduleFinite_fieldRange_scalars K σ
  let : Module.Finite L N := Module.Finite.trans M N
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable M N := isSeparable_fieldRange_scalars K σ
  let : Algebra.IsSeparable L N := Algebra.IsSeparable.trans L M N
  calc
    FieldOfNorms.map σ (FieldOfNorms.map τ x) =
        FieldOfNorms.inclusion K M N (FieldOfNorms.map τ x) :=
      FieldOfNorms.map_toAlgHom M N _
    _ = FieldOfNorms.inclusion K M N (FieldOfNorms.inclusion K L M x) :=
      congrArg (FieldOfNorms.inclusion K M N) (FieldOfNorms.map_toAlgHom L M x)
    _ = FieldOfNorms.inclusion K L N x := FieldOfNorms.inclusion_inclusion K L M N x
    _ = FieldOfNorms.map (σ.comp τ) x :=
      (FieldOfNorms.map_toAlgHom L N x).symm

/-- The prescribed good coordinates uniquely determine the same
arbitrary finite-embedding map, even among all functions of norm families. -/
theorem FieldOfNorms.map_unique
    (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (g : FieldOfNorms K L → FieldOfNorms K M)
    (hg : ∀ (D : FiniteIntermediateField K M), IsGoodFiniteLayer K τ.fieldRange D →
      ∀ x, (FieldOfNorms.coord K M D (g x) : M) =
        τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
          (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L)) :
    g = FieldOfNorms.map τ := by
  funext x
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K τ.fieldRange)
    (goodFiniteLayers_cofinal K τ.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [hg D hD x, FieldOfNorms.coe_coord_map τ D hD]

end Map

end

end FontaineWintenberger
