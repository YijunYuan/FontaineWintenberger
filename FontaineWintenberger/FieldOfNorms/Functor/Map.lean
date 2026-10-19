/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Basic.Ring
public import FontaineWintenberger.Ramification.Upper.Transport
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

section Multiplicative

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
/-- The transported coordinates satisfy the finite norm equations. -/
theorem FieldOfNorms.map_compatible (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E F : FiniteIntermediateField K M) (hEF : E ≤ F) :
    FiniteIntermediateField.norm E F hEF
        ((FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F) x)) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  rw [FiniteIntermediateField.equivMap_norm, AlgEquiv.apply_symm_apply,
    FieldOfNorms.coord_norm, AlgEquiv.apply_symm_apply]

/-- The field isomorphism reindexes the norm families,
with their zero and multiplication. -/
def FieldOfNorms.map (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) : FieldOfNorms K M :=
  (existsUnique_fieldOfNorms_of_compatible K M
    (fun E => (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
      (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x))
    (FieldOfNorms.map_compatible e x)).choose

/-- Evaluation of the transported family in its finite field. -/
theorem FieldOfNorms.coord_fieldOfNormsMap (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M E (FieldOfNorms.map e x) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) :=
  (existsUnique_fieldOfNorms_of_compatible K M _ (FieldOfNorms.map_compatible e x)).choose_spec.1 E

/-- The ambient-field formula, including finite intermediate fields moved by e. -/
@[simp]
theorem coe_fieldOfNormsEval_fieldOfNormsMap (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    (FieldOfNorms.coord K M E (FieldOfNorms.map e x) : M) =
      e (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x : L) := by
  apply e.symm.injective
  rw [AlgEquiv.symm_apply_apply, FieldOfNorms.coord_fieldOfNormsMap]
  exact congrArg (fun z : (FiniteIntermediateField.map e.symm.toAlgHom E).val => (z : L))
    ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).apply_symm_apply _)

@[simp]
theorem FieldOfNorms.map_zero (e : L ≃ₐ[K] M) : FieldOfNorms.map e (0 : FieldOfNorms K L) = 0 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  simp

@[simp]
theorem FieldOfNorms.map_one (e : L ≃ₐ[K] M) : FieldOfNorms.map e (1 : FieldOfNorms K L) = 1 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  simp

theorem FieldOfNorms.map_mul (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.map e (x * y) = FieldOfNorms.map e x * FieldOfNorms.map e y := by
  apply FieldOfNorms.ext K M
  intro E
  simp only [_root_.map_mul, FieldOfNorms.coord_fieldOfNormsMap]

@[simp]
theorem FieldOfNorms.map_symm_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.map e.symm (FieldOfNorms.map e x) = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap, coe_fieldOfNormsEval_fieldOfNormsMap]
  simp only [AlgEquiv.symm_apply_apply]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    ((FiniteIntermediateField.mapOrderIso e).left_inv E)

@[simp]
theorem FieldOfNorms.map_apply_symm (e : L ≃ₐ[K] M) (x : FieldOfNorms K M) :
    FieldOfNorms.map e (FieldOfNorms.map e.symm x) = x :=
  FieldOfNorms.map_symm_apply e.symm x

@[simp]
theorem FieldOfNorms.map_refl (x : FieldOfNorms K L) :
    FieldOfNorms.map (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    (FiniteIntermediateField.map_id E)

/-- The coordinate transports respect composition. -/
theorem FieldOfNorms.map_trans (e : L ≃ₐ[K] M) (f : M ≃ₐ[K] N) (x : FieldOfNorms K L) :
    FieldOfNorms.map f (FieldOfNorms.map e x) = FieldOfNorms.map (e.trans f) x := by
  apply FieldOfNorms.ext K N
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap, coe_fieldOfNormsEval_fieldOfNormsMap,
    coe_fieldOfNormsEval_fieldOfNormsMap]
  exact congrArg (fun D : FiniteIntermediateField K L => f (e (FieldOfNorms.coord K L D x : L)))
    (FiniteIntermediateField.map_map f.symm.toAlgHom e.symm.toAlgHom E)

/-- The transported norm families form a multiplicative equivalence on
the carriers, before any APF or additive assumptions. -/
def FieldOfNorms.mulEquiv (e : L ≃ₐ[K] M) : FieldOfNorms K L ≃* FieldOfNorms K M where
  toFun := FieldOfNorms.map e
  invFun := FieldOfNorms.map e.symm
  left_inv := FieldOfNorms.map_symm_apply e
  right_inv := FieldOfNorms.map_apply_symm e
  map_mul' := FieldOfNorms.map_mul e

@[simp]
theorem FieldOfNorms.mulEquiv_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.mulEquiv e x = FieldOfNorms.map e x := rfl
/-- Norm-sum nets are taken to the target nets by the
finite field restrictions and finite-layer reindexing. -/
theorem normSumNet_fieldOfNormsMap (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) (F : Set.Ici E) :
    normSumNet K M E (FieldOfNorms.map e x) (FieldOfNorms.map e y) F =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (normSumNet K L (FiniteIntermediateField.map e.symm.toAlgHom E) x y
          (FiniteIntermediateField.mapIci e.symm.toAlgHom E F)) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  have hEF : E ≤ F.val := F.property
  have hm := FiniteIntermediateField.map_mono e.symm.toAlgHom hEF
  change (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      (FiniteIntermediateField.norm E F.val hEF
        (FieldOfNorms.coord K M F.val (FieldOfNorms.map e x) +
          FieldOfNorms.coord K M F.val (FieldOfNorms.map e y))) =
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FiniteIntermediateField.norm _ _ hm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) x +
            FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) y)))
  rw [FiniteIntermediateField.equivMap_norm, map_add, FieldOfNorms.coord_fieldOfNormsMap,
    FieldOfNorms.coord_fieldOfNormsMap, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

end Multiplicative
section ValuedFields

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
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

/-- The reindexing preserves the stable normalized
valuation, using finite coordinates on both stable tails. -/
theorem FieldOfNorms.valuation_fieldOfNormsMap [IsAPF K L] [IsAPF K M]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K M (FieldOfNorms.map e x) = FieldOfNorms.valuation K L x := by
  obtain ⟨D, hD⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  obtain ⟨E, hE⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K M
  let F := FiniteIntermediateField.sup E (FiniteIntermediateField.map e.toAlgHom D)
  let P := FiniteIntermediateField.map e.symm.toAlgHom F
  have hDP : D ≤ P := by
    calc
      D = FiniteIntermediateField.map e.symm.toAlgHom (FiniteIntermediateField.map e.toAlgHom D) :=
        ((FiniteIntermediateField.mapOrderIso e).left_inv D).symm
      _ ≤ P := FiniteIntermediateField.map_mono e.symm.toAlgHom
          (FiniteIntermediateField.le_sup_right E _)
  rw [hE F (FiniteIntermediateField.le_sup_left E _) (FieldOfNorms.map e x), hD P hDP x]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation
      F.val (FieldOfNorms.coord K M F (FieldOfNorms.map e x)) =
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K P.val)).valuation P.val
      (FieldOfNorms.coord K L P x)
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  exact spectral_normalizedValuation_algEquiv K
    (FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm (FieldOfNorms.coord K L P x)

/-- Continuity of the finite restrictions and cofinal reindexing
take the sum-net limits to the target limits. -/
theorem FieldOfNorms.map_add
    [IsAPF K L] [IsAPF K M] (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.map e (FieldOfNorms.add K L x y) =
      FieldOfNorms.add K M (FieldOfNorms.map e x) (FieldOfNorms.map e y) := by
  apply eq_fieldOfNormsAdd_of_tendsto K M (FieldOfNorms.map e x) (FieldOfNorms.map e y)
  intro E
  let D := FiniteIntermediateField.map e.symm.toAlgHom E
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K E.val
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm :=
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  have ht := hc.continuousAt.tendsto.comp
    ((tendsto_normSumNet_fieldOfNormsAdd K L x y D).comp
      (FiniteIntermediateField.tendsto_mapIci e.symm E))
  convert ht using 1
  funext F
  exact normSumNet_fieldOfNormsMap e x y E F

/-- A field isomorphism induces a ring isomorphism between the
same norm fields with their already constructed field structures. -/
def FieldOfNorms.ringEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    FieldOfNorms K L ≃+* FieldOfNorms K M := by
  exact { FieldOfNorms.mulEquiv e with
    map_add' := FieldOfNorms.map_add K e }

@[simp]
theorem FieldOfNorms.ringEquiv_apply [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.ringEquiv K e x = FieldOfNorms.map e x := rfl

variable (L) in
/-- The automorphism group acts by ring automorphisms
of the norm field, with coordinate transport. -/
def FieldOfNorms.aut [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (L ≃ₐ[K] L) →* (FieldOfNorms K L ≃+* FieldOfNorms K L) := by
  exact {
    toFun := FieldOfNorms.ringEquiv K
    map_one' := by
      apply RingEquiv.ext
      intro x
      exact FieldOfNorms.map_refl x
    map_mul' := by
      intro e f
      apply RingEquiv.ext
      intro x
      exact (FieldOfNorms.map_trans f e x).symm }

@[simp]
theorem FieldOfNorms.aut_apply [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.aut K L e x = FieldOfNorms.map e x := rfl

/-- The ring isomorphism is uniformly continuous for the existing
valuation uniformities on the two fields. -/
theorem uniformContinuous_fieldOfNormsRingEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    UniformContinuous (FieldOfNorms.ringEquiv K e) := by
  apply valuedRingEquiv_uniformContinuous
  intro x
  change FieldOfNorms.valuation K M (FieldOfNorms.map e x) = FieldOfNorms.valuation K L x
  exact FieldOfNorms.valuation_fieldOfNormsMap K e x

/-- The norm-field isomorphism and its inverse preserve
the existing uniform spaces; no alternate topology is introduced. -/
def FieldOfNorms.uniformEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    FieldOfNorms K L ≃ᵤ FieldOfNorms K M := by
  exact {
    toEquiv := (FieldOfNorms.ringEquiv K e).toEquiv
    uniformContinuous_toFun :=
      uniformContinuous_fieldOfNormsRingEquiv K e
    uniformContinuous_invFun :=
      uniformContinuous_fieldOfNormsRingEquiv K e.symm }

@[simp]
theorem FieldOfNorms.uniformEquiv_apply [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.uniformEquiv K e x = FieldOfNorms.map e x := rfl

/-- Every automorphism acts by an automorphism preserving
the stable normalized valuation. -/
theorem FieldOfNorms.aut_valuation [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.aut K L e x) =
      FieldOfNorms.valuation K L x :=
  FieldOfNorms.valuation_fieldOfNormsMap K e x

end ValuedFields

end

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The coordinate included in a target finite field. -/
def FieldOfNorms.finiteCoordinate (D : FiniteIntermediateField K N) : FieldOfNorms K M →*₀ D.val :=
  (FiniteIntermediateField.pullbackTo K M D).toRingHom.toMonoidWithZeroHom.comp
    (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D))

/-- On every good pair these coordinates satisfy the
finite target norm equation. -/
theorem FieldOfNorms.finiteCoordinate_norm (D D' : FiniteIntermediateField K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (x : FieldOfNorms K M) :
    FiniteIntermediateField.norm D D' h (FieldOfNorms.finiteCoordinate K M N D' x) =
      FieldOfNorms.finiteCoordinate K M N D x := by
  exact (goodFinitePair_norm K M D D' h hD hD'
    (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D') x)).trans
      (congrArg (FiniteIntermediateField.pullbackTo K M D)
        (FieldOfNorms.coord_norm K M (FiniteIntermediateField.pullbackLayer K M D)
          (FiniteIntermediateField.pullbackLayer K M D') (FiniteIntermediateField.pullback_mono K M
              h) x))

variable [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The good finite fields form a cofinal index set. -/
theorem goodFiniteLayers_cofinal (E : FiniteIntermediateField K N) :
    ∃ D, IsGoodFiniteLayer K M D ∧ E ≤ D := by
  obtain ⟨D, hED, hD⟩ := exists_goodFiniteLayer_ge K M E
  exact ⟨D, hD, hED⟩

/-- The covariant multiplicative map for a finite separable inclusion,
constructed from coordinates on good finite fields. -/
def FieldOfNorms.finiteMap : FieldOfNorms K M →*₀ FieldOfNorms K N where
  toFun x := FieldOfNorms.ofCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun D _ => FieldOfNorms.finiteCoordinate K M N D x)
    (fun D D' hD hD' h => FieldOfNorms.finiteCoordinate_norm K M N D D' h hD hD' x)
  map_zero' := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [FieldOfNorms.coord_fieldOfNormsOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (_root_.map_zero (FieldOfNorms.finiteCoordinate K M N D)).trans (_root_.map_zero _).symm
  map_one' := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [FieldOfNorms.coord_fieldOfNormsOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (_root_.map_one (FieldOfNorms.finiteCoordinate K M N D)).trans (_root_.map_one _).symm
  map_mul' x y := by
    apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    simp only [_root_.map_mul,
      FieldOfNorms.coord_fieldOfNormsOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]

/-- Every good target coordinate retains precisely the included
pullback coordinate of the input family. -/
@[simp]
theorem FieldOfNorms.coord_finiteFieldOfNormsMap (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N D (FieldOfNorms.finiteMap K M N x) =
      FieldOfNorms.finiteCoordinate K M N D x :=
  FieldOfNorms.coord_fieldOfNormsOfCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun E _ => FieldOfNorms.finiteCoordinate K M N E x)
    (fun E F hE hF h => FieldOfNorms.finiteCoordinate_norm K M N E F h hE hF x) D hD

/-- Any target coordinate is computed from any good upper finite
field by its norm. -/
theorem FieldOfNorms.coord_finiteFieldOfNormsMap_any (E D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (hED : E ≤ D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N E (FieldOfNorms.finiteMap K M N x) =
      FiniteIntermediateField.norm E D hED (FieldOfNorms.finiteCoordinate K M N D x) := by
  rw [← FieldOfNorms.coord_norm K N E D hED, FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]

/-- The prescribed good coordinates determine the covariant map. -/
theorem FieldOfNorms.finiteMap_unique (f : FieldOfNorms K M → FieldOfNorms K N)
    (hf : ∀ (D : FiniteIntermediateField K N), IsGoodFiniteLayer K M D →
      ∀ x, FieldOfNorms.coord K N D (f x) = FieldOfNorms.finiteCoordinate K M N D x) :
    f = FieldOfNorms.finiteMap K M N := by
  funext x
  apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  rw [hf D hD x, FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]

/-- The ambient-element formula at every good field. -/
theorem coe_fieldOfNormsEval_finiteFieldOfNormsMap (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    (FieldOfNorms.coord K N D (FieldOfNorms.finiteMap K M N x) : N) =
      algebraMap M N (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M)
          := by
  rw [FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]
  rfl

/-- Zero detection is inherited from a good finite-field coordinate. -/
@[simp]
theorem FieldOfNorms.finiteMap_eq_zero_iff (x : FieldOfNorms K M) :
    FieldOfNorms.finiteMap K M N x = 0 ↔ x = 0 := by
  obtain ⟨D, hD, _⟩ := goodFiniteLayers_cofinal K M N (FiniteIntermediateField.bottom)
  rw [← FieldOfNorms.coord_eq_zero_iff K N D,
    FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]
  constructor
  · intro hx
    apply (FieldOfNorms.coord_eq_zero_iff K M (FiniteIntermediateField.pullbackLayer K M D) x).mp
    exact (FiniteIntermediateField.pullbackTo K M D).injective (hx.trans (_root_.map_zero _).symm)
  · intro hx
    subst x
    exact _root_.map_zero (FieldOfNorms.finiteCoordinate K M N D)

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

section Identity

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

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
theorem FieldOfNorms.finiteCoordinate_self (D : FiniteIntermediateField K M) (x : FieldOfNorms K M)
    :
    FieldOfNorms.finiteCoordinate K M M D x = FieldOfNorms.coord K M D x := by
  apply Subtype.ext
  change (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M) =
    (FieldOfNorms.coord K M D x : M)
  rw [FiniteIntermediateField.pullbackLayer_self]

variable [Algebra.IsAlgebraic K M]

/-- The covariant finite-inclusion map preserves the identity. -/
@[simp]
theorem FieldOfNorms.finiteMap_refl (x : FieldOfNorms K M) : FieldOfNorms.finiteMap K M M x = x :=
    by
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M M)
  intro D hD
  exact (FieldOfNorms.coord_finiteFieldOfNormsMap K M M D hD x).trans
    (FieldOfNorms.finiteCoordinate_self K M D x)

end Identity

section Composition

variable (K M N P : Type*) [Field K] [Field M] [Field N] [Field P]
    [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower M N P] [Algebra.IsAlgebraic K M]
    [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]

/-- Composition on the norm families, tested on the proved
cofinal simultaneous good stages of the finite separable tower. -/
theorem FieldOfNorms.finiteMap_trans (x : FieldOfNorms K M) :
    letI : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    FieldOfNorms.finiteMap K N P (FieldOfNorms.finiteMap K M N x) = FieldOfNorms.finiteMap K M P x
        := by
  let : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let Q (D : FiniteIntermediateField K P) := IsGoodFiniteLayer K N D ∧ IsGoodFiniteLayer K M D ∧
    IsGoodFiniteLayer K M (FiniteIntermediateField.pullbackLayer K N D)
  have hQ (E : FiniteIntermediateField K P) : ∃ D, Q D ∧ E ≤ D := by
    obtain ⟨D, hED, hN, hM, hMN⟩ := exists_goodFiniteLayer_tower_ge K M N E
    exact ⟨D, ⟨hN, hM, hMN⟩, hED⟩
  apply FieldOfNorms.ext_cofinal K P Q hQ
  intro D ⟨hN, hM, hMN⟩
  rw [FieldOfNorms.coord_finiteFieldOfNormsMap K N P D hN,
    FieldOfNorms.coord_finiteFieldOfNormsMap K M P D hM]
  change FiniteIntermediateField.pullbackTo K N D
      (FieldOfNorms.coord K N (FiniteIntermediateField.pullbackLayer K N D) (FieldOfNorms.finiteMap
          K M N x)) = _
  rw [FieldOfNorms.coord_finiteFieldOfNormsMap K M N (FiniteIntermediateField.pullbackLayer K N D)
      hMN]
  apply Subtype.ext
  change algebraMap N P (algebraMap M N
      (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M
          (FiniteIntermediateField.pullbackLayer K N D)) x : M)) =
    algebraMap M P (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M)
  rw [← IsScalarTower.algebraMap_apply, FiniteIntermediateField.pullbackLayer_tower K M N D]

end Composition

section Embeddings

variable (K : Type*) {L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]

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

variable [Algebra.IsAlgebraic K L]

/-- The multiplicative norm-family map for any finite separable
embedding, factored through its image with the proved isomorphism API. -/
def FieldOfNorms.finiteEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M] :
    FieldOfNorms K L →*₀ FieldOfNorms K M := by
  letI : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact (FieldOfNorms.finiteMap K τ.fieldRange M).comp
    (FieldOfNorms.mulEquiv τ.equivFieldRange).toMonoidWithZeroHom

/-- The range factorization gives precisely the prescribed good
coordinates on the norm families. -/
theorem FieldOfNorms.coord_finiteFieldOfNormsEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteIntermediateField K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : FieldOfNorms K
        L) :
    FieldOfNorms.coord K M D (FieldOfNorms.finiteEmbeddingMap K τ x) =
      FieldOfNorms.finiteCoordinate K τ.fieldRange M D (FieldOfNorms.map τ.equivFieldRange x) := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  exact FieldOfNorms.coord_finiteFieldOfNormsMap K τ.fieldRange M D hD _

/-- In the ambient field, the prescribed coordinate is the
embedding applied to the preimage coordinate. -/
theorem coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (D : FiniteIntermediateField K M) (hD : IsGoodFiniteLayer K τ.fieldRange D) (x : FieldOfNorms K
        L) :
    (FieldOfNorms.coord K M D (FieldOfNorms.finiteEmbeddingMap K τ x) : M) =
      τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
        (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L) := by
  rw [FieldOfNorms.coord_finiteFieldOfNormsEmbeddingMap K τ D hD]
  change algebraMap τ.fieldRange M
      (FieldOfNorms.coord K τ.fieldRange (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)
        (FieldOfNorms.map τ.equivFieldRange x) : τ.fieldRange) = _
  rw [coe_fieldOfNormsEval_fieldOfNormsMap]
  rfl

end Embeddings

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

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

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) {L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]

/-- The codomain is finite over the image of an isomorphism. -/
theorem moduleFinite_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
    Module.Finite e.toAlgHom.fieldRange M := by
  apply Module.Finite.of_surjective (Algebra.linearMap e.toAlgHom.fieldRange M)
  intro m
  exact ⟨⟨m, e.symm m, e.apply_symm_apply m⟩, rfl⟩

/-- The image extension of an isomorphism is separable of degree one. -/
theorem isSeparable_algEquiv_fieldRange (e : L ≃ₐ[K] M) :
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

/-- The same finite-embedding map on an isomorphism is the already
constructed isomorphism map, with no assumed comparison. -/
theorem FieldOfNorms.finiteEmbeddingMap_algEquiv [Algebra.IsAlgebraic K L]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    letI := moduleFinite_algEquiv_fieldRange K e
    letI := isSeparable_algEquiv_fieldRange K e
    FieldOfNorms.finiteEmbeddingMap K e.toAlgHom x = FieldOfNorms.map e x := by
  let := moduleFinite_algEquiv_fieldRange K e
  let := isSeparable_algEquiv_fieldRange K e
  let : Algebra.IsAlgebraic K e.toAlgHom.fieldRange := e.toAlgHom.equivFieldRange.isAlgebraic
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K e.toAlgHom.fieldRange)
    (goodFiniteLayers_cofinal K e.toAlgHom.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap K e.toAlgHom D hD,
    coe_fieldOfNormsEval_fieldOfNormsMap, FiniteIntermediateField.pullback_algEquiv K e D]
  rfl

section Naturality

variable {M' N' : Type*} [Field M'] [Field N'] [Algebra K M'] [Algebra K N']
    [Algebra M N] [Algebra M' N'] [IsScalarTower K M N] [IsScalarTower K M' N']

/-- The pullback indices commute with the given isomorphisms. -/
theorem FiniteIntermediateField.pullbackLayer_map (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (D : FiniteIntermediateField K N) :
    FiniteIntermediateField.map e.toAlgHom (FiniteIntermediateField.pullbackLayer K M D) =
      FiniteIntermediateField.pullbackLayer K M' (FiniteIntermediateField.map f.toAlgHom D) := by
  apply Subtype.ext
  exact FiniteIntermediateField.pullback_map K e f h D

variable [Algebra.IsAlgebraic K M] [Algebra.IsAlgebraic K M']
    [Module.Finite M N] [Module.Finite M' N']
    [Algebra.IsSeparable M N] [Algebra.IsSeparable M' N']

/-- Commuting isomorphisms and finite inclusions give the same
map of norm families, by the proved cofinal good-coordinate formulas. -/
theorem FieldOfNorms.finiteMap_naturality (e : M ≃ₐ[K] M') (f : N ≃ₐ[K] N')
    (h : ∀ m : M, f (algebraMap M N m) = algebraMap M' N' (e m))
    (x : FieldOfNorms K M) :
    FieldOfNorms.map f (FieldOfNorms.finiteMap K M N x) =
      FieldOfNorms.finiteMap K M' N' (FieldOfNorms.map e x) := by
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
  rw [coe_fieldOfNormsEval_fieldOfNormsMap,
    coe_fieldOfNormsEval_finiteFieldOfNormsMap K M N _ hDb,
    coe_fieldOfNormsEval_finiteFieldOfNormsMap K M' N' D hD,
    coe_fieldOfNormsEval_fieldOfNormsMap,
    h, FiniteIntermediateField.pullbackLayer_map K e.symm f.symm hs D]

end Naturality

section RangeScalars

variable (M N) [Algebra M N] [IsScalarTower K M N]

/-- Finiteness over the coefficient field gives finiteness over
its image, through the source-to-image isomorphism. -/
theorem moduleFinite_algebraMap_fieldRange [Module.Finite M N] :
    Module.Finite (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Module.Finite.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

/-- Separability over the coefficient field gives separability over
the same image, with the inclusion square. -/
theorem isSeparable_algebraMap_fieldRange [Algebra.IsSeparable M N] :
    Algebra.IsSeparable (IsScalarTower.toAlgHom K M N).fieldRange N := by
  exact Algebra.IsSeparable.of_equiv_equiv
    (IsScalarTower.toAlgHom K M N).equivFieldRange.toRingEquiv (RingEquiv.refl N)
    (by ext m; rfl)

end RangeScalars

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

section InclusionComparison

variable (M N) [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The finite-embedding map of an algebra inclusion agrees
with the inclusion map; range naturality proves the bridge. -/
theorem FieldOfNorms.finiteEmbeddingMap_algebraMap (x : FieldOfNorms K M) :
    letI := moduleFinite_algebraMap_fieldRange K M N
    letI := isSeparable_algebraMap_fieldRange K M N
    FieldOfNorms.finiteEmbeddingMap K (IsScalarTower.toAlgHom K M N) x =
      FieldOfNorms.finiteMap K M N x := by
  let := moduleFinite_algebraMap_fieldRange K M N
  let := isSeparable_algebraMap_fieldRange K M N
  let τ := IsScalarTower.toAlgHom K M N
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  change FieldOfNorms.finiteMap K τ.fieldRange N (FieldOfNorms.map τ.equivFieldRange x) = _
  simpa only [FieldOfNorms.map_refl] using
    (FieldOfNorms.finiteMap_naturality K τ.equivFieldRange (AlgEquiv.refl : N ≃ₐ[K] N)
      (fun _ => rfl) x).symm

end InclusionComparison

/-- Naturality for the same arbitrary embedding maps, obtained
through their proved inclusion comparisons. -/
theorem FieldOfNorms.finiteEmbeddingMap_naturality [Algebra.IsAlgebraic K L]
    {L' M' : Type*} [Field L'] [Field M'] [Algebra K L'] [Algebra K M']
    (τ : L →ₐ[K] M) (τ' : L' →ₐ[K] M')
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite τ'.fieldRange M'] [Algebra.IsSeparable τ'.fieldRange M']
    (e : L ≃ₐ[K] L') (f : M ≃ₐ[K] M')
    (h : ∀ l : L, f (τ l) = τ' (e l)) (x : FieldOfNorms K L) :
    letI : Algebra.IsAlgebraic K L' := e.isAlgebraic
    FieldOfNorms.map f (FieldOfNorms.finiteEmbeddingMap K τ x) =
      FieldOfNorms.finiteEmbeddingMap K τ' (FieldOfNorms.map e x) := by
  let : Algebra.IsAlgebraic K L' := e.isAlgebraic
  let := τ.toRingHom.toAlgebra
  let := τ'.toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun k => (τ.commutes k).symm)
  let : IsScalarTower K L' M' := IsScalarTower.of_algebraMap_eq (fun k => (τ'.commutes k).symm)
  let : Module.Finite L M := moduleFinite_fieldRange_scalars K τ
  let : Module.Finite L' M' := moduleFinite_fieldRange_scalars K τ'
  let : Algebra.IsSeparable L M := isSeparable_fieldRange_scalars K τ
  let : Algebra.IsSeparable L' M' := isSeparable_fieldRange_scalars K τ'
  calc
    FieldOfNorms.map f (FieldOfNorms.finiteEmbeddingMap K τ x) =
        FieldOfNorms.map f (FieldOfNorms.finiteMap K L M x) :=
      congrArg (FieldOfNorms.map f) (FieldOfNorms.finiteEmbeddingMap_algebraMap K L M x)
    _ = FieldOfNorms.finiteMap K L' M' (FieldOfNorms.map e x) :=
      FieldOfNorms.finiteMap_naturality K e f h x
    _ = FieldOfNorms.finiteEmbeddingMap K τ' (FieldOfNorms.map e x) :=
      (FieldOfNorms.finiteEmbeddingMap_algebraMap K L' M' (FieldOfNorms.map e x)).symm

/-- The composite of the finite embeddings is finite over its
image; the scalar structures are the embedding maps. -/
theorem moduleFinite_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
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
theorem isSeparable_comp_fieldRange (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
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

/-- Equal embeddings induce equal norm-family maps,
including their proved finite-image instance transports. -/
theorem FieldOfNorms.finiteEmbeddingMap_congr [Algebra.IsAlgebraic K L]
    {τ σ : L →ₐ[K] M}
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange M] [Algebra.IsSeparable σ.fieldRange M]
    (h : τ = σ) (x : FieldOfNorms K L) :
    FieldOfNorms.finiteEmbeddingMap K τ x = FieldOfNorms.finiteEmbeddingMap K σ x := by
  subst σ
  rfl

/-- The arbitrary-embedding map preserves the identity. -/
theorem FieldOfNorms.finiteEmbeddingMap_refl [Algebra.IsAlgebraic K L]
    (x : FieldOfNorms K L) :
    letI : Module.Finite (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    letI : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
      have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
      exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
    FieldOfNorms.finiteEmbeddingMap K (AlgHom.id K L) x = x := by
  let : Module.Finite (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let : Algebra.IsSeparable (AlgHom.id K L).fieldRange L := by
    have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
    exact h ▸ isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let := moduleFinite_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  let := isSeparable_algEquiv_fieldRange K (AlgEquiv.refl : L ≃ₐ[K] L)
  have h : (AlgEquiv.refl : L ≃ₐ[K] L).toAlgHom = AlgHom.id K L := AlgEquiv.refl_toAlgHom
  exact (FieldOfNorms.finiteEmbeddingMap_congr K h x).symm.trans
    ((FieldOfNorms.finiteEmbeddingMap_algEquiv K (AlgEquiv.refl : L ≃ₐ[K] L) x).trans
      (FieldOfNorms.map_refl x))

/-- Arbitrary finite separable embeddings compose on the norm
families. The scalar bridges reduce to the simultaneous-good-stage
composition theorem for the inclusions. -/
theorem FieldOfNorms.finiteEmbeddingMap_trans [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M) (σ : M →ₐ[K] N)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [Module.Finite σ.fieldRange N] [Algebra.IsSeparable σ.fieldRange N]
    (x : FieldOfNorms K L) :
    letI := isAlgebraic_of_finite_fieldRange K τ
    letI := moduleFinite_comp_fieldRange K τ σ
    letI := isSeparable_comp_fieldRange K τ σ
    FieldOfNorms.finiteEmbeddingMap K σ (FieldOfNorms.finiteEmbeddingMap K τ x) =
      FieldOfNorms.finiteEmbeddingMap K (σ.comp τ) x := by
  let := isAlgebraic_of_finite_fieldRange K τ
  let := moduleFinite_comp_fieldRange K τ σ
  let := isSeparable_comp_fieldRange K τ σ
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
    FieldOfNorms.finiteEmbeddingMap K σ (FieldOfNorms.finiteEmbeddingMap K τ x) =
        FieldOfNorms.finiteMap K M N (FieldOfNorms.finiteEmbeddingMap K τ x) :=
      FieldOfNorms.finiteEmbeddingMap_algebraMap K M N _
    _ = FieldOfNorms.finiteMap K M N (FieldOfNorms.finiteMap K L M x) :=
      congrArg (FieldOfNorms.finiteMap K M N) (FieldOfNorms.finiteEmbeddingMap_algebraMap K L M x)
    _ = FieldOfNorms.finiteMap K L N x := FieldOfNorms.finiteMap_trans K L M N x
    _ = FieldOfNorms.finiteEmbeddingMap K (σ.comp τ) x :=
      (FieldOfNorms.finiteEmbeddingMap_algebraMap K L N x).symm

/-- The prescribed good coordinates uniquely determine the same
arbitrary finite-embedding map, even among all functions of norm families. -/
theorem FieldOfNorms.finiteEmbeddingMap_unique [Algebra.IsAlgebraic K L]
    (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    (g : FieldOfNorms K L → FieldOfNorms K M)
    (hg : ∀ (D : FiniteIntermediateField K M), IsGoodFiniteLayer K τ.fieldRange D →
      ∀ x, (FieldOfNorms.coord K M D (g x) : M) =
        τ (FieldOfNorms.coord K L (FiniteIntermediateField.map τ.equivFieldRange.symm.toAlgHom
          (FiniteIntermediateField.pullbackLayer K τ.fieldRange D)) x : L)) :
    g = FieldOfNorms.finiteEmbeddingMap K τ := by
  let : Algebra.IsAlgebraic K τ.fieldRange := τ.equivFieldRange.isAlgebraic
  funext x
  apply FieldOfNorms.ext_cofinal K M (IsGoodFiniteLayer K τ.fieldRange)
    (goodFiniteLayers_cofinal K τ.fieldRange M)
  intro D hD
  apply Subtype.val_injective
  rw [hg D hD x, coe_fieldOfNormsEval_finiteFieldOfNormsEmbeddingMap K τ D hD]

end FontaineWintenberger
