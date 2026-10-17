/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteNormPairs
public import FontaineWintenberger.FieldOfNorms.Cofinal

/-!
# Finite inclusions on the original multiplicative norm limits

Canonical pullbacks and original good-field norm base change construct the
covariant map on the same norm families. No APF or valued-field structure is
needed for this multiplicative construction.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K M N : Type*) [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

/-- The original source coordinate included in an actual target finite field. -/
def finiteNormLimitCoordinate (D : FiniteLayer K N) : NormLimit K M →*₀ D.val :=
  (finiteLayerPullbackTo K M D).toRingHom.toMonoidWithZeroHom.comp
    (normLimitEval K M (finiteLayerPullbackLayer K M D))

/-- On every original good pair these literal coordinates satisfy the original
finite target norm equation. -/
theorem finiteNormLimitCoordinate_norm (D D' : FiniteLayer K N) (h : D ≤ D')
    (hD : IsGoodFiniteLayer K M D) (hD' : IsGoodFiniteLayer K M D')
    (x : NormLimit K M) :
    FiniteLayer.norm D D' h (finiteNormLimitCoordinate K M N D' x) =
      finiteNormLimitCoordinate K M N D x := by
  exact (goodFinitePair_norm K M D D' h hD hD'
    (normLimitEval K M (finiteLayerPullbackLayer K M D') x)).trans
      (congrArg (finiteLayerPullbackTo K M D)
        (normLimitEval_norm K M (finiteLayerPullbackLayer K M D)
          (finiteLayerPullbackLayer K M D') (finiteLayerPullback_mono K M h) x))

variable [Algebra.IsAlgebraic K M] [Module.Finite M N] [Algebra.IsSeparable M N]

/-- The good original finite fields form a genuinely cofinal index set. -/
theorem goodFiniteLayers_cofinal (E : FiniteLayer K N) :
    ∃ D, IsGoodFiniteLayer K M D ∧ E ≤ D := by
  obtain ⟨D, hED, hD⟩ := exists_goodFiniteLayer_ge K M E
  exact ⟨D, hD, hED⟩

/-- The actual covariant multiplicative map for a finite separable inclusion,
constructed from original coordinates on actual good finite fields. -/
def finiteNormLimitMap : NormLimit K M →*₀ NormLimit K N where
  toFun x := normLimitOfCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun D _ => finiteNormLimitCoordinate K M N D x)
    (fun D D' hD hD' h => finiteNormLimitCoordinate_norm K M N D D' h hD hD' x)
  map_zero' := by
    apply NormLimit.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [normLimitEval_normLimitOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (map_zero (finiteNormLimitCoordinate K M N D)).trans (map_zero _).symm
  map_one' := by
    apply NormLimit.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    rw [normLimitEval_normLimitOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE := hD)]
    exact (map_one (finiteNormLimitCoordinate K M N D)).trans (map_one _).symm
  map_mul' x y := by
    apply NormLimit.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
    intro D hD
    simp only [map_mul, normLimitEval_normLimitOfCofinal K N (IsGoodFiniteLayer K M) (E := D) (hE :=
        hD)]

/-- Every good target coordinate retains precisely the included original
pullback coordinate of the input family. -/
@[simp]
theorem normLimitEval_finiteNormLimitMap (D : FiniteLayer K N)
    (hD : IsGoodFiniteLayer K M D) (x : NormLimit K M) :
    normLimitEval K N D (finiteNormLimitMap K M N x) =
      finiteNormLimitCoordinate K M N D x :=
  normLimitEval_normLimitOfCofinal K N (IsGoodFiniteLayer K M)
    (goodFiniteLayers_cofinal K M N)
    (fun E _ => finiteNormLimitCoordinate K M N E x)
    (fun E F hE hF h => finiteNormLimitCoordinate_norm K M N E F h hE hF x) D hD

/-- Any original target coordinate is computed from any good upper finite
field by its original norm. -/
theorem normLimitEval_finiteNormLimitMap_any (E D : FiniteLayer K N)
    (hD : IsGoodFiniteLayer K M D) (hED : E ≤ D) (x : NormLimit K M) :
    normLimitEval K N E (finiteNormLimitMap K M N x) =
      FiniteLayer.norm E D hED (finiteNormLimitCoordinate K M N D x) := by
  rw [← normLimitEval_norm K N E D hED, normLimitEval_finiteNormLimitMap K M N D hD]

/-- The prescribed original good coordinates determine the covariant map. -/
theorem finiteNormLimitMap_unique (f : NormLimit K M → NormLimit K N)
    (hf : ∀ (D : FiniteLayer K N), IsGoodFiniteLayer K M D →
      ∀ x, normLimitEval K N D (f x) = finiteNormLimitCoordinate K M N D x) :
    f = finiteNormLimitMap K M N := by
  funext x
  apply NormLimit.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  rw [hf D hD x, normLimitEval_finiteNormLimitMap K M N D hD]

/-- The original ambient-element formula at every actual good field. -/
theorem coe_normLimitEval_finiteNormLimitMap (D : FiniteLayer K N)
    (hD : IsGoodFiniteLayer K M D) (x : NormLimit K M) :
    (normLimitEval K N D (finiteNormLimitMap K M N x) : N) =
      algebraMap M N (normLimitEval K M (finiteLayerPullbackLayer K M D) x : M) := by
  rw [normLimitEval_finiteNormLimitMap K M N D hD]
  rfl

/-- Zero detection is inherited from an actual good finite-field coordinate. -/
@[simp]
theorem finiteNormLimitMap_eq_zero_iff (x : NormLimit K M) :
    finiteNormLimitMap K M N x = 0 ↔ x = 0 := by
  obtain ⟨D, hD, _⟩ := goodFiniteLayers_cofinal K M N (FiniteLayer.bottom)
  rw [← normLimitEval_eq_zero_iff K N D,
    normLimitEval_finiteNormLimitMap K M N D hD]
  constructor
  · intro hx
    apply (normLimitEval_eq_zero_iff K M (finiteLayerPullbackLayer K M D) x).mp
    exact (finiteLayerPullbackTo K M D).injective (hx.trans (map_zero _).symm)
  · intro hx
    subst x
    exact map_zero (finiteNormLimitCoordinate K M N D)

end FontaineWintenberger
