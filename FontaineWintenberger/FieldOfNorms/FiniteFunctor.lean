/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Algebra.FiniteNormPairs
public import FontaineWintenberger.FieldOfNorms.Cofinal

/-!
# Finite inclusions on the original multiplicative fields of norms

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
def FieldOfNorms.finiteCoordinate (D : FiniteIntermediateField K N) : FieldOfNorms K M →*₀ D.val :=
  (FiniteIntermediateField.pullbackTo K M D).toRingHom.toMonoidWithZeroHom.comp
    (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D))

/-- On every original good pair these literal coordinates satisfy the original
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

/-- The good original finite fields form a genuinely cofinal index set. -/
theorem goodFiniteLayers_cofinal (E : FiniteIntermediateField K N) :
    ∃ D, IsGoodFiniteLayer K M D ∧ E ≤ D := by
  obtain ⟨D, hED, hD⟩ := exists_goodFiniteLayer_ge K M E
  exact ⟨D, hD, hED⟩

/-- The actual covariant multiplicative map for a finite separable inclusion,
constructed from original coordinates on actual good finite fields. -/
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

/-- Every good target coordinate retains precisely the included original
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

/-- Any original target coordinate is computed from any good upper finite
field by its original norm. -/
theorem FieldOfNorms.coord_finiteFieldOfNormsMap_any (E D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (hED : E ≤ D) (x : FieldOfNorms K M) :
    FieldOfNorms.coord K N E (FieldOfNorms.finiteMap K M N x) =
      FiniteIntermediateField.norm E D hED (FieldOfNorms.finiteCoordinate K M N D x) := by
  rw [← FieldOfNorms.coord_norm K N E D hED, FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]

/-- The prescribed original good coordinates determine the covariant map. -/
theorem FieldOfNorms.finiteMap_unique (f : FieldOfNorms K M → FieldOfNorms K N)
    (hf : ∀ (D : FiniteIntermediateField K N), IsGoodFiniteLayer K M D →
      ∀ x, FieldOfNorms.coord K N D (f x) = FieldOfNorms.finiteCoordinate K M N D x) :
    f = FieldOfNorms.finiteMap K M N := by
  funext x
  apply FieldOfNorms.ext_cofinal K N (IsGoodFiniteLayer K M) (goodFiniteLayers_cofinal K M N)
  intro D hD
  rw [hf D hD x, FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]

/-- The original ambient-element formula at every actual good field. -/
theorem coe_fieldOfNormsEval_finiteFieldOfNormsMap (D : FiniteIntermediateField K N)
    (hD : IsGoodFiniteLayer K M D) (x : FieldOfNorms K M) :
    (FieldOfNorms.coord K N D (FieldOfNorms.finiteMap K M N x) : N) =
      algebraMap M N (FieldOfNorms.coord K M (FiniteIntermediateField.pullbackLayer K M D) x : M)
          := by
  rw [FieldOfNorms.coord_finiteFieldOfNormsMap K M N D hD]
  rfl

/-- Zero detection is inherited from an actual good finite-field coordinate. -/
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
