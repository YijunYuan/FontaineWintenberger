module

public import FontaineWintenberger.APF.Residue
public import FontaineWintenberger.FieldOfNorms.Integral
public import FontaineWintenberger.Ramification.NormValuation

/-!
# The actual stable valuation on the multiplicative norm limit

Actual residue inclusions on an APF finite tail are bijective, so actual field
norms preserve their normalized valuations. The original multiplicative limit
therefore has a single coordinate-independent normalized valuation.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

namespace FiniteLayer

local notation "R₀" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- Original field norms preserve normalized valuations whenever their actual
residue inclusion is surjective. No normality is required. -/
theorem normalizedValuation_norm_of_residueInclusion_surjective
    (E F : FiniteLayer K L) (hEF : E ≤ F)
    (hs : Function.Surjective
      (spectralResidueInclusion K (IntermediateField.inclusion hEF))) (x : F.val) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
        (norm E F hEF x) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation F.val x := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  have : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  have := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  have := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E.val) (spectralValuation K F.val)
  have : Module.Finite (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) :=
    Module.Finite.of_restrictScalars_finite R₀ _ _
  have : IsScalarTower (spectralIntegerRing K E.val) E.val F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F.val) (spectralValuation K E.val)
  have : IsScalarTower (spectralIntegerRing K E.val) (spectralIntegerRing K F.val) F.val :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E.val) (spectralValuation K F.val)
  have hf : Module.finrank (IsLocalRing.ResidueField (spectralIntegerRing K E.val))
      (IsLocalRing.ResidueField (spectralIntegerRing K F.val)) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨(spectralResidueInclusion K (IntermediateField.inclusion hEF)).injective, hs⟩
  have hv := normalizedValuation_norm (spectralIntegerRing K E.val)
    (spectralIntegerRing K F.val) E.val F.val x
  rw [local_inertiaDeg_eq_finrank_residueField, hf, pow_one] at hv
  convert hv using 1
  congr 1

end FiniteLayer

/-- Evaluate the original multiplicative limit and then use the actual
normalized valuation of that finite field. -/
def normLimitCoordinateValuation (E : FiniteLayer K L) : NormLimit K L →*₀ WithZero (Multiplicative ℤ) :=
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  v.toMonoidWithZeroHom.comp (normLimitEval K L E)

variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

/-- The normalized coordinate valuations agree on an actual APF finite tail. -/
theorem IsAPF.exists_normLimitCoordinateValuation_stable (hL : IsAPF K L) :
    ∃ E₀ : FiniteLayer K L, ∀ E F : FiniteLayer K L, E₀ ≤ E → E₀ ≤ F →
      ∀ x : NormLimit K L,
        normLimitCoordinateValuation K L E x = normLimitCoordinateValuation K L F x := by
  obtain ⟨E₀, hE₀⟩ := IsAPF.exists_finiteLayer_residueInclusion_surjective K L hL
  refine ⟨E₀, fun E F hE hF x => ?_⟩
  let G := FiniteLayer.sup E F
  have hEG : E ≤ G := FiniteLayer.le_sup_left E F
  have hFG : F ≤ G := FiniteLayer.le_sup_right E F
  have hvE := FiniteLayer.normalizedValuation_norm_of_residueInclusion_surjective K L E G hEG
    (hE₀ E G hE hEG) (normLimitEval K L G x)
  have hvF := FiniteLayer.normalizedValuation_norm_of_residueInclusion_surjective K L F G hFG
    (hE₀ F G hF hFG) (normLimitEval K L G x)
  rw [normLimitEval_norm] at hvE hvF
  exact hvE.trans hvF.symm

/-- The stable normalized multiplicative valuation on the original single
norm-limit carrier. APF supplies and proves the actual finite stable tail. -/
def normLimitValuation (hL : IsAPF K L) : NormLimit K L →*₀ WithZero (Multiplicative ℤ) :=
  normLimitCoordinateValuation K L
    (IsAPF.exists_normLimitCoordinateValuation_stable K L hL).choose

/-- The same normalized valuation is computed by every sufficiently large
original finite coordinate. -/
theorem IsAPF.exists_normLimitValuation_eq_coordinate (hL : IsAPF K L) :
    ∃ E₀ : FiniteLayer K L, ∀ E : FiniteLayer K L, E₀ ≤ E → ∀ x : NormLimit K L,
      normLimitValuation K L hL x = normLimitCoordinateValuation K L E x := by
  let hex := IsAPF.exists_normLimitCoordinateValuation_stable K L hL
  exact ⟨hex.choose, fun E hE x => hex.choose_spec hex.choose E le_rfl hE x⟩

/-- The stable normalized valuation detects zero on the original norm limit. -/
@[simp]
theorem normLimitValuation_eq_zero_iff (hL : IsAPF K L) (x : NormLimit K L) :
    normLimitValuation K L hL x = 0 ↔ x = 0 := by
  simp [normLimitValuation, normLimitCoordinateValuation]

end FontaineWintenberger
