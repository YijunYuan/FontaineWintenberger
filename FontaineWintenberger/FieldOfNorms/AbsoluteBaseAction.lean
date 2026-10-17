module

public import FontaineWintenberger.FieldOfNorms.ActionContinuity
public import FontaineWintenberger.FieldOfNorms.FaithfulAction
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The absolute base action on the original norm field

For a normal intermediate field of the actual separable closure, compose
ordinary Galois restriction with the existing original norm-field action.
The action preserves the original coordinates and valuation, has continuous
orbits, and has exactly the pointwise fixer of the intermediate field as kernel.

This is the restriction to the base norm field in Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

/-- The actual absolute Galois group acts on the original norm field through
its ordinary restriction to the given normal APF extension. -/
def normLimitAbsoluteAut :
    letI := normLimitField K L p hL hInfinite
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →*
      (NormLimit K L ≃+* NormLimit K L) := by
  letI := normLimitField K L p hL hInfinite
  exact (normLimitAut K p hL hInfinite).comp (AlgEquiv.restrictNormalHom L)

/-- The absolute base action factors through the actual Galois restriction. -/
@[simp]
theorem normLimitAbsoluteAut_apply (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfinite
    normLimitAbsoluteAut K L p hL hInfinite σ x =
      normLimitAut K p hL hInfinite (AlgEquiv.restrictNormalHom L σ) x := rfl

/-- The original coordinate formula, viewed in the same actual separable closure. -/
theorem coe_normLimitEval_normLimitAbsoluteAut
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (x : NormLimit K L) (E : FiniteLayer K L) :
    letI := normLimitField K L p hL hInfinite
    ((normLimitEval K L E (normLimitAbsoluteAut K L p hL hInfinite σ x) : L) :
        SeparableClosure K) =
      σ ((normLimitEval K L
        (FiniteLayer.map (AlgEquiv.restrictNormalHom L σ).symm.toAlgHom E) x : L) :
          SeparableClosure K) := by
  let := normLimitField K L p hL hInfinite
  let τ := AlgEquiv.restrictNormalHom L σ
  change ((normLimitEval K L E (normLimitMap τ x) : L) : SeparableClosure K) = _
  calc
    _ = ((τ (normLimitEval K L (FiniteLayer.map τ.symm.toAlgHom E) x) : L) :
        SeparableClosure K) :=
      congrArg (fun y : L => (y : SeparableClosure K))
        (coe_normLimitEval_normLimitMap τ x E)
    _ = _ := AlgEquiv.restrictNormalHom_apply L σ _

/-- Absolute Galois transport preserves the original normalized valuation. -/
theorem normLimitAbsoluteAut_valuation
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfinite
    normLimitValuation K L hL (normLimitAbsoluteAut K L p hL hInfinite σ x) =
      normLimitValuation K L hL x :=
  normLimitAut_valuation K p hL hInfinite (AlgEquiv.restrictNormalHom L σ) x

/-- Every absolute Galois orbit is continuous for the original Krull and
norm-field valuation topologies. -/
theorem continuous_normLimitAbsoluteAut_apply :
    letI := normLimitField K L p hL hInfinite
    letI := normLimitValued K L p hL hInfinite
    ∀ x : NormLimit K L,
      Continuous (fun σ : SeparableClosure K ≃ₐ[K] SeparableClosure K =>
        normLimitAbsoluteAut K L p hL hInfinite σ x) := by
  let := normLimitField K L p hL hInfinite
  let := normLimitValued K L p hL hInfinite
  intro x
  exact (continuous_normLimitAut_apply K L p hL hInfinite x).comp
    (InfiniteGalois.restrictNormalHom_continuous L)

/-- The kernel is exactly the original pointwise fixer of the actual field `L`. -/
theorem normLimitAbsoluteAut_ker :
    letI := normLimitField K L p hL hInfinite
    (normLimitAbsoluteAut K L p hL hInfinite).ker = L.fixingSubgroup := by
  let := normLimitField K L p hL hInfinite
  rw [← L.restrictNormalHom_ker]
  ext σ
  change normLimitAut K p hL hInfinite (AlgEquiv.restrictNormalHom L σ) = 1 ↔
    AlgEquiv.restrictNormalHom L σ = 1
  constructor
  · intro h
    apply normLimitAut_injective K L p hL hInfinite
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- Extension of actual normal-field automorphisms to the same separable
closure shows that restricting the absolute action does not change its image. -/
theorem normLimitAbsoluteAut_range :
    letI := normLimitField K L p hL hInfinite
    (normLimitAbsoluteAut K L p hL hInfinite).range =
      (normLimitAut K p hL hInfinite).range := by
  let := normLimitField K L p hL hInfinite
  ext e
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨AlgEquiv.restrictNormalHom L σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := L) (SeparableClosure K) τ
    exact ⟨σ, congrArg (normLimitAut K p hL hInfinite) hσ⟩

end FontaineWintenberger
