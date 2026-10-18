/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteGalois
public import FontaineWintenberger.FieldOfNorms.EmbeddingFunctor
public import FontaineWintenberger.APF.FiniteExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite separable extensions of the original norm fields

Actual finite normal closures and the original inclusion maps give degree
preservation and separability without normality over the original base.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section ScalarTower

variable (K M N P : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field M] [Field N] [Field P] [Algebra K M] [Algebra K N] [Algebra K P]
    [Algebra M N] [Algebra M P] [Algebra N P]
    [IsScalarTower K M N] [IsScalarTower K M P] [IsScalarTower K N P]
    [IsScalarTower M N P] [Algebra.IsSeparable K M]
    [Algebra.IsSeparable K N] [Algebra.IsSeparable K P]
    [Module.Finite M N] [Module.Finite N P]
    [Algebra.IsSeparable M N] [Algebra.IsSeparable N P]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The three original finite-inclusion field homomorphisms form a genuine
scalar tower, by composition on the original norm-compatible families. -/
theorem finiteNormLimitRingHom_isScalarTower
    [IsAPF K M] [IsAPF K N] [IsAPF K P]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)]
    [Fact (¬ Module.Finite K P)] :
    letI := normLimitField K M p
    letI := normLimitField K N p
    letI := normLimitField K P p
    letI : Module.Finite M P := Module.Finite.trans N P
    letI : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
    letI := (finiteNormLimitRingHom K M N p).toAlgebra
    letI := (finiteNormLimitRingHom K M P p).toAlgebra
    letI := (finiteNormLimitRingHom K N P p).toAlgebra
    IsScalarTower (NormLimit K M) (NormLimit K N) (NormLimit K P) := by
  let := normLimitField K M p
  let := normLimitField K N p
  let := normLimitField K P p
  let : Module.Finite M P := Module.Finite.trans N P
  let : Algebra.IsSeparable M P := Algebra.IsSeparable.trans M N P
  let := (finiteNormLimitRingHom K M N p).toAlgebra
  let := (finiteNormLimitRingHom K M P p).toAlgebra
  let := (finiteNormLimitRingHom K N P p).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (finiteNormLimitMap_trans K M N P x).symm

end ScalarTower

section FiniteSeparable

variable (K M N : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra M N] [IsScalarTower K M N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable K N] [Module.Finite M N]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- A genuine finite normal closure proves finiteness, separability and
preservation of the full original degree for the actual inclusion field map. -/
theorem finiteNormLimit_finite_separable_degree
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := normLimitField K M p
    letI := normLimitField K N p
    letI := (finiteNormLimitRingHom K M N p).toAlgebra
    FiniteDimensional (NormLimit K M) (NormLimit K N) ∧
      Algebra.IsSeparable (NormLimit K M) (NormLimit K N) ∧
      Module.finrank (NormLimit K M) (NormLimit K N) = Module.finrank M N := by
  let : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
  let P := IntermediateField.normalClosure M N (AlgebraicClosure N)
  let : Algebra K P := inferInstance
  let : IsScalarTower K M P := inferInstance
  let : IsScalarTower K N P := IsScalarTower.to₁₃₄ K M N P
  let : Module.Finite M P := inferInstance
  let : Module.Finite N P := Module.Finite.right M N P
  let : IsGalois M P := inferInstance
  let : IsGalois N P := IsGalois.tower_top_of_isGalois M N P
  let : Algebra.IsSeparable K P := Algebra.IsSeparable.trans K M P
  have hP : IsAPF K P := (isAPF_finite_extension_iff K P M).mpr ‹_›
  have hInfiniteP : ¬ Module.Finite K P := by
    intro h
    let : Module.Finite K P := h
    exact (Fact.out : ¬ Module.Finite K M) (FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom K M P).toLinearMap (algebraMap M P).injective)
  have : Fact (¬ Module.Finite K P) := ⟨hInfiniteP⟩
  let := normLimitField K M p
  let := normLimitField K N p
  let := normLimitField K P p
  let := (finiteNormLimitRingHom K M N p).toAlgebra
  let := (finiteNormLimitRingHom K M P p).toAlgebra
  let := (finiteNormLimitRingHom K N P p).toAlgebra
  let : IsScalarTower (NormLimit K M) (NormLimit K N) (NormLimit K P) :=
    finiteNormLimitRingHom_isScalarTower K M N P p
  let : FiniteDimensional (NormLimit K M) (NormLimit K P) :=
    finiteDimensional_finiteNormLimit_of_isGalois K M P p
  let : FiniteDimensional (NormLimit K N) (NormLimit K P) :=
    finiteDimensional_finiteNormLimit_of_isGalois K N P p
  let : FiniteDimensional (NormLimit K M) (NormLimit K N) :=
    FiniteDimensional.of_injective
      (IsScalarTower.toAlgHom (NormLimit K M) (NormLimit K N) (NormLimit K P)).toLinearMap
      (algebraMap (NormLimit K N) (NormLimit K P)).injective
  let : IsGalois (NormLimit K M) (NormLimit K P) :=
    isGalois_finiteNormLimit K M P p
  refine ⟨inferInstance, Algebra.isSeparable_tower_bot_of_isSeparable
    (NormLimit K M) (NormLimit K N) (NormLimit K P), ?_⟩
  have hmul := Module.finrank_mul_finrank (NormLimit K M) (NormLimit K N) (NormLimit K P)
  rw [finrank_finiteNormLimit_of_isGalois K N P p,
    finrank_finiteNormLimit_of_isGalois K M P p,
    ← Module.finrank_mul_finrank M N P] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := N) (M := P)) hmul

/-- The actual finite-inclusion norm-field extension is finite-dimensional. -/
theorem finiteDimensional_finiteNormLimit
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := normLimitField K M p
    letI := normLimitField K N p
    letI := (finiteNormLimitRingHom K M N p).toAlgebra
    FiniteDimensional (NormLimit K M) (NormLimit K N) :=
  (finiteNormLimit_finite_separable_degree K M N p).1

/-- The actual finite-inclusion norm-field extension is separable. -/
theorem isSeparable_finiteNormLimit
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := normLimitField K M p
    letI := normLimitField K N p
    letI := (finiteNormLimitRingHom K M N p).toAlgebra
    Algebra.IsSeparable (NormLimit K M) (NormLimit K N) :=
  (finiteNormLimit_finite_separable_degree K M N p).2.1

/-- The actual finite-inclusion norm-field extension has the full original degree. -/
theorem finrank_finiteNormLimit
    [IsAPF K M] [IsAPF K N]
    [Fact (¬ Module.Finite K M)] [Fact (¬ Module.Finite K N)] :
    letI : Algebra.IsSeparable M N := Algebra.isSeparable_tower_top_of_isSeparable K M N
    letI := normLimitField K M p
    letI := normLimitField K N p
    letI := (finiteNormLimitRingHom K M N p).toAlgebra
    Module.finrank (NormLimit K M) (NormLimit K N) = Module.finrank M N :=
  (finiteNormLimit_finite_separable_degree K M N p).2.2

end FiniteSeparable

section ArbitraryEmbeddings

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- The actual range factorization transports finite dimension, separability
and the full degree to every original finite separable algebra embedding. -/
theorem finiteNormLimitEmbedding_finite_separable_degree (τ : L →ₐ[K] M)
    [Module.Finite τ.fieldRange M] [Algebra.IsSeparable τ.fieldRange M]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] :
    letI := normLimitField K L p
    letI := normLimitField K M p
    letI := (finiteNormLimitEmbeddingRingHom K p τ).toAlgebra
    FiniteDimensional (NormLimit K L) (NormLimit K M) ∧
      Algebra.IsSeparable (NormLimit K L) (NormLimit K M) ∧
      Module.finrank (NormLimit K L) (NormLimit K M) = Module.finrank τ.fieldRange M := by
  have hR : IsAPF K τ.fieldRange := (isAPF_algEquiv K τ.equivFieldRange).mp ‹_›
  have : Fact (¬ Module.Finite K τ.fieldRange) := ⟨not_finite_fieldRange τ⟩
  let := normLimitField K L p
  let := normLimitField K M p
  let := normLimitField K τ.fieldRange p
  let := (finiteNormLimitEmbeddingRingHom K p τ).toAlgebra
  let := (finiteNormLimitRingHom K τ.fieldRange M p).toAlgebra
  let e := normLimitRingEquiv K p τ.equivFieldRange
  have he : (algebraMap (NormLimit K τ.fieldRange) (NormLimit K M)).comp e.toRingHom =
      (RingEquiv.refl (NormLimit K M)).toRingHom.comp
        (algebraMap (NormLimit K L) (NormLimit K M)) := rfl
  have hdeg : Module.finrank (NormLimit K L) (NormLimit K M) =
      Module.finrank τ.fieldRange M :=
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl _) he).trans
      (finrank_finiteNormLimit K τ.fieldRange M p)
  have hpos : 0 < Module.finrank (NormLimit K L) (NormLimit K M) := by
    rw [hdeg]
    exact Module.finrank_pos
  let : FiniteDimensional (NormLimit K L) (NormLimit K M) :=
    FiniteDimensional.of_finrank_pos hpos
  refine ⟨inferInstance, ?_, hdeg⟩
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e (RingEquiv.refl _) he).mpr
    (isSeparable_finiteNormLimit K τ.fieldRange M p)

end ArbitraryEmbeddings

end FontaineWintenberger
