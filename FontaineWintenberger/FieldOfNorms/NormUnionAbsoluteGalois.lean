/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.SeparableClosedUnion
public import FontaineWintenberger.FieldOfNorms.NormUnionKrull

/-!
# The absolute Galois equivalence of the original norm field

The same canonical norm-field union is a genuine separable closure. Its
original Krull equivalence, followed by actual separable-closure comparisons,
therefore identifies the absolute Galois groups with their Krull topologies.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section KrullConjugacy

variable {F A B : Type*} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]

/-- Conjugation by an actual field isomorphism pulls back a finite-field
fixer to the fixer of its actual inverse image. -/
theorem autCongr_mem_fixingSubgroup_iff (e : A ≃ₐ[F] B)
    (D : IntermediateField F B) (σ : A ≃ₐ[F] A) :
    e.autCongr σ ∈ D.fixingSubgroup ↔
      σ ∈ (D.map e.symm.toAlgHom).fixingSubgroup := by
  constructor
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
    rintro x ⟨y, hy, rfl⟩
    have hfix := h y hy
    change e (σ (e.symm y)) = y at hfix
    change σ (e.symm y) = e.symm y
    simpa only [AlgEquiv.symm_apply_apply] using congrArg e.symm hfix
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
    intro y hy
    have hfix := h (e.symm y) ⟨y, hy, rfl⟩
    change e (σ (e.symm y)) = y
    rw [hfix, e.apply_symm_apply]

open scoped Topology in
/-- The existing algebraic automorphism conjugacy is continuous for the
actual Krull topologies, without a normality assumption. -/
theorem continuous_autCongr_krull (e : A ≃ₐ[F] B) :
    Continuous e.autCongr := by
  apply continuous_of_continuousAt_one e.autCongr
  change Filter.Tendsto e.autCongr (𝓝 1) (𝓝 (e.autCongr 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff F B s).mp hs
  let : FiniteDimensional F D := hD
  let C := D.map e.symm.toAlgHom
  have hC : FiniteDimensional F C :=
    (IntermediateField.intermediateFieldMap e.symm D).toLinearEquiv.finiteDimensional
  apply (krullTopology_mem_nhds_one_iff F A _).mpr
  refine ⟨C, hC, ?_⟩
  intro σ hσ
  exact hDs ((autCongr_mem_fixingSubgroup_iff e D σ).mpr hσ)

/-- The existing automorphism conjugacy as a genuine Krull homeomorphism. -/
def krullAutCongr (e : A ≃ₐ[F] B) : (A ≃ₐ[F] A) ≃ₜ* (B ≃ₐ[F] B) :=
  { e.autCongr with
    continuous_toFun := continuous_autCongr_krull e
    continuous_invFun := continuous_autCongr_krull e.symm }

/-- The topological comparison retains Mathlib's algebraic conjugacy. -/
@[simp]
theorem krullAutCongr_toMulEquiv (e : A ≃ₐ[F] B) :
    (krullAutCongr e).toMulEquiv = e.autCongr := rfl

/-- The same actual conjugation formula holds on every field element. -/
@[simp]
theorem krullAutCongr_apply (e : A ≃ₐ[F] B) (σ : A ≃ₐ[F] A) (x : B) :
    krullAutCongr e σ x = e (σ (e.symm x)) := rfl

end KrullConjugacy

section OriginalClosures

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsSepClosure K Ω]

include K in
/-- An original separable closure containing the original extension is a
genuine separable closure of that extension too. -/
theorem originalClosure_isSepClosure : IsSepClosure L Ω := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact isSepClosure_iff.mpr ⟨IsSepClosure.sep_closed K, inferInstance⟩

include K in
/-- The actual original closure comparison, chosen over the original base. -/
def originalSeparableClosureEquiv : SeparableClosure L ≃ₐ[L] Ω := by
  let := originalClosure_isSepClosure K L Ω
  exact IsSepClosure.equiv L (SeparableClosure L) Ω

end OriginalClosures

section NormField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω] [Algebra K L] [Algebra.IsSeparable K L]
    [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)

local notation "X" => NormLimit K L
local notation "U" => SeparableNormUnion K L Ω p hL hInfinite

/-- The same original norm-field union is compared to the canonical
separable closure using its proved separable-closure structure. -/
def normUnionSeparableClosureEquiv :
    letI := normLimitField K L p hL hInfinite
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    U ≃ₐ[X] SeparableClosure X := by
  let := normLimitField K L p hL hInfinite
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  let := separableNormUnion_isSepClosure K L Ω p hL hInfinite
  exact IsSepClosure.equiv X U (SeparableClosure X)

/-- The source corollary for the actual original closure and the canonical
separable closure of the same original norm field. -/
def normUnionAbsoluteGaloisEquiv :
    letI := normLimitField K L p hL hInfinite
    (Ω ≃ₐ[L] Ω) ≃ₜ* (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  let := normLimitField K L p hL hInfinite
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  exact (separableNormUnionKrullEquiv K L Ω p hL hInfinite).trans
    (krullAutCongr (normUnionSeparableClosureEquiv K L Ω p hL hInfinite))

/-- The source comparison agrees on the same union with the original
norm-field automorphism, rather than an independently constructed action. -/
theorem normUnionAbsoluteGaloisEquiv_apply (σ : Ω ≃ₐ[L] Ω)
    (z : letI : Algebra.IsSeparable L Ω :=
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω; U) :
    letI := normLimitField K L p hL hInfinite
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    normUnionAbsoluteGaloisEquiv K L Ω p hL hInfinite σ
      (normUnionSeparableClosureEquiv K L Ω p hL hInfinite z) =
      normUnionSeparableClosureEquiv K L Ω p hL hInfinite
        (separableNormUnionMap K L Ω p hL hInfinite Ω σ.toAlgHom z) := by
  let := normLimitField K L p hL hInfinite
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  change (normUnionSeparableClosureEquiv K L Ω p hL hInfinite)
    ((separableNormUnionKrullEquiv K L Ω p hL hInfinite σ)
      ((normUnionSeparableClosureEquiv K L Ω p hL hInfinite).symm
        (normUnionSeparableClosureEquiv K L Ω p hL hInfinite z))) = _
  rw [AlgEquiv.symm_apply_apply, separableNormUnionKrullEquiv_apply]

/-- The actual absolute Galois equivalence on the project's canonical
separable-closure automorphism groups, with their existing Krull topologies. -/
def normLimitAbsoluteGaloisEquiv :
    letI := normLimitField K L p hL hInfinite
    (SeparableClosure L ≃ₐ[L] SeparableClosure L) ≃ₜ*
      (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  let := normLimitField K L p hL hInfinite
  exact (krullAutCongr (originalSeparableClosureEquiv K L Ω)).trans
    (normUnionAbsoluteGaloisEquiv K L Ω p hL hInfinite)

/-- The canonical absolute-group equivalence retains precisely the
original union map after conjugating the original closure. -/
theorem normLimitAbsoluteGaloisEquiv_apply
    (σ : SeparableClosure L ≃ₐ[L] SeparableClosure L)
    (z : letI : Algebra.IsSeparable L Ω :=
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω; U) :
    letI := normLimitField K L p hL hInfinite
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI := separableNormUnionField K L Ω p hL hInfinite
    letI := separableNormUnionAlgebra K L Ω p hL hInfinite
    normLimitAbsoluteGaloisEquiv K L Ω p hL hInfinite σ
      (normUnionSeparableClosureEquiv K L Ω p hL hInfinite z) =
      normUnionSeparableClosureEquiv K L Ω p hL hInfinite
        (separableNormUnionMap K L Ω p hL hInfinite Ω
          ((originalSeparableClosureEquiv K L Ω).autCongr σ).toAlgHom z) := by
  let := normLimitField K L p hL hInfinite
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := separableNormUnionField K L Ω p hL hInfinite
  let := separableNormUnionAlgebra K L Ω p hL hInfinite
  exact normUnionAbsoluteGaloisEquiv_apply K L Ω p hL hInfinite
    ((originalSeparableClosureEquiv K L Ω).autCongr σ) z

/-- The absolute Galois equivalence with no supplied closure or embedding
data: the canonical separable closure of the original field is itself a
separable closure of the original base via the actual composite algebra. -/
def fieldOfNormsAbsoluteGaloisEquiv :
    letI := normLimitField K L p hL hInfinite
    (SeparableClosure L ≃ₐ[L] SeparableClosure L) ≃ₜ*
      (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  let := normLimitField K L p hL hInfinite
  let : Algebra K (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L (SeparableClosure L) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable K (SeparableClosure L) :=
    Algebra.IsSeparable.trans K L (SeparableClosure L)
  let : IsSepClosure K (SeparableClosure L) :=
    isSepClosure_iff.mpr ⟨IsSepClosure.sep_closed L, inferInstance⟩
  exact normUnionAbsoluteGaloisEquiv K L (SeparableClosure L) p hL hInfinite

end NormField

end FontaineWintenberger
