/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.NormUnionAutomorphisms
public import Mathlib.FieldTheory.KrullTopology

/-!
# Krull topology on the original norm-field automorphism correspondence

The original finite norm-field images are finite and cofinal among finite
subfields of the canonical union. Full faithfulness identifies their pointwise
fixing subgroups, giving a homeomorphism for the actual Krull topologies.

Reference: Wintenberger, Corollary 3.2.3, finite-fixer argument.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Equality of actual union maps on one original finite stage reflects and
is reflected by equality of the original finite restrictions. -/
theorem separableNormUnionMap_eq_on_stage_iff (s t : M →ₐ[L] M)
    (Q : FiniteLayer L M) :
    (∀ x : NormLimit K Q.val,
      separableNormUnionMap K L M p M s
          (separableNormUnionOf K L M p Q x) =
        separableNormUnionMap K L M p M t
          (separableNormUnionOf K L M p Q x)) ↔
      ∀ a : Q.val, s (a : M) = t (a : M) := by
  let P := FiniteLayer.sup (FiniteLayer.map s Q) (FiniteLayer.map t Q)
  let φ : Q.val →ₐ[L] P.val :=
    (IntermediateField.inclusion (FiniteLayer.le_sup_left _ _)).comp
      (FiniteLayer.equivMap s Q).toAlgHom
  let ψ : Q.val →ₐ[L] P.val :=
    (IntermediateField.inclusion (FiniteLayer.le_sup_right _ _)).comp
      (FiniteLayer.equivMap t Q).toAlgHom
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let : Algebra.IsSeparable K P.val := Algebra.IsSeparable.trans K L P.val
  have hs (x : NormLimit K Q.val) :
      separableNormUnionMap K L M p M s
          (separableNormUnionOf K L M p Q x) =
        separableNormUnionOf K L M p P
          (finiteNormLimitHomEquiv K L Q.val P.val p φ x) :=
    separableNormUnionAlgMap_of_factor K L M p M s Q P φ (fun _ => rfl) x
  have ht (x : NormLimit K Q.val) :
      separableNormUnionMap K L M p M t
          (separableNormUnionOf K L M p Q x) =
        separableNormUnionOf K L M p P
          (finiteNormLimitHomEquiv K L Q.val P.val p ψ x) :=
    separableNormUnionAlgMap_of_factor K L M p M t Q P ψ (fun _ => rfl) x
  constructor
  · intro h
    exact separableNormUnion_finiteHom_faithful K L M p M Q P P φ ψ
      (fun x => (hs x).symm.trans ((h x).trans (ht x)))
  · intro h x
    rw [hs, ht]
    have he : φ = ψ := AlgHom.ext (fun a => Subtype.ext (h a))
    rw [he]

/-- The actual finite original norm-field image inside the same canonical union. -/
def separableNormUnionFiniteImage (Q : FiniteLayer L M) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    IntermediateField (NormLimit K L) (SeparableNormUnion K L M p) := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionAlgebra K L M p
  letI := separableNormUnionStageField K L M p Q
  letI := separableNormUnionStageAlgebra K L M p Q
  exact (separableNormUnionOfAlgHom K L M p Q).fieldRange

/-- Each actual finite original image is a finite extension of the base norm field. -/
theorem separableNormUnionFiniteImage_finite (Q : FiniteLayer L M) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    letI : Module (NormLimit K L) (SeparableNormUnion K L M p) :=
      Algebra.toModule
    letI : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
      (Algebra.toModule : Module (NormLimit K L)
        (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
    Module.Finite (NormLimit K L) (separableNormUnionFiniteImage K L M p Q) := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let : Module (NormLimit K L) (SeparableNormUnion K L M p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
  let := separableNormUnionStageField K L M p Q
  let := separableNormUnionStageAlgebra K L M p Q
  let : Module (NormLimit K L) (NormLimit K Q.val) := Algebra.toModule
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K L Q.val
  let : Module.Finite (NormLimit K L) (NormLimit K Q.val) :=
    (finiteNormLimit_finite_separable_degree K L Q.val p
      ).1
  exact Module.Finite.equiv
    (separableNormUnionOfAlgHom K L M p Q).equivFieldRange.toLinearEquiv

/-- The actual image has exactly the original stage representatives as its elements. -/
@[simp]
theorem mem_separableNormUnionFiniteImage (Q : FiniteLayer L M)
    (z : SeparableNormUnion K L M p) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    z ∈ separableNormUnionFiniteImage K L M p Q ↔
      ∃ x : NormLimit K Q.val, separableNormUnionOf K L M p Q x = z := Iff.rfl

/-- Full faithfulness identifies the actual finite pointwise fixing subgroups. -/
theorem separableNormUnionAutEquiv_mem_fixingSubgroup_iff
    (Q : FiniteLayer L M) (σ : M ≃ₐ[L] M) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    separableNormUnionAutEquiv K L M p σ ∈
        (separableNormUnionFiniteImage K L M p Q).fixingSubgroup ↔
      σ ∈ Q.val.fixingSubgroup := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  have hstage :
      (∀ x : NormLimit K Q.val,
        separableNormUnionAutEquiv K L M p σ
            (separableNormUnionOf K L M p Q x) =
          separableNormUnionOf K L M p Q x) ↔
        ∀ a : Q.val, σ (a : M) = (a : M) := by
    simpa only [separableNormUnionAutEquiv_apply, separableNormUnionMap_id,
      RingHom.id_apply, AlgHom.id_apply, AlgEquiv.coe_toAlgHom] using
      separableNormUnionMap_eq_on_stage_iff K L M p
        σ.toAlgHom (AlgHom.id L M) Q
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h a ha
    exact hstage.mp (fun x => h _
      ((mem_separableNormUnionFiniteImage K L M p Q _).mpr ⟨x, rfl⟩)) ⟨a, ha⟩
  · intro h z hz
    obtain ⟨x, rfl⟩ := (mem_separableNormUnionFiniteImage K L M p Q z).mp hz
    exact hstage.mpr (fun a => h a a.property) x

/-- Every actual finite target subfield lies in one actual original finite image. -/
theorem separableNormUnion_exists_finiteImage_ge :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    letI : Module (NormLimit K L) (SeparableNormUnion K L M p) :=
      Algebra.toModule
    letI : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
      (Algebra.toModule : Module (NormLimit K L)
        (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
    ∀ (D : IntermediateField (NormLimit K L) (SeparableNormUnion K L M p))
      [FiniteDimensional (NormLimit K L) D],
      ∃ Q : FiniteLayer L M, D ≤ separableNormUnionFiniteImage K L M p Q := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let : Module (NormLimit K L) (SeparableNormUnion K L M p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
  intro D _
  obtain ⟨Q, x, hx⟩ := separableNormUnion_exists_finiteStage K L M p
    (fun i => ((Module.finBasis (NormLimit K L) D i : D) :
      SeparableNormUnion K L M p))
  let := separableNormUnionStageField K L M p Q
  let := separableNormUnionStageAlgebra K L M p Q
  obtain ⟨g, hg⟩ := exists_algHom_factor_of_basis_mem_range D.val
    (separableNormUnionOfAlgHom K L M p Q)
    (fun i => ⟨x i, hx i⟩)
  refine ⟨Q, fun a ha => ?_⟩
  exact (mem_separableNormUnionFiniteImage K L M p Q a).mpr
    ⟨g ⟨a, ha⟩, AlgHom.congr_fun hg ⟨a, ha⟩⟩

open scoped Topology in
/-- The original norm-union automorphism correspondence is Krull-continuous. -/
theorem continuous_separableNormUnionAutEquiv :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    Continuous (separableNormUnionAutEquiv K L M p) := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let : Module (NormLimit K L) (SeparableNormUnion K L M p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
  apply continuous_of_continuousAt_one
    (separableNormUnionAutEquiv K L M p)
  change Filter.Tendsto (separableNormUnionAutEquiv K L M p) (𝓝 1)
    (𝓝 (separableNormUnionAutEquiv K L M p 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff (NormLimit K L)
    (SeparableNormUnion K L M p) s).mp hs
  let : FiniteDimensional (NormLimit K L) D := hD
  obtain ⟨Q, hDQ⟩ := separableNormUnion_exists_finiteImage_ge K L M p D
  apply (krullTopology_mem_nhds_one_iff L M _).mpr
  refine ⟨Q.val, inferInstance, ?_⟩
  intro σ hσ
  apply hDs
  exact D.fixingSubgroup_le hDQ
    ((separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L M p Q σ).mpr hσ)

open scoped Topology in
/-- The inverse correspondence is continuous for the same actual Krull topologies. -/
theorem continuous_separableNormUnionAutEquiv_symm :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    Continuous (separableNormUnionAutEquiv K L M p).symm := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let : Module (NormLimit K L) (SeparableNormUnion K L M p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L M p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L M p)).toDistribMulAction.toMulAction
  apply continuous_of_continuousAt_one
    (separableNormUnionAutEquiv K L M p).symm
  change Filter.Tendsto (separableNormUnionAutEquiv K L M p).symm (𝓝 1)
    (𝓝 ((separableNormUnionAutEquiv K L M p).symm 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff L M s).mp hs
  let Q : FiniteLayer L M := ⟨D, hD⟩
  let B := separableNormUnionFiniteImage K L M p Q
  let : FiniteDimensional (NormLimit K L) B :=
    separableNormUnionFiniteImage_finite K L M p Q
  apply (krullTopology_mem_nhds_one_iff (NormLimit K L)
    (SeparableNormUnion K L M p) _).mpr
  refine ⟨B, inferInstance, ?_⟩
  intro τ hτ
  apply hDs
  apply (separableNormUnionAutEquiv_mem_fixingSubgroup_iff K L M p Q
    ((separableNormUnionAutEquiv K L M p).symm τ)).mp
  simpa only [B, SetLike.mem_coe, MulEquiv.apply_symm_apply] using hτ

/-- The original automorphism correspondence as a Krull-topological group isomorphism. -/
def separableNormUnionKrullEquiv :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    (M ≃ₐ[L] M) ≃ₜ* (SeparableNormUnion K L M p ≃ₐ[NormLimit K L]
      SeparableNormUnion K L M p) := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionAlgebra K L M p
  exact { separableNormUnionAutEquiv K L M p with
    continuous_toFun := continuous_separableNormUnionAutEquiv K L M p
    continuous_invFun := continuous_separableNormUnionAutEquiv_symm K L M p }

/-- The topological comparison retains exactly the original algebraic correspondence. -/
@[simp]
theorem separableNormUnionKrullEquiv_toMulEquiv :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    (separableNormUnionKrullEquiv K L M p).toMulEquiv =
      separableNormUnionAutEquiv K L M p := rfl

/-- The Krull homeomorphism acts by the same original finite-family union map. -/
@[simp]
theorem separableNormUnionKrullEquiv_apply (σ : M ≃ₐ[L] M)
    (z : SeparableNormUnion K L M p) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    separableNormUnionKrullEquiv K L M p σ z =
      separableNormUnionMap K L M p M σ.toAlgHom z := rfl

end FontaineWintenberger
