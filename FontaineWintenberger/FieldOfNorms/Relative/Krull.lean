/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Relative.Hom
public import Mathlib.FieldTheory.KrullTopology

/-!
# Krull topology on the norm-field automorphism correspondence

The finite norm-field images are finite and cofinal among finite
subfields of the relative field of norms. Full faithfulness identifies their pointwise
fixing subgroups, giving a homeomorphism for the Krull topologies.

Reference: Wintenberger, Corollary 3.2.3, finite-fixer argument.

## Main definitions

* `RelFieldOfNorms.finiteImage`: The finite norm-field image inside the same relative field of
  norms.
* `RelFieldOfNorms.krullEquiv`: The automorphism correspondence as a Krull-topological group
  isomorphism.

## Main results

* `RelFieldOfNorms.map_eq_on_stage_iff`: Equality of union maps on one finite stage reflects and is
  reflected by equality of the finite restrictions.
* `RelFieldOfNorms.finiteImage_finite`: Each finite image is a finite extension of the base norm
  field.
* `mem_relFieldOfNormsFiniteImage`: The image has exactly the stage representatives as its elements.
* `RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff`: Full faithfulness identifies the finite
  pointwise fixing subgroups.
* `RelFieldOfNorms.exists_finiteImage_ge`: Every finite target subfield lies in one finite image.
* `continuous_relFieldOfNormsAutEquiv`: The norm-union automorphism correspondence is
  Krull-continuous.
* `continuous_relFieldOfNormsAutEquiv_symm`: The inverse correspondence is continuous for the same
  Krull topologies.
* `RelFieldOfNorms.krullEquiv_toMulEquiv`: The topological comparison retains exactly the algebraic
  correspondence.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Equality of union maps on one finite stage reflects and
is reflected by equality of the finite restrictions. -/
theorem RelFieldOfNorms.map_eq_on_stage_iff (s t : M →ₐ[L] M)
    (Q : FiniteIntermediateField L M) :
    (∀ x : FieldOfNorms K Q.val,
      RelFieldOfNorms.mapEquiv K L M M s
          (RelFieldOfNorms.of K L M Q x) =
        RelFieldOfNorms.mapEquiv K L M M t
          (RelFieldOfNorms.of K L M Q x)) ↔
      ∀ a : Q.val, s (a : M) = t (a : M) := by
  let P := FiniteIntermediateField.sup (FiniteIntermediateField.map s Q)
      (FiniteIntermediateField.map t Q)
  let φ : Q.val →ₐ[L] P.val :=
    (IntermediateField.inclusion (FiniteIntermediateField.le_sup_left _ _)).comp
      (FiniteIntermediateField.equivMap s Q).toAlgHom
  let ψ : Q.val →ₐ[L] P.val :=
    (IntermediateField.inclusion (FiniteIntermediateField.le_sup_right _ _)).comp
      (FiniteIntermediateField.equivMap t Q).toAlgHom
  have hs (x : FieldOfNorms K Q.val) :
      RelFieldOfNorms.mapEquiv K L M M s
          (RelFieldOfNorms.of K L M Q x) =
        RelFieldOfNorms.of K L M P
          (FieldOfNorms.algHomEquiv K L Q.val P.val φ x) :=
    RelFieldOfNorms.algMap_of_factor K L M M s Q P φ (fun _ => rfl) x
  have ht (x : FieldOfNorms K Q.val) :
      RelFieldOfNorms.mapEquiv K L M M t
          (RelFieldOfNorms.of K L M Q x) =
        RelFieldOfNorms.of K L M P
          (FieldOfNorms.algHomEquiv K L Q.val P.val ψ x) :=
    RelFieldOfNorms.algMap_of_factor K L M M t Q P ψ (fun _ => rfl) x
  constructor
  · intro h
    exact RelFieldOfNorms.finiteHom_faithful K L M M Q P P φ ψ
      (fun x => (hs x).symm.trans ((h x).trans (ht x)))
  · intro h x
    rw [hs, ht]
    have he : φ = ψ := AlgHom.ext (fun a => Subtype.ext (h a))
    rw [he]

/-- The finite norm-field image inside the same relative field of norms. -/
def RelFieldOfNorms.finiteImage (Q : FiniteIntermediateField L M) :
    IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L M) := by
  exact (RelFieldOfNorms.ofAlgHom K L M Q).fieldRange

/-- Each finite image is a finite extension of the base norm field. -/
theorem RelFieldOfNorms.finiteImage_finite (Q : FiniteIntermediateField L M) :
    Module.Finite (FieldOfNorms K L) (RelFieldOfNorms.finiteImage K L M Q) := by
  let : Module.Finite (FieldOfNorms K L) (FieldOfNorms K Q.val) :=
    (FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion K L Q.val
).1
  exact Module.Finite.equiv
    (RelFieldOfNorms.ofAlgHom K L M Q).equivFieldRange.toLinearEquiv

/-- The image has exactly the stage representatives as its elements. -/
@[simp]
theorem mem_relFieldOfNormsFiniteImage (Q : FiniteIntermediateField L M)
    (z : RelFieldOfNorms K L M) :
    z ∈ RelFieldOfNorms.finiteImage K L M Q ↔
      ∃ x : FieldOfNorms K Q.val, RelFieldOfNorms.of K L M Q x = z := Iff.rfl

/-- Full faithfulness identifies the finite pointwise fixing subgroups. -/
theorem RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff
    (Q : FiniteIntermediateField L M) (σ : M ≃ₐ[L] M) :
    RelFieldOfNorms.autEquiv K L M σ ∈
        (RelFieldOfNorms.finiteImage K L M Q).fixingSubgroup ↔
      σ ∈ Q.val.fixingSubgroup := by
  have hstage :
      (∀ x : FieldOfNorms K Q.val,
        RelFieldOfNorms.autEquiv K L M σ
            (RelFieldOfNorms.of K L M Q x) =
          RelFieldOfNorms.of K L M Q x) ↔
        ∀ a : Q.val, σ (a : M) = (a : M) := by
    simpa only [RelFieldOfNorms.autEquiv_apply, RelFieldOfNorms.map_id,
      RingHom.id_apply, AlgHom.id_apply, AlgEquiv.coe_toAlgHom] using
      RelFieldOfNorms.map_eq_on_stage_iff K L M
        σ.toAlgHom (AlgHom.id L M) Q
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h a ha
    exact hstage.mp (fun x => h _
      ((mem_relFieldOfNormsFiniteImage K L M Q _).mpr ⟨x, rfl⟩)) ⟨a, ha⟩
  · intro h z hz
    obtain ⟨x, rfl⟩ := (mem_relFieldOfNormsFiniteImage K L M Q z).mp hz
    exact hstage.mpr (fun a => h a a.property) x

/-- Every finite target subfield lies in one finite image. -/
theorem RelFieldOfNorms.exists_finiteImage_ge :
    ∀ (D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L M))
      [FiniteDimensional (FieldOfNorms K L) D],
      ∃ Q : FiniteIntermediateField L M, D ≤ RelFieldOfNorms.finiteImage K L M Q := by
  intro D _
  obtain ⟨Q, x, hx⟩ := RelFieldOfNorms.exists_finiteStage K L M
    (fun i => ((Module.finBasis (FieldOfNorms K L) D i : D) :
      RelFieldOfNorms K L M))
  obtain ⟨g, hg⟩ := exists_algHom_factor_of_basis_mem_range D.val
    (RelFieldOfNorms.ofAlgHom K L M Q)
    (fun i => ⟨x i, hx i⟩)
  refine ⟨Q, fun a ha => ?_⟩
  exact (mem_relFieldOfNormsFiniteImage K L M Q a).mpr
    ⟨g ⟨a, ha⟩, AlgHom.congr_fun hg ⟨a, ha⟩⟩

open scoped Topology in
/-- The norm-union automorphism correspondence is Krull-continuous. -/
theorem continuous_relFieldOfNormsAutEquiv :
    Continuous (RelFieldOfNorms.autEquiv K L M) := by
  apply continuous_of_continuousAt_one
    (RelFieldOfNorms.autEquiv K L M)
  change Filter.Tendsto (RelFieldOfNorms.autEquiv K L M) (𝓝 1)
    (𝓝 (RelFieldOfNorms.autEquiv K L M 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff (FieldOfNorms K L)
    (RelFieldOfNorms K L M) s).mp hs
  let : FiniteDimensional (FieldOfNorms K L) D := hD
  obtain ⟨Q, hDQ⟩ := RelFieldOfNorms.exists_finiteImage_ge K L M D
  apply (krullTopology_mem_nhds_one_iff L M _).mpr
  refine ⟨Q.val, inferInstance, ?_⟩
  intro σ hσ
  apply hDs
  exact D.fixingSubgroup_le hDQ
    ((RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff K L M Q σ).mpr hσ)

open scoped Topology in
/-- The inverse correspondence is continuous for the same Krull topologies. -/
theorem continuous_relFieldOfNormsAutEquiv_symm :
    Continuous (RelFieldOfNorms.autEquiv K L M).symm := by
  apply continuous_of_continuousAt_one
    (RelFieldOfNorms.autEquiv K L M).symm
  change Filter.Tendsto (RelFieldOfNorms.autEquiv K L M).symm (𝓝 1)
    (𝓝 ((RelFieldOfNorms.autEquiv K L M).symm 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff L M s).mp hs
  let Q : FiniteIntermediateField L M := ⟨D, hD⟩
  let B := RelFieldOfNorms.finiteImage K L M Q
  let : FiniteDimensional (FieldOfNorms K L) B :=
    RelFieldOfNorms.finiteImage_finite K L M Q
  apply (krullTopology_mem_nhds_one_iff (FieldOfNorms K L)
    (RelFieldOfNorms K L M) _).mpr
  refine ⟨B, inferInstance, ?_⟩
  intro τ hτ
  apply hDs
  apply (RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff K L M Q
    ((RelFieldOfNorms.autEquiv K L M).symm τ)).mp
  simpa only [B, SetLike.mem_coe, MulEquiv.apply_symm_apply] using hτ

/-- The automorphism correspondence as a Krull-topological group isomorphism. -/
def RelFieldOfNorms.krullEquiv :
    (M ≃ₐ[L] M) ≃ₜ* (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  exact { RelFieldOfNorms.autEquiv K L M with
    continuous_toFun := continuous_relFieldOfNormsAutEquiv K L M
    continuous_invFun := continuous_relFieldOfNormsAutEquiv_symm K L M }

/-- The topological comparison retains exactly the algebraic correspondence. -/
@[simp]
theorem RelFieldOfNorms.krullEquiv_toMulEquiv :
    (RelFieldOfNorms.krullEquiv K L M).toMulEquiv =
      RelFieldOfNorms.autEquiv K L M := rfl

/-- The Krull homeomorphism acts by the finite-family union map. -/
@[simp]
theorem RelFieldOfNorms.krullEquiv_apply (σ : M ≃ₐ[L] M)
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.krullEquiv K L M σ z =
      RelFieldOfNorms.mapEquiv K L M M σ.toAlgHom z := rfl

end FontaineWintenberger
