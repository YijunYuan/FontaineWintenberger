/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Functor.FullyFaithful
public import FontaineWintenberger.FieldOfNorms.Relative.Defs
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Homomorphisms of the relative field of norms

## Finite-stage factorization and gluing of norm-field Hom maps

Finite basis images lie in one target stage. Canonical range
factorization then gives a finite-stage algebra homomorphism;
finite full faithfulness supplies and glues the field embeddings.

## Automorphisms of the separable relative field of norms

The field-of-norms functor identifies algebraic endomorphism monoids.
Passing to their units gives the canonical automorphism-group correspondence,
with the finite-image formula and rational valuation preservation.

Reference: Wintenberger, Theorem 3.2.2(ii), and its automorphism consequence.

## Main definitions

* `RelFieldOfNorms.homEquiv`: The canonical full Hom equivalence is the union functor.
* `RelFieldOfNorms.endHom`: The union functor preserves the endomorphism monoid.
* `RelFieldOfNorms.endEquiv`: Full faithfulness identifies the endomorphism monoids.
* `RelFieldOfNorms.autEquiv`: The canonical automorphism-group correspondence on the fields.

## Main results

* `exists_algHom_factor_of_basis_mem_range`: Containment of the images of a finite basis gives
  canonical factorization through the embedded target field.
* `RelFieldOfNorms.exists_algHom_factor`: A finite algebraic Hom into the relative field of norms
  factors through one finite stage.
* `RelFieldOfNorms.exists_finite_preimage`: Every Hom from a finite norm field to the union comes
  from a field embedding into a finite target layer.
* `RelFieldOfNorms.of_finiteHom_inclusion`: Enlarging the target layer leaves the induced map into
  the same relative field of norms unchanged.
* `RelFieldOfNorms.finiteHom_faithful`: Equality of maps into the union reflects equality of the
  finite-source embeddings, even when their target stages differ.
* `RelFieldOfNorms.finiteHom_inclusion`: Restricting a finite embedding to a smaller source stage
  gives the same finite Hom evaluated after the transition map.
* `RelFieldOfNorms.exists_hom`: A Hom of the norm-field unions determines an algebra embedding whose
  finite restrictions realize all its finite-stage maps.
* `RelFieldOfNorms.algMap_of_factor`: A finite-stage factorization computes the induced union map by
  the same finite Hom, independently of the chosen containing stage.

## Notation

The following notation is local to this file.

* `p` denotes the residue characteristic `residueChar K`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- Containment of the images of a finite basis gives canonical
factorization through the embedded target field. -/
theorem exists_algHom_factor_of_basis_mem_range
    {F A B C : Type*} [Field F] [Field A] [Field B] [Field C]
    [Algebra F A] [Algebra F B] [Algebra F C] [FiniteDimensional F A]
    (φ : A →ₐ[F] C) (ι : B →ₐ[F] C)
    (hmem : ∀ i : Fin (Module.finrank F A),
      φ (Module.finBasis F A i) ∈ ι.fieldRange) :
    ∃ ψ : A →ₐ[F] B, ι.comp ψ = φ := by
  have hfull (a : A) : φ a ∈ ι.fieldRange := by
    rw [← (Module.finBasis F A).sum_repr a, map_sum]
    apply ι.fieldRange.toSubalgebra.sum_mem
    intro i _
    rw [map_smul]
    exact ι.fieldRange.toSubalgebra.smul_mem (hmem i) ((Module.finBasis F A).repr a i)
  let φ' : A →ₐ[F] ι.fieldRange := φ.codRestrict ι.fieldRange.toSubalgebra hfull
  let ψ := ι.equivFieldRange.symm.toAlgHom.comp φ'
  refine ⟨ψ, AlgHom.ext (fun a => ?_)⟩
  exact congrArg Subtype.val (ι.equivFieldRange.apply_symm_apply (φ' a))

section NormUnion

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A finite algebraic Hom into the relative field of norms factors through
one finite stage. -/
theorem RelFieldOfNorms.exists_algHom_factor :
    ∀ {A : Type*} [Field A] [Algebra (FieldOfNorms K L) A]
      [FiniteDimensional (FieldOfNorms K L) A]
      (f : A →ₐ[FieldOfNorms K L] RelFieldOfNorms K L M),
      ∃ N : FiniteIntermediateField L M,
        ∃ g : A →ₐ[FieldOfNorms K L] FieldOfNorms K N.val,
          (RelFieldOfNorms.ofAlgHom K L M N).comp g = f := by
  intro A _ _ _ f
  obtain ⟨N, x, hx⟩ := RelFieldOfNorms.exists_finiteStage K L M
    (fun i => f (Module.finBasis (FieldOfNorms K L) A i))
  refine ⟨N, exists_algHom_factor_of_basis_mem_range f
    (RelFieldOfNorms.ofAlgHom K L M N) (fun i => ?_)⟩
  exact ⟨x i, hx i⟩

variable (M₁ : Type*) [Field M₁] [Algebra K M₁] [Algebra L M₁]
    [IsScalarTower K L M₁] [Algebra.IsSeparable L M₁]

/-- Every Hom from a finite norm field to the union comes from
a field embedding into a finite target layer. -/
theorem RelFieldOfNorms.exists_finite_preimage (Q : FiniteIntermediateField L M₁) :
    ∀ f : FieldOfNorms K Q.val →ₐ[FieldOfNorms K L] RelFieldOfNorms K L M,
      ∃ R : FiniteIntermediateField L M,
        ∃ φ : Q.val →ₐ[L] R.val,
          (RelFieldOfNorms.ofAlgHom K L M R).comp
            (FieldOfNorms.mapAlgHom K L Q.val R.val
              φ) = f := by
  let : FiniteDimensional (FieldOfNorms K L) (FieldOfNorms K Q.val) :=
    FieldOfNorms.finiteDimensional K L Q.val
  intro f
  obtain ⟨R, g, hg⟩ := RelFieldOfNorms.exists_algHom_factor K L M f
  let e := FieldOfNorms.algHomEquiv K L Q.val R.val
  refine ⟨R, e.symm g, ?_⟩
  exact (congrArg (fun j =>
    (RelFieldOfNorms.ofAlgHom K L M R).comp j)
    (e.apply_symm_apply g)).trans hg

/-- Enlarging the target layer leaves the induced map into the same
relative field of norms unchanged. -/
theorem RelFieldOfNorms.of_finiteHom_inclusion (Q : FiniteIntermediateField L M₁)
    (R P : FiniteIntermediateField L M) (hRP : R ≤ P) (φ : Q.val →ₐ[L] R.val)
    (x : FieldOfNorms K Q.val) :
    RelFieldOfNorms.of K L M P
        (FieldOfNorms.algHomEquiv K L Q.val P.val
          ((IntermediateField.inclusion hRP).comp φ) x) =
      RelFieldOfNorms.of K L M R
        (FieldOfNorms.algHomEquiv K L Q.val R.val φ x) := by
  let y := FieldOfNorms.algHomEquiv K L Q.val R.val φ x
  have hc := congrArg (fun f => f x)
    (FieldOfNorms.mapAlgHom_comp K L Q.val R.val P.val
      φ
      (IntermediateField.inclusion hRP))
  have hi : FieldOfNorms.algHomEquiv K L R.val P.val
      (IntermediateField.inclusion hRP) y =
      RelFieldOfNorms.transition K L M R P hRP y := by
    let : Algebra R.val P.val := (IntermediateField.inclusion hRP).toRingHom.toAlgebra
    let : IsScalarTower L R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower K R.val P.val := IsScalarTower.of_algebraMap_eq' rfl
    exact FieldOfNorms.mapAlgHom_algebraMap K L R.val P.val
      y
  exact (congrArg (RelFieldOfNorms.of K L M P) hc).trans
    ((congrArg (RelFieldOfNorms.of K L M P) hi).trans
      (RelFieldOfNorms.of_transition K L M R P hRP y))

/-- Equality of maps into the union reflects equality of the
finite-source embeddings, even when their target stages differ. -/
theorem RelFieldOfNorms.finiteHom_faithful (Q : FiniteIntermediateField L M₁)
    (R S : FiniteIntermediateField L M) (φ : Q.val →ₐ[L] R.val) (ψ : Q.val →ₐ[L] S.val) :
    (∀ x : FieldOfNorms K Q.val,
      RelFieldOfNorms.of K L M R
          (FieldOfNorms.algHomEquiv K L Q.val R.val φ x) =
        RelFieldOfNorms.of K L M S
          (FieldOfNorms.algHomEquiv K L Q.val S.val ψ x)) →
      ∀ a : Q.val, (φ a : M) = (ψ a : M) := by
  intro h a
  let P : FiniteIntermediateField L M := FiniteIntermediateField.sup R S
  have he : (IntermediateField.inclusion (show R ≤ P from FiniteIntermediateField.le_sup_left R
      S)).comp φ =
      (IntermediateField.inclusion (show S ≤ P from FiniteIntermediateField.le_sup_right R S)).comp
          ψ := by
    apply (FieldOfNorms.algHomEquiv K L Q.val P.val).injective
    apply AlgHom.ext
    intro x
    apply RelFieldOfNorms.of_injective K L M P
    exact (RelFieldOfNorms.of_finiteHom_inclusion K L M M₁
      Q R P (FiniteIntermediateField.le_sup_left R S) φ x).trans ((h x).trans
        (RelFieldOfNorms.of_finiteHom_inclusion K L M M₁
          Q S P (FiniteIntermediateField.le_sup_right R S) ψ x).symm)
  exact congrArg (fun z : P.val => (z : M)) (AlgHom.congr_fun he a)

/-- Restricting a finite embedding to a smaller source stage gives
the same finite Hom evaluated after the transition map. -/
theorem RelFieldOfNorms.finiteHom_inclusion (Q T : FiniteIntermediateField L M₁)
    (hQT : Q ≤ T) (R : FiniteIntermediateField L M) (ψ : T.val →ₐ[L] R.val)
    (x : FieldOfNorms K Q.val) :
    FieldOfNorms.algHomEquiv K L Q.val R.val
        (ψ.comp (IntermediateField.inclusion hQT)) x =
      FieldOfNorms.algHomEquiv K L T.val R.val ψ
        (RelFieldOfNorms.transition K L M₁ Q T hQT x) := by
  have hc := congrArg (fun f => f x)
    (FieldOfNorms.mapAlgHom_comp K L Q.val T.val R.val
      (IntermediateField.inclusion hQT) ψ)
  have hi : FieldOfNorms.algHomEquiv K L Q.val T.val
      (IntermediateField.inclusion hQT) x =
      RelFieldOfNorms.transition K L M₁ Q T hQT x := by
    let : Algebra Q.val T.val := (IntermediateField.inclusion hQT).toRingHom.toAlgebra
    let : IsScalarTower L Q.val T.val := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower K Q.val T.val := IsScalarTower.of_algebraMap_eq' rfl
    exact FieldOfNorms.mapAlgHom_algebraMap K L Q.val T.val
      x
  exact hc.trans (congrArg
    (FieldOfNorms.algHomEquiv K L T.val R.val ψ) hi)

/-- A Hom of the norm-field unions determines an algebra
embedding whose finite restrictions realize all its finite-stage maps. -/
theorem RelFieldOfNorms.exists_hom :
    ∀ f : RelFieldOfNorms K L M₁ →ₐ[FieldOfNorms K L]
        RelFieldOfNorms K L M,
      ∃ t : M₁ →ₐ[L] M, ∀ Q : FiniteIntermediateField L M₁,
        ∃ R : FiniteIntermediateField L M,
          ∃ φ : Q.val →ₐ[L] R.val,
            (∀ a : Q.val, (φ a : M) = t a) ∧
              (RelFieldOfNorms.ofAlgHom K L M R).comp
                (FieldOfNorms.algHomEquiv K L Q.val R.val φ) =
                f.comp (RelFieldOfNorms.ofAlgHom K L M₁ Q) := by
  classical
  intro f
  choose R φ hφ using fun Q : FiniteIntermediateField L M₁ =>
    RelFieldOfNorms.exists_finite_preimage K L M M₁ Q
      (f.comp (RelFieldOfNorms.ofAlgHom K L M₁ Q))
  let family (Q : FiniteIntermediateField L M₁) : Q.val →ₐ[L] M := (R Q).val.val.comp (φ Q)
  have hc (Q T : FiniteIntermediateField L M₁) (hQT : Q ≤ T) :
      family Q = (family T).comp (IntermediateField.inclusion hQT) := by
    apply AlgHom.ext
    intro a
    refine RelFieldOfNorms.finiteHom_faithful K L M M₁
      Q (R Q) (R T) (φ Q) ((φ T).comp (IntermediateField.inclusion hQT)) ?_ a
    intro x
    have hQ := AlgHom.congr_fun (hφ Q) x
    have hT := AlgHom.congr_fun (hφ T)
      (RelFieldOfNorms.transition K L M₁ Q T hQT x)
    exact hQ.trans ((congrArg f
      (RelFieldOfNorms.of_transition K L M₁ Q T hQT x).symm).trans
        (hT.symm.trans (congrArg (RelFieldOfNorms.of K L M (R T))
          (RelFieldOfNorms.finiteHom_inclusion K L M M₁
            Q T hQT (R T) (φ T) x).symm)))
  let t := FiniteIntermediateField.liftAlgHom family hc
  refine ⟨t, fun Q => ⟨R Q, φ Q, ⟨?_, hφ Q⟩⟩⟩
  intro a
  exact (FiniteIntermediateField.liftAlgHom_apply family hc Q a).symm

/-- A finite-stage factorization computes the induced union
map by the same finite Hom, independently of the chosen containing stage. -/
theorem RelFieldOfNorms.algMap_of_factor (t : M₁ →ₐ[L] M)
    (Q : FiniteIntermediateField L M₁) (R : FiniteIntermediateField L M) (φ : Q.val →ₐ[L] R.val)
    (h : ∀ a : Q.val, (φ a : M) = t a) (x : FieldOfNorms K Q.val) :
    RelFieldOfNorms.algMap K L M₁ M t
        (RelFieldOfNorms.of K L M₁ Q x) =
      RelFieldOfNorms.of K L M R
        (FieldOfNorms.algHomEquiv K L Q.val R.val φ x) := by
  let J : FiniteIntermediateField L M := FiniteIntermediateField.map t Q
  let e : Q.val ≃ₐ[L] J.val := FiniteIntermediateField.equivMap t Q
  have hJR : J ≤ R := by
    intro z hz
    let a := e.symm ⟨z, hz⟩
    have ha : (e a : M) = z := congrArg (fun w : J.val => (w : M))
      (e.apply_symm_apply ⟨z, hz⟩)
    have hzφ : (φ a : M) = z := (h a).trans ha
    exact hzφ ▸ (φ a).property
  have hc : (IntermediateField.inclusion hJR).comp e.toAlgHom = φ := by
    apply AlgHom.ext
    intro a
    exact Subtype.ext (h a).symm
  have he : FieldOfNorms.algHomEquiv K L Q.val J.val e.toAlgHom x =
      FieldOfNorms.mapEquiv (e.restrictScalars K) x := by
    exact FieldOfNorms.map_algEquiv (e.restrictScalars K) x
  calc
    _ = RelFieldOfNorms.of K L M J
        (FieldOfNorms.mapEquiv (e.restrictScalars K) x) :=
      (RelFieldOfNorms.map_of K L M₁ M t Q x).trans
        (congrArg (RelFieldOfNorms.of K L M J)
          (RelFieldOfNorms.stageMap_apply K L M₁ M t Q x))
    _ = RelFieldOfNorms.of K L M J
        (FieldOfNorms.algHomEquiv K L Q.val J.val e.toAlgHom x) :=
      congrArg (RelFieldOfNorms.of K L M J) he.symm
    _ = RelFieldOfNorms.of K L M R
        (FieldOfNorms.algHomEquiv K L Q.val R.val
          ((IntermediateField.inclusion hJR).comp e.toAlgHom) x) :=
      (RelFieldOfNorms.of_finiteHom_inclusion K L M M₁
        Q J R hJR e.toAlgHom x).symm
    _ = _ := congrArg (fun j => RelFieldOfNorms.of K L M R
      (FieldOfNorms.algHomEquiv K L Q.val R.val j x)) hc

/-- Every algebra Hom of the unions is induced by an embedding. -/
theorem RelFieldOfNorms.algMap_surjective :
    Function.Surjective (RelFieldOfNorms.algMap K L M₁ M) := by
  intro f
  obtain ⟨t, ht⟩ := RelFieldOfNorms.exists_hom K L M M₁ f
  refine ⟨t, AlgHom.ext (fun z => ?_)⟩
  obtain ⟨Q, x, rfl⟩ := RelFieldOfNorms.exists_stage K L M₁ z
  obtain ⟨R, φ, hφ, hf⟩ := ht Q
  exact (RelFieldOfNorms.algMap_of_factor K L M M₁
    t Q R φ hφ x).trans (AlgHom.congr_fun hf x)

/-- The union functor distinguishes every algebra embedding. -/
theorem RelFieldOfNorms.algMap_injective :
    Function.Injective (RelFieldOfNorms.algMap K L M₁ M) := by
  intro t u h
  apply AlgHom.ext
  intro a
  obtain ⟨Q, ha⟩ := FiniteIntermediateField.exists_mem (L := L) a
  let R := FiniteIntermediateField.map t Q
  let S := FiniteIntermediateField.map u Q
  refine RelFieldOfNorms.finiteHom_faithful K L M M₁
    Q R S (FiniteIntermediateField.equivMap t Q).toAlgHom
      (FiniteIntermediateField.equivMap u Q).toAlgHom ?_ ⟨a, ha⟩
  intro x
  exact (RelFieldOfNorms.algMap_of_factor K L M M₁ t Q R
    (FiniteIntermediateField.equivMap t Q).toAlgHom (fun _ => rfl) x).symm.trans
      ((AlgHom.congr_fun h (RelFieldOfNorms.of K L M₁ Q x)).trans
        (RelFieldOfNorms.algMap_of_factor K L M M₁ u Q S
          (FiniteIntermediateField.equivMap u Q).toAlgHom (fun _ => rfl) x))

/-- Full faithfulness for arbitrary separable algebraic extensions. -/
theorem RelFieldOfNorms.algMap_bijective :
    Function.Bijective (RelFieldOfNorms.algMap K L M₁ M) := by
  exact ⟨RelFieldOfNorms.algMap_injective K L M M₁,
    RelFieldOfNorms.algMap_surjective K L M M₁⟩

end NormUnion

section FullFaithful

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L M N : Type*) [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The canonical full Hom equivalence is the union functor. -/
def RelFieldOfNorms.homEquiv :
    (M →ₐ[L] N) ≃ (RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L N) := by
  exact Equiv.ofBijective (RelFieldOfNorms.algMap K L M N)
    (RelFieldOfNorms.algMap_bijective K L N M)

end FullFaithful

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The union functor preserves the endomorphism monoid. -/
def RelFieldOfNorms.endHom :
    (M →ₐ[L] M) →* (RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  refine { toFun := RelFieldOfNorms.algMap K L M M
           map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro z
    change RelFieldOfNorms.mapEquiv K L M M (AlgHom.id L M) z = z
    rw [RelFieldOfNorms.map_id]
    rfl
  · intro s t
    apply AlgHom.ext
    intro z
    change RelFieldOfNorms.mapEquiv K L M M (s.comp t) z =
      RelFieldOfNorms.mapEquiv K L M M s
        (RelFieldOfNorms.mapEquiv K L M M t z)
    exact congrArg (fun f => f z)
      (RelFieldOfNorms.map_comp K L M M t M s).symm

/-- Full faithfulness identifies the endomorphism monoids. -/
def RelFieldOfNorms.endEquiv :
    (M →ₐ[L] M) ≃* (RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  exact MulEquiv.ofBijective (RelFieldOfNorms.endHom K L M)
    (RelFieldOfNorms.algMap_bijective K L M M)

/-- The canonical automorphism-group correspondence on the fields. -/
def RelFieldOfNorms.autEquiv :
    (M ≃ₐ[L] M) ≃* (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M) := by
  exact (AlgEquiv.algHomUnitsEquiv L M).symm.trans
    ((Units.mapEquiv (RelFieldOfNorms.endEquiv K L M)).trans
      (AlgEquiv.algHomUnitsEquiv (FieldOfNorms K L)
        (RelFieldOfNorms K L M)))

/-- The group correspondence has the induced algebra map as its forward map. -/
@[simp]
theorem RelFieldOfNorms.autEquiv_toAlgHom (σ : M ≃ₐ[L] M) :
    (RelFieldOfNorms.autEquiv K L M σ).toAlgHom =
      RelFieldOfNorms.algMap K L M M σ.toAlgHom := rfl

/-- Evaluation is the union embedding. -/
@[simp]
theorem RelFieldOfNorms.autEquiv_apply (σ : M ≃ₐ[L] M)
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.autEquiv K L M σ z =
      RelFieldOfNorms.mapEquiv K L M M σ.toAlgHom z := rfl

/-- On every finite stage the automorphism is image transport. -/
theorem RelFieldOfNorms.autEquiv_of (σ : M ≃ₐ[L] M)
    (Q : FiniteIntermediateField L M) (x : FieldOfNorms K Q.val) :
    RelFieldOfNorms.autEquiv K L M σ
        (RelFieldOfNorms.of K L M Q x) =
      RelFieldOfNorms.of K L M (FiniteIntermediateField.map σ.toAlgHom Q)
        (RelFieldOfNorms.stageMap K L M M σ.toAlgHom Q x) :=
  RelFieldOfNorms.map_of K L M M σ.toAlgHom Q x

/-- Every algebra automorphism preserves the compatible rational valuation. -/
theorem RelFieldOfNorms.autEquiv_valuation (σ : M ≃ₐ[L] M)
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L M
        (RelFieldOfNorms.autEquiv K L M σ z) =
      RelFieldOfNorms.valuation K L M z :=
  RelFieldOfNorms.map_valuation K L M M σ.toAlgHom z

/-- Every automorphism of the target union preserves its rational valuation. -/
theorem RelFieldOfNorms.algEquiv_valuation :
    ∀ (σ : RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
        RelFieldOfNorms K L M)
      (z : RelFieldOfNorms K L M),
      RelFieldOfNorms.valuation K L M (σ z) =
        RelFieldOfNorms.valuation K L M z := by
  intro σ z
  obtain ⟨τ, rfl⟩ := (RelFieldOfNorms.autEquiv K L M).surjective σ
  exact RelFieldOfNorms.autEquiv_valuation K L M τ z

end FontaineWintenberger
