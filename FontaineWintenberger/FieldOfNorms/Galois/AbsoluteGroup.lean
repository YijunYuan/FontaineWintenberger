/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Relative.SeparablyClosed
public import FontaineWintenberger.FieldOfNorms.Relative.Krull

/-!
# The absolute Galois equivalence of the norm field

The same canonical relative field of norms is a separable closure. Its
Krull equivalence, followed by separable-closure comparisons,
therefore identifies the absolute Galois groups with their Krull topologies.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section KrullConjugacy

variable {F A B : Type*} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]

/-- Conjugation by a field isomorphism pulls back a finite-field
fixer to the fixer of its inverse image. -/
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
Krull topologies, without a normality assumption. -/
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

/-- The existing automorphism conjugacy as a Krull homeomorphism. -/
def krullAutCongr (e : A ≃ₐ[F] B) : (A ≃ₐ[F] A) ≃ₜ* (B ≃ₐ[F] B) :=
  { e.autCongr with
    continuous_toFun := continuous_autCongr_krull e
    continuous_invFun := continuous_autCongr_krull e.symm }

/-- The topological comparison retains Mathlib's algebraic conjugacy. -/
@[simp]
theorem krullAutCongr_toMulEquiv (e : A ≃ₐ[F] B) :
    (krullAutCongr e).toMulEquiv = e.autCongr := rfl

/-- The same conjugation formula holds on every field element. -/
@[simp]
theorem krullAutCongr_apply (e : A ≃ₐ[F] B) (σ : A ≃ₐ[F] A) (x : B) :
    krullAutCongr e σ x = e (σ (e.symm x)) := rfl

end KrullConjugacy

section Closures

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsSepClosure K Ω]

include K in
/-- A separable closure containing the extension is a
separable closure of that extension too. -/
theorem closure_isSepClosure : IsSepClosure L Ω := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact isSepClosure_iff.mpr ⟨IsSepClosure.sep_closed K, inferInstance⟩

include K in
/-- The closure comparison, chosen over the base. -/
def separableClosureEquiv : SeparableClosure L ≃ₐ[L] Ω := by
  let := closure_isSepClosure K L Ω
  exact IsSepClosure.equiv L (SeparableClosure L) Ω

end Closures

section NormField

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω] [Algebra K L] [Algebra.IsSeparable K L]
    [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω

/-- The relative field of norms is compared to the canonical
separable closure using its proved separable-closure structure. -/
def RelFieldOfNorms.separableClosureEquiv :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    U ≃ₐ[X] SeparableClosure X := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let := RelFieldOfNorms.isSepClosure K L Ω
  exact IsSepClosure.equiv X U (SeparableClosure X)

/-- The corollary for the closure and the canonical
separable closure of the norm field. -/
def RelFieldOfNorms.absoluteGaloisEquiv :
    (Ω ≃ₐ[L] Ω) ≃ₜ* (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact (RelFieldOfNorms.krullEquiv K L Ω).trans
    (krullAutCongr (RelFieldOfNorms.separableClosureEquiv K L Ω))

/-- The comparison agrees on the same union with the
norm-field automorphism, rather than an independently constructed action. -/
theorem RelFieldOfNorms.absoluteGaloisEquiv_apply (σ : Ω ≃ₐ[L] Ω)
    (z : letI : Algebra.IsSeparable L Ω :=
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω; U) :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    RelFieldOfNorms.absoluteGaloisEquiv K L Ω σ
      (RelFieldOfNorms.separableClosureEquiv K L Ω z) =
      RelFieldOfNorms.separableClosureEquiv K L Ω
        (RelFieldOfNorms.map K L Ω Ω σ.toAlgHom z) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  change (RelFieldOfNorms.separableClosureEquiv K L Ω)
    ((RelFieldOfNorms.krullEquiv K L Ω σ)
      ((RelFieldOfNorms.separableClosureEquiv K L Ω).symm
        (RelFieldOfNorms.separableClosureEquiv K L Ω z))) = _
  rw [AlgEquiv.symm_apply_apply, RelFieldOfNorms.krullEquiv_apply]

/-- The absolute Galois equivalence on the project's canonical
separable-closure automorphism groups, with their existing Krull topologies. -/
def FieldOfNorms.absoluteGaloisEquiv :
    (SeparableClosure L ≃ₐ[L] SeparableClosure L) ≃ₜ*
      (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  exact (krullAutCongr (separableClosureEquiv K L Ω)).trans
    (RelFieldOfNorms.absoluteGaloisEquiv K L Ω)

/-- The canonical absolute-group equivalence retains precisely the
union map after conjugating the closure. -/
theorem FieldOfNorms.absoluteGaloisEquiv_apply
    (σ : SeparableClosure L ≃ₐ[L] SeparableClosure L)
    (z : letI : Algebra.IsSeparable L Ω :=
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω; U) :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    FieldOfNorms.absoluteGaloisEquiv K L Ω σ
      (RelFieldOfNorms.separableClosureEquiv K L Ω z) =
      RelFieldOfNorms.separableClosureEquiv K L Ω
        (RelFieldOfNorms.map K L Ω Ω
          ((separableClosureEquiv K L Ω).autCongr σ).toAlgHom z) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact RelFieldOfNorms.absoluteGaloisEquiv_apply K L Ω
    ((separableClosureEquiv K L Ω).autCongr σ) z

/-- The absolute Galois equivalence with no supplied closure or embedding
data: the canonical separable closure of the field is itself a
separable closure of the base via the composite algebra. -/
def fieldOfNormsAbsoluteGaloisEquiv :
    (SeparableClosure L ≃ₐ[L] SeparableClosure L) ≃ₜ*
      (SeparableClosure X ≃ₐ[X] SeparableClosure X) := by
  let : Algebra K (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L (SeparableClosure L) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable K (SeparableClosure L) :=
    Algebra.IsSeparable.trans K L (SeparableClosure L)
  let : IsSepClosure K (SeparableClosure L) :=
    isSepClosure_iff.mpr ⟨IsSepClosure.sep_closed L, inferInstance⟩
  exact RelFieldOfNorms.absoluteGaloisEquiv K L (SeparableClosure L)

end NormField

end FontaineWintenberger
