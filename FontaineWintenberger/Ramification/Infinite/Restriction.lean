/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Infinite.Basic

/-!
# Infinite upper ramification under restriction

## Upper ramification under infinite Galois restriction

Finite subfields of an intermediate field are transported by their
inclusions. Compactness of the infinite upper group then supplies a
lift satisfying every finite restriction condition.

## Intrinsic infinite upper groups under field isomorphisms

The image of a finite Galois subextension is a finite Galois
subextension. Ordinary restrictions commute with the restricted field
isomorphism, so the finite own-ring transport identifies every upper condition.
-/

@[expose] public section

namespace FontaineWintenberger

section Lift

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The image in the ambient field of a finite Galois subfield of an intermediate field. -/
noncomputable def finiteGaloisLift (L : IntermediateField K Ω)
    (E : FiniteGaloisIntermediateField K L) : FiniteGaloisIntermediateField K Ω :=
  let e := IntermediateField.liftAlgEquiv E.toIntermediateField
  letI := Module.Finite.equiv e.toLinearEquiv
  letI := IsGalois.of_algEquiv e
  .mk (IntermediateField.lift E.toIntermediateField)

/-- The canonical inclusion isomorphism onto the lifted subfield. -/
noncomputable def finiteGaloisLiftEquiv (L : IntermediateField K Ω)
    (E : FiniteGaloisIntermediateField K L) : E ≃ₐ[K] finiteGaloisLift L E :=
  IntermediateField.liftAlgEquiv E.toIntermediateField

/-- Ordinary restriction commutes with the canonical inclusion isomorphism. -/
theorem restrictNormal_finiteGaloisLift (L : IntermediateField K Ω) [Normal K L]
    (E : FiniteGaloisIntermediateField K L) (s : Ω ≃ₐ[K] Ω) :
    s.restrictNormal (finiteGaloisLift L E) =
      (finiteGaloisLiftEquiv L E).autCongr ((s.restrictNormal L).restrictNormal E) := by
  let e := finiteGaloisLiftEquiv L E
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change ((s.restrictNormal (finiteGaloisLift L E)) x : Ω) =
    ((e (((s.restrictNormal L).restrictNormal E) (e.symm x))) : Ω)
  calc
    _ = s (x : Ω) := AlgEquiv.restrictNormal_commutes s (finiteGaloisLift L E) x
    _ = s ((e (e.symm x)) : Ω) := by rw [e.apply_symm_apply]
    _ = s (((e.symm x : E) : L) : Ω) := rfl
    _ = ((s.restrictNormal L) ((e.symm x : E) : L) : Ω) :=
      (AlgEquiv.restrictNormal_commutes s L ((e.symm x : E) : L)).symm
    _ = (((((s.restrictNormal L).restrictNormal E) (e.symm x) : E) : L) : Ω) :=
      congrArg (algebraMap L Ω)
        (AlgEquiv.restrictNormal_commutes (s.restrictNormal L) E (e.symm x)).symm
    _ = _ := rfl

end Lift

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω]
variable (L : IntermediateField K Ω) [IsGalois K L]

theorem restrictNormal_mem_upperRamificationGroupInfinite (u : ℝ) (hu : -1 ≤ u)
    (s : Ω ≃ₐ[K] Ω) (hs : s ∈ upperRamificationGroupInfinite K Ω u) :
    s.restrictNormal L ∈ upperRamificationGroupInfinite K L u := by
  rw [mem_upperRamificationGroupInfinite] at hs ⊢
  intro E
  have h := hs (finiteGaloisLift L E)
  rw [restrictNormal_finiteGaloisLift] at h
  rw [← upperRamificationGroup_map_autCongr K (finiteGaloisLiftEquiv L E) hu,
    Subgroup.mem_map_equiv] at h
  simpa only [MulEquiv.symm_apply_apply] using h

variable [IsGalois K Ω]
variable [PerfectField 𝓀[K]]

/-- A finite list of prescribed subextension restrictions is realized inside the upper
group. -/
theorem exists_lift_finite_infinite_upper_restrictions
    (S : Finset (FiniteGaloisIntermediateField K L)) (u : ℝ) (hu : -1 ≤ u)
    (q : L ≃ₐ[K] L) (hq : q ∈ upperRamificationGroupInfinite K L u) :
    ∃ s ∈ upperRamificationGroupInfinite K Ω u,
      ∀ E ∈ S, (s.restrictNormal L).restrictNormal E = q.restrictNormal E := by
  classical
  let E₀ := S.sup id
  let e := finiteGaloisLiftEquiv L E₀
  have hq₀ := (mem_upperRamificationGroupInfinite K L u q).mp hq E₀
  have hm : e.autCongr (q.restrictNormal E₀) ∈
      upperRamificationGroup (R := spectralIntegerRing K (finiteGaloisLift L E₀))
        ((finiteGaloisLift L E₀) ≃ₐ[K] (finiteGaloisLift L E₀)) u := by
    rw [← upperRamificationGroup_map_autCongr K e hu]
    exact Subgroup.mem_map.mpr ⟨q.restrictNormal E₀, hq₀, rfl⟩
  obtain ⟨s, hs, hres⟩ := exists_lift_upperRamificationGroupInfinite K Ω
    (finiteGaloisLift L E₀) u hu (e.autCongr (q.restrictNormal E₀)) hm
  have h₀ : (s.restrictNormal L).restrictNormal E₀ = q.restrictNormal E₀ :=
    e.autCongr.injective ((restrictNormal_finiteGaloisLift L E₀ s).symm.trans hres)
  refine ⟨s, hs, ?_⟩
  intro E hE
  let f : Opposite.op E₀ ⟶ Opposite.op E :=
    (CategoryTheory.homOfLE (show E ≤ E₀ from Finset.le_sup (f := id) hE)).op
  have hS := (InfiniteGalois.algEquivToLimit K L (s.restrictNormal L)).property f
  have hQ := (InfiniteGalois.algEquivToLimit K L q).property f
  change (finGaloisGroupMap f).hom.hom ((s.restrictNormal L).restrictNormal E₀) =
    (s.restrictNormal L).restrictNormal E at hS
  change (finGaloisGroupMap f).hom.hom (q.restrictNormal E₀) = q.restrictNormal E at hQ
  exact hS.symm.trans ((congrArg (finGaloisGroupMap f).hom.hom h₀).trans hQ)

/-- Every upper automorphism of an arbitrary Galois subextension has an upper lift. -/
theorem exists_lift_infinite_upper_restriction (u : ℝ) (hu : -1 ≤ u)
    (q : L ≃ₐ[K] L) (hq : q ∈ upperRamificationGroupInfinite K L u) :
    ∃ s ∈ upperRamificationGroupInfinite K Ω u, s.restrictNormal L = q := by
  let T (E : FiniteGaloisIntermediateField K L) : Set (Ω ≃ₐ[K] Ω) :=
    {s | (s.restrictNormal L).restrictNormal E = q.restrictNormal E}
  have hT (E : FiniteGaloisIntermediateField K L) : IsClosed (T E) :=
    isClosed_singleton.preimage
      ((InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField).comp
        (InfiniteGalois.restrictNormalHom_continuous L))
  have hfinite (S : Finset (FiniteGaloisIntermediateField K L)) :
      ((upperRamificationGroupInfinite K Ω u : Set (Ω ≃ₐ[K] Ω)) ∩
        ⋂ E ∈ S, T E).Nonempty := by
    obtain ⟨s, hs, hS⟩ := exists_lift_finite_infinite_upper_restrictions K Ω L S u hu q hq
    refine ⟨s, hs, ?_⟩
    simp only [Set.mem_iInter]
    exact hS
  obtain ⟨s, hs, hST⟩ :=
    (isCompact_upperRamificationGroupInfinite K Ω u).inter_iInter_nonempty T hT hfinite
  refine ⟨s, hs, ?_⟩
  apply (InfiniteGalois.mulEquivToLimit K L).injective
  apply Subtype.ext
  funext E
  exact Set.mem_iInter.mp hST E.unop

/-- Ordinary infinite Galois restriction maps upper groups onto upper groups. -/
theorem restrictNormalHom_map_upperRamificationGroupInfinite (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K Ω u).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroupInfinite K L u := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact restrictNormal_mem_upperRamificationGroupInfinite K Ω L u hu s hs
  · intro q hq
    obtain ⟨s, hs, hres⟩ := exists_lift_infinite_upper_restriction K Ω L u hu q hq
    exact Subgroup.mem_map.mpr ⟨s, hs, hres⟩

end FontaineWintenberger

namespace FontaineWintenberger

section Fields

variable (K : Type*) [Field K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- The image of a finite Galois intermediate field. -/
noncomputable def finiteGaloisMap (f : L →ₐ[K] M) (D : FiniteGaloisIntermediateField K L) :
    FiniteGaloisIntermediateField K M := by
  let : FiniteDimensional K (D.toIntermediateField.map f) :=
    Module.Finite.equiv (D.toIntermediateField.equivMap f).toLinearEquiv
  let : IsGalois K (D.toIntermediateField.map f) :=
    IsGalois.of_algEquiv (D.toIntermediateField.equivMap f)
  exact ⟨D.toIntermediateField.map f⟩

/-- The canonical isomorphism onto this image. -/
noncomputable def finiteGaloisMapEquiv (f : L →ₐ[K] M)
    (D : FiniteGaloisIntermediateField K L) : D ≃ₐ[K] finiteGaloisMap K f D :=
  D.toIntermediateField.equivMap f

@[simp]
theorem coe_finiteGaloisMapEquiv (f : L →ₐ[K] M)
    (D : FiniteGaloisIntermediateField K L) (x : D) :
    ((finiteGaloisMapEquiv K f D x : finiteGaloisMap K f D) : M) = f (x : L) := rfl

/-- Conjugation commutes with ordinary restriction to the finite image. -/
theorem restrictNormal_finiteGaloisMap (f : L ≃ₐ[K] M)
    (D : FiniteGaloisIntermediateField K L) (s : L ≃ₐ[K] L) :
    (f.autCongr s).restrictNormal (finiteGaloisMap K f.toAlgHom D) =
      (finiteGaloisMapEquiv K f.toAlgHom D).autCongr (s.restrictNormal D) := by
  let e := finiteGaloisMapEquiv K f.toAlgHom D
  ext x
  obtain ⟨a, rfl⟩ := e.surjective x
  calc
    ((f.autCongr s).restrictNormal (finiteGaloisMap K f.toAlgHom D) (e a) : M) =
        (f.autCongr s) (e a : M) :=
      AlgEquiv.restrictNormal_commutes (f.autCongr s) (finiteGaloisMap K f.toAlgHom D) (e a)
    _ = f (s (a : L)) := by
      rw [show (e a : M) = f (a : L) from rfl]
      simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    _ = f ((s.restrictNormal D a : D) : L) :=
      congrArg f (AlgEquiv.restrictNormal_commutes s D a).symm
    _ = (e (s.restrictNormal D a) : M) := rfl
    _ = (e.autCongr (s.restrictNormal D) (e a) : M) := by
      simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]

theorem mem_upperRamificationGroupInfinite_of_autCongr (f : L ≃ₐ[K] M) {u : ℝ}
    (hu : -1 ≤ u) (s : L ≃ₐ[K] L)
    (h : f.autCongr s ∈ upperRamificationGroupInfinite K M u) :
    s ∈ upperRamificationGroupInfinite K L u := by
  rw [mem_upperRamificationGroupInfinite] at h ⊢
  intro D
  have hD := h (finiteGaloisMap K f.toAlgHom D)
  rw [restrictNormal_finiteGaloisMap] at hD
  rw [← upperRamificationGroup_map_autCongr K (finiteGaloisMapEquiv K f.toAlgHom D) hu] at hD
  obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hD
  exact (finiteGaloisMapEquiv K f.toAlgHom D).autCongr.injective heq ▸ ha

theorem mem_upperRamificationGroupInfinite_autCongr_iff (f : L ≃ₐ[K] M) {u : ℝ}
    (hu : -1 ≤ u) (s : L ≃ₐ[K] L) :
    f.autCongr s ∈ upperRamificationGroupInfinite K M u ↔
      s ∈ upperRamificationGroupInfinite K L u := by
  constructor
  · exact mem_upperRamificationGroupInfinite_of_autCongr K f hu s
  · intro h
    apply mem_upperRamificationGroupInfinite_of_autCongr K f.symm hu (f.autCongr s)
    simpa only [← AlgEquiv.autCongr_symm, MulEquiv.symm_apply_apply] using h

theorem upperRamificationGroupInfinite_map_autCongr (f : L ≃ₐ[K] M) {u : ℝ}
    (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K L u).map f.autCongr.toMonoidHom =
      upperRamificationGroupInfinite K M u := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (mem_upperRamificationGroupInfinite_autCongr_iff K f hu s).mpr hs
  · intro ht
    refine ⟨f.autCongr.symm t, ?_, f.autCongr.apply_symm_apply t⟩
    exact (mem_upperRamificationGroupInfinite_autCongr_iff K f hu _).mp
      ((f.autCongr.apply_symm_apply t).symm ▸ ht)

end FontaineWintenberger
