/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Absolute

/-!
# Intrinsic infinite upper groups under field isomorphisms

The image of a finite Galois subextension is an actual finite Galois
subextension. Ordinary restrictions commute with the restricted field
isomorphism, so the finite own-ring transport identifies every upper condition.
-/

@[expose] public section

namespace FontaineWintenberger

section Fields

variable (K : Type*) [Field K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- The actual image of a finite Galois intermediate field. -/
noncomputable def finiteGaloisMap (f : L →ₐ[K] M) (D : FiniteGaloisIntermediateField K L) :
    FiniteGaloisIntermediateField K M := by
  let : FiniteDimensional K (D.toIntermediateField.map f) :=
    Module.Finite.equiv (D.toIntermediateField.equivMap f).toLinearEquiv
  let : IsGalois K (D.toIntermediateField.map f) :=
    IsGalois.of_algEquiv (D.toIntermediateField.equivMap f)
  exact ⟨D.toIntermediateField.map f⟩

/-- The canonical isomorphism onto this actual image. -/
noncomputable def finiteGaloisMapEquiv (f : L →ₐ[K] M)
    (D : FiniteGaloisIntermediateField K L) : D ≃ₐ[K] finiteGaloisMap K f D :=
  D.toIntermediateField.equivMap f

@[simp]
theorem coe_finiteGaloisMapEquiv (f : L →ₐ[K] M)
    (D : FiniteGaloisIntermediateField K L) (x : D) :
    ((finiteGaloisMapEquiv K f D x : finiteGaloisMap K f D) : M) = f (x : L) := rfl

/-- Conjugation commutes with ordinary restriction to the actual finite image. -/
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
