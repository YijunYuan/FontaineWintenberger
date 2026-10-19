/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite subfields stable under every automorphism

Mathlib's compositum of all embedding images is finite for a finite
field, without normality of the ambient field. We prove its invariance
under ambient automorphisms and retain their restrictions.

## Main definitions

* `normalClosureRestrict`: Restriction of the ambient automorphism to the image compositum.

## Main results

* `map_normalClosure_le`: All embedding images remain in their compositum after any ambient
  embedding.
* `map_normalClosure_eq`: The finite-image compositum is stable under every automorphism, with no
  normality hypothesis on the ambient field.
* `exists_finite_aut_stable`: A finite field is contained in a finite field stable under all
  automorphisms; finiteness comes from the canonical existing construction.

## References

* Mathlib; this file is an upstream candidate and has no project-specific reference.
-/

@[expose] public section

noncomputable section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- All embedding images remain in their compositum after any ambient embedding. -/
theorem map_normalClosure_le (D : IntermediateField K L) (σ : L →ₐ[K] L) :
    (normalClosure K D L).map σ ≤ normalClosure K D L := by
  rw [normalClosure_def, map_iSup]
  apply iSup_le
  intro f
  rw [AlgHom.map_fieldRange]
  exact (σ.comp f).fieldRange_le_normalClosure

/-- The finite-image compositum is stable under every automorphism,
with no normality hypothesis on the ambient field. -/
theorem map_normalClosure_eq (D : IntermediateField K L) (σ : L ≃ₐ[K] L) :
    (normalClosure K D L).map σ.toAlgHom = normalClosure K D L := by
  apply le_antisymm (map_normalClosure_le D σ.toAlgHom)
  have h := map_mono σ.toAlgHom (map_normalClosure_le D σ.symm.toAlgHom)
  simpa only [map_map, AlgEquiv.comp_symm, map_id] using h

/-- Restriction of the ambient automorphism to the image compositum. -/
def normalClosureRestrict (D : IntermediateField K L) (σ : L ≃ₐ[K] L) :
    normalClosure K D L ≃ₐ[K] normalClosure K D L :=
  (equivMap (normalClosure K D L) σ.toAlgHom).trans
    (equivOfEq (map_normalClosure_eq D σ))

@[simp]
theorem coe_normalClosureRestrict (D : IntermediateField K L) (σ : L ≃ₐ[K] L)
    (x : normalClosure K D L) :
    (normalClosureRestrict D σ x : L) = σ (x : L) := rfl

/-- A finite field is contained in a finite field stable under
all automorphisms; finiteness comes from the canonical existing construction. -/
theorem exists_finite_aut_stable (D : IntermediateField K L) [FiniteDimensional K D] :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ D ≤ E ∧
      ∀ σ : L ≃ₐ[K] L, E.map σ.toAlgHom = E :=
  ⟨normalClosure K D L, inferInstance, le_normalClosure D, map_normalClosure_eq D⟩

end IntermediateField
