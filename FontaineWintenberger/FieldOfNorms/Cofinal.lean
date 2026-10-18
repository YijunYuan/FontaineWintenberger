/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Multiplicative

/-!
# Extension from original cofinal norm coordinates

Any genuinely cofinal set of original finite fields determines and constructs
the same zero-adjoined unit field of norms. This supplies the covariant finite
functor before its additive and topological properties.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Original evaluations on any genuinely cofinal set already distinguish
elements of the original zero-adjoined unit limit. -/
theorem FieldOfNorms.ext_cofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F) {α β : FieldOfNorms K L}
    (h : ∀ E, P E → FieldOfNorms.coord K L E α = FieldOfNorms.coord K L E β) : α = β := by
  apply FieldOfNorms.ext K L
  intro E
  obtain ⟨F, hF, hEF⟩ := hP E
  rw [← FieldOfNorms.coord_norm K L E F hEF α,
    ← FieldOfNorms.coord_norm K L E F hEF β, h F hF]

/-- Any actual compatible cofinal coordinate family extends uniquely to the
same original field of norms, using original finite field norms. -/
theorem existsUnique_fieldOfNorms_of_compatible_cofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE) :
    ∃! α : FieldOfNorms K L, ∀ (E : FiniteIntermediateField K L) (hE : P E),
      FieldOfNorms.coord K L E α = x E hE := by
  let u (E : FiniteIntermediateField K L) := (hP E).choose
  have hu (E : FiniteIntermediateField K L) : P (u E) := (hP E).choose_spec.1
  have hEu (E : FiniteIntermediateField K L) : E ≤ u E := (hP E).choose_spec.2
  let f (E : FiniteIntermediateField K L) := FiniteIntermediateField.norm E (u E) (hEu E) (x (u E)
      (hu E))
  have hf (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
      FiniteIntermediateField.norm E F hEF (f F) = f E := by
    obtain ⟨G, hG, hUG⟩ := hP (FiniteIntermediateField.sup (u E) (u F))
    have hEG : u E ≤ G := (FiniteIntermediateField.le_sup_left (u E) (u F)).trans hUG
    have hFG : u F ≤ G := (FiniteIntermediateField.le_sup_right (u E) (u F)).trans hUG
    dsimp only [f]
    rw [← hx (u E) G (hu E) hG hEG, ← hx (u F) G (hu F) hG hFG]
    simp only [FiniteIntermediateField.norm_norm]
  obtain ⟨α, hα, _⟩ := existsUnique_fieldOfNorms_of_compatible K L f hf
  have hαP (E : FiniteIntermediateField K L) (hE : P E) : FieldOfNorms.coord K L E α = x E hE :=
    (hα E).trans (hx E (u E) hE (hu E) (hEu E))
  refine ⟨α, hαP, ?_⟩
  intro β hβ
  apply FieldOfNorms.ext_cofinal K L P hP
  intro E hE
  exact (hβ E hE).trans (hαP E hE).symm

/-- The canonical extension of actual compatible cofinal coordinates. -/
def FieldOfNorms.ofCofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE) : FieldOfNorms K L :=
  (existsUnique_fieldOfNorms_of_compatible_cofinal K L P hP x hx).choose

/-- Every original prescribed cofinal coordinate is retained exactly. -/
@[simp]
theorem FieldOfNorms.coord_fieldOfNormsOfCofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE)
    (E : FiniteIntermediateField K L) (hE : P E) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofCofinal K L P hP x hx) = x E hE :=
  (existsUnique_fieldOfNorms_of_compatible_cofinal K L P hP x hx).choose_spec.1 E hE

/-- Any original finite field is computed from any prescribed cofinal upper
field by its actual original norm, independently of the choice. -/
theorem FieldOfNorms.coord_fieldOfNormsOfCofinal_any (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE)
    (E F : FiniteIntermediateField K L) (hF : P F) (hEF : E ≤ F) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofCofinal K L P hP x hx) =
      FiniteIntermediateField.norm E F hEF (x F hF) := by
  rw [← FieldOfNorms.coord_norm K L E F hEF, FieldOfNorms.coord_fieldOfNormsOfCofinal]

end FontaineWintenberger
