module

public import FontaineWintenberger.FieldOfNorms.Multiplicative

/-!
# Extension from original cofinal norm coordinates

Any genuinely cofinal set of original finite fields determines and constructs
the same zero-adjoined unit norm limit. This supplies the covariant finite
functor before its additive and topological properties.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Original evaluations on any genuinely cofinal set already distinguish
elements of the original zero-adjoined unit limit. -/
theorem NormLimit.ext_cofinal (P : FiniteLayer K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F) {α β : NormLimit K L}
    (h : ∀ E, P E → normLimitEval K L E α = normLimitEval K L E β) : α = β := by
  apply NormLimit.ext K L
  intro E
  obtain ⟨F, hF, hEF⟩ := hP E
  rw [← normLimitEval_norm K L E F hEF α,
    ← normLimitEval_norm K L E F hEF β, h F hF]

/-- Any actual compatible cofinal coordinate family extends uniquely to the
same original norm limit, using original finite field norms. -/
theorem existsUnique_normLimit_of_compatible_cofinal (P : FiniteLayer K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hF) = x E hE) :
    ∃! α : NormLimit K L, ∀ (E : FiniteLayer K L) (hE : P E),
      normLimitEval K L E α = x E hE := by
  let u (E : FiniteLayer K L) := (hP E).choose
  have hu (E : FiniteLayer K L) : P (u E) := (hP E).choose_spec.1
  have hEu (E : FiniteLayer K L) : E ≤ u E := (hP E).choose_spec.2
  let f (E : FiniteLayer K L) := FiniteLayer.norm E (u E) (hEu E) (x (u E) (hu E))
  have hf (E F : FiniteLayer K L) (hEF : E ≤ F) :
      FiniteLayer.norm E F hEF (f F) = f E := by
    obtain ⟨G, hG, hUG⟩ := hP (FiniteLayer.sup (u E) (u F))
    have hEG : u E ≤ G := (FiniteLayer.le_sup_left (u E) (u F)).trans hUG
    have hFG : u F ≤ G := (FiniteLayer.le_sup_right (u E) (u F)).trans hUG
    dsimp only [f]
    rw [← hx (u E) G (hu E) hG hEG, ← hx (u F) G (hu F) hG hFG]
    simp only [FiniteLayer.norm_norm]
  obtain ⟨α, hα, _⟩ := existsUnique_normLimit_of_compatible K L f hf
  have hαP (E : FiniteLayer K L) (hE : P E) : normLimitEval K L E α = x E hE :=
    (hα E).trans (hx E (u E) hE (hu E) (hEu E))
  refine ⟨α, hαP, ?_⟩
  intro β hβ
  apply NormLimit.ext_cofinal K L P hP
  intro E hE
  exact (hβ E hE).trans (hαP E hE).symm

/-- The canonical extension of actual compatible cofinal coordinates. -/
def normLimitOfCofinal (P : FiniteLayer K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hF) = x E hE) : NormLimit K L :=
  (existsUnique_normLimit_of_compatible_cofinal K L P hP x hx).choose

/-- Every original prescribed cofinal coordinate is retained exactly. -/
@[simp]
theorem normLimitEval_normLimitOfCofinal (P : FiniteLayer K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hF) = x E hE)
    (E : FiniteLayer K L) (hE : P E) :
    normLimitEval K L E (normLimitOfCofinal K L P hP x hx) = x E hE :=
  (existsUnique_normLimit_of_compatible_cofinal K L P hP x hx).choose_spec.1 E hE

/-- Any original finite field is computed from any prescribed cofinal upper
field by its actual original norm, independently of the choice. -/
theorem normLimitEval_normLimitOfCofinal_any (P : FiniteLayer K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hF) = x E hE)
    (E F : FiniteLayer K L) (hF : P F) (hEF : E ≤ F) :
    normLimitEval K L E (normLimitOfCofinal K L P hP x hx) =
      FiniteLayer.norm E F hEF (x F hF) := by
  rw [← normLimitEval_norm K L E F hEF, normLimitEval_normLimitOfCofinal]

end FontaineWintenberger
